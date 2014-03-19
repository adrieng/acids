(* Copyright (C) Adrien Guatto <adrien.guatto@laposte.net> 2013-2014
 *
 * This file is part of Acid Synchrone.
 *
 * nsched is free software: you can redistribute it and/or modify it under the
 * terms of the GNU General Public License as published by the Free Software
 * Foundation, either version 3 of the License, or (at your option) any later
 * version.
 *
 * nsched is distributed in the hope that it will be useful, but WITHOUT ANY
 * WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR
 * A PARTICULAR PURPOSE.  See the GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License along with
 * nsched. If not, see <http://www.gnu.org/licenses/>.
 *)

module Make(A : Nir.A) =
struct
  open A

  let rec clock_input acc st =
    let open Clock_types in
    match st with
    | St_var _ -> acc
    | St_on (st, Ce_condvar { cecv_name = id; }) -> clock_input (id :: acc) st
    | St_on (st, (Ce_pword _ | Ce_equal _)) -> clock_input acc st

  let eq_output acc eq =
    match eq.eq_desc with
    | Var (x, _) | Const (x, _) | Pword (x, _) ->
      x :: acc
    | Call (x_l, { c_op = BufferAccess (b, Nir.Push, Nir.Strict); }, _)
    | Call (x_l, { c_op = BufferAccess (b, Nir.Pop, Nir.Lazy); }, _)
      ->
      b :: x_l @ acc
    | Call (x_l, _, _) ->
      x_l @ acc
    | Merge (x, _, _) ->
      x :: acc
    | Split (x_l, _, _, _) ->
      x_l @ acc
    | Buffer (x, _, _) ->
      x :: acc
    | Delay (x, _) ->
      x :: acc
    | Block block ->
      Ident.Env.fold
        (fun x cv acc -> if cv.cv_direction = Nir.Push then x :: acc else acc)
        block.b_conv
        acc

  let eq_input acc eq =
    let acc = clock_input acc eq.eq_base_clock in
    match eq.eq_desc with
    | Var (_, y) ->
      y :: acc
    | Const _ | Pword _ ->
      acc
    | Call (_, { c_op = BufferAccess (b, Nir.Push, Nir.Lazy); }, y_l)
    | Call (_, { c_op = BufferAccess (b, Nir.Pop, Nir.Strict); }, y_l)
      ->
      b :: y_l @ acc
    | Call (_, _, y_l) ->
      y_l @ acc
    | Merge (_, y, z_l) ->
      y :: (List.map snd z_l @ acc)
    | Split (_, y, z, _) ->
      y :: z :: acc
    | Buffer (_, _, y) ->
      y :: acc
    | Delay (_, y) ->
      y :: acc
    | Block block ->
      Ident.Env.fold
        (fun x cv acc -> if cv.cv_direction = Nir.Pop then x :: acc else acc)
        block.b_conv
        acc

  let rec eq_vars acc eq =
    match eq.eq_desc with
    | Var _ | Const _ | Pword _ | Call _ | Merge _ | Split _ | Buffer _
    | Delay _ ->
      eq_input (eq_output acc eq) eq
    | Block block ->
      block_vars acc block

  and block_vars acc block =
    List.fold_left eq_vars acc block.b_body

  let rec is_on_id id st =
    let open Clock_types in
    match st with
    | St_var id' -> id = id'
    | St_on (st, _) -> is_on_id id st

  (* Conversion functions for clock types.

     The next two functions handle a subtle point of clock and data
     signatures in Acid Synchrone / NIR.

     Consider the following node:

     let node f (x, y) = (x, y) when (true)

     It has the signature (s):
     f : forall 'x, 'x1. ('x * 'x1) -> ('x * 'x1)
     f :: forall 'a. ('a * 'a) -> 'a

     We would like to know the clock types of the two outputs of f. However,
     since the output of f is a stream of tuples rather than a tuple of stream,
     it only has the clock (stream) type 'a for the two components, rather than
     'a * 'a.

     Calling the function [signature_skeleton data_sig clock_sig] with
     [data_sig] and [clock_sig] the signatures defined above, we get a pair of
     input and output stream type lists ['a; 'a] and ['a; 'a].

     This is useful in the clock_slicing and block_formation passes.
  *)

  let rec replicate_stream_type st acc ty =
    let open Data_types in
    match ty with
    | Ty_var _ | Ty_scal _ | Ty_cond _ | Ty_boxed _ ->
      st :: acc
    | Ty_prod ty_l ->
      List.fold_left (replicate_stream_type st) acc ty_l

  let rec clock_type_skeleton acc ct ty =
    let open Data_types in
    let open Clock_types in
    match ct, ty with
    | Ct_prod _, (Ty_var _ | Ty_scal _ | Ty_cond _ | Ty_boxed _) ->
      invalid_arg "skeleton_clock_type" (* ill-typed? *)
    | Ct_prod ct_l, Ty_prod ty_l ->
      List.fold_left2 clock_type_skeleton acc ct_l ty_l
    | Ct_stream st, (Ty_var _ | Ty_scal _ | Ty_cond _ | Ty_boxed _) ->
      st :: acc
    | Ct_stream st, Ty_prod _ ->
      replicate_stream_type st acc ty

  let clock_type_skeleton ct ty = List.rev (clock_type_skeleton [] ct ty)

  let signature_skeleton ct_sig ty_sig =
    let open Data_types in
    let open Clock_types in
    clock_type_skeleton ct_sig.ct_sig_input ty_sig.data_sig_input,
    clock_type_skeleton ct_sig.ct_sig_output ty_sig.data_sig_output

  (* Environment handling *)

  type signature_env =
    {
      intf_env : Interface.env;
      locals : (Clock_types.clock_sig * Data_types.data_sig) Names.ShortEnv.t;
    }

  let signature_env_of_file file =
    let locals =
      let add locals nd =
        Names.ShortEnv.add
          (I.original_name nd.n_name).Names.shortn
          (nd.n_orig_info#ni_clock, nd.n_orig_info#ni_data)
          locals
      in
      List.fold_left add Names.ShortEnv.empty file.f_body
    in
    {
      intf_env = file.f_info;
      locals = locals;
    }

  let find_node_sig env ln =
    let open Names in
    match ln.modn with
    | LocalModule ->
      ShortEnv.find ln.shortn env.locals
    | Module modn ->
      let open Interface in
      let intf = ShortEnv.find modn env.intf_env in
      let ni = find_node intf ln.shortn in
      clock_signature_of_node_item ni, data_signature_of_node_item ni

  let find_node_clock_sig_sliced env ln ck_id =
    let ct_sig, data_sig = find_node_sig env ln in
    let input_sts, output_sts = signature_skeleton ct_sig data_sig in
    List.filter (is_on_id ck_id) input_sts,
    List.filter (is_on_id ck_id) output_sts

  (** Compute block count *)

  let rec block_count_eq count eq =
    match eq.eq_desc with
    | Var _ | Const _ | Pword _ | Call _ | Merge _ | Split _ | Buffer _
    | Delay _
      ->
      count
    | Block block ->
      block_count_block count block

  and block_count_block count block =
    List.fold_left block_count_eq (succ count) block.b_body

  let block_count_node node =
    block_count_block 0 node.n_body

  (** Substitution *)
  let subst_var subst v = try Ident.Env.find v subst with Not_found -> v

  let rec subst_eq subst eq =
    let var = subst_var subst in
    let vars = List.map var in
    let eqd =
      match eq.eq_desc with
      | Var (x, y) ->
        Var (var x, var y)
      | Const (x, c) ->
        Const (var x, c)
      | Pword (x, pw) ->
        Pword (var x, pw)
      | Call (x_l, c, y_l) ->
        Call (vars x_l, c, vars y_l)
      | Merge (x, y, c_l) ->
        Merge (var x, var y, List.map (fun (ec, z) -> ec, var z) c_l)
      | Split (x_l, y, z, ec_l) ->
        Split (vars x_l, var y, var z, ec_l)
      | Buffer (x, bu, y) ->
        Buffer (var x, bu, var y)
      | Delay (x, y) ->
        Delay (var x, var y)
      | Block block ->
        Block (subst_block subst block)
    in
    make_eq
      ~loc:eq.eq_loc
      eqd
      eq.eq_base_clock

  and subst_block subst block =
    let conv =
      let update name conv_var conv =
        let name = subst_var subst name in
        Ident.Env.add name conv_var conv
      in
      Ident.Env.fold update block.b_conv Ident.Env.empty
    in
    make_block
      ~loc:block.b_loc
      ~conv
      block.b_id
      (List.map (subst_eq subst) block.b_body)
end
