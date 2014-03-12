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

open Nir
open Nir_sliced

(** {1 Block formation}

    This pass introduces blocks around some equations. The goal is to establish
    the following invariant: *polymorphic clock variables present in clock
    signatures are only instantiated with block base clocks*.

    For example, consider the node f with clock signature:

    f :: forall 'a. 'a on (1 0) -> 'a

    called with 'a instantiated to 'a on (3):

    y :: 'a on (3) = f (x :: 'a on (2 1)

    The block formation pass introduces a block such that the invariant is
    respected:

    block 1 :: 'a on (3)
      y :: 'blk1 = f (x :: 'blk1 on (1 0))
    end
*)

(** {2 Utility functions} *)

let mk_sampled_clock ce ec ck =
  Clock_types.(St_on (ck, Ce_equal (ce, ec)))

(** {2 Environments} *)

type env =
  {
    senv : signature_env;
    mutable current_block_count : int;
    mutable var_decs : var_dec Ident.Env.t;
  }

let initial_env file =
  {
    senv = signature_env_of_file file;
    current_block_count = 0;
    var_decs = Ident.Env.empty;
  }

let find_node_sig env ln = find_node_sig env.senv ln

let enter_node env nd =
  env.var_decs <- nd.n_env;
  env.current_block_count <- block_count_node nd

let get_current_block_count env = env.current_block_count

let fresh_block_id env =
  let next = env.current_block_count in
  env.current_block_count <- env.current_block_count + 1;
  Block_id next

let get_var_decs env = env.var_decs

let add_var_dec env vd =
  env.var_decs <- Ident.Env.add vd.v_name vd env.var_decs

let find_var_dec env id = Ident.Env.find id env.var_decs

let find_var_specs env id =
  let vd = find_var_dec env id in
  let add_annot acc ann =
    match ann with
    | Ann_spec spec ->
      spec :: acc
    | Ann_type _ | Ann_clock _ ->
      acc
  in
  List.fold_left add_annot [] vd.v_annots

let find_var_bounds env id =
  let vd = find_var_dec env id in
  let rec search l =
    match l with
    | [] ->
      invalid_arg
        ("find_var_bounds: var " ^ Ident.to_string id ^ " has no bounds")
    | Ann_spec (Ast_misc.Interval it) :: _ ->
      it
    | _ :: l -> search
      l
  in
  search vd.v_annots

let clock_exp_of_id env id =
  let open Clock_types in
  Ce_condvar
    {
      cecv_name = id;
      cecv_bounds = find_var_bounds env id;
      cecv_specs = find_var_specs env id;
    }

(** {2 AST traversal} *)

let form_block
    env
    (* environment *)
    base_clock
    (* base_clock of the block to form *)
    mk_desc
    (* function creating the body of the expression *)
    x_l
    (* list of inputs *)
    x_ck_l
    (* list of clocks to be rerooted *)
    y_l
    (* list of outputs *)
    y_ck_l
    (* y_ck_l is to y_l what x_ck_l is to x_l *)
    =
  assert (List.length x_l = List.length x_ck_l);
  assert (List.length y_l = List.length y_ck_l);

  let bid = fresh_block_id env in
  let bck = Clock_types.St_var Info.Cv_base in

  let refresh_variable dir (conv, eqs) x mk_ck =
    let x_vd = find_var_dec env x in
    let x' = Ident.make_prefix "blk_" x in
    (* let x'_ck = Clock_types.reroot_stream_type Info.Cv_base bck in *)
    let x'_ck = mk_ck bck in
    let x'_vd =
      make_var_dec
        ~loc:x_vd.v_loc
        ~annots:x_vd.v_annots
        x'
        x_vd.v_data
        x'_ck
        x_vd.v_scope
    in
    let conv =
      Ident.Env.add
        x
        {
          cv_internal_clock = x_vd.v_clock;
          cv_external_clock = x'_ck;
          cv_direction = dir;
        }
        conv
    in
    add_var_dec env x'_vd;
    (conv, make_eq (Var (x', x)) bck :: eqs), x'
  in

  let (conv, eqs), x'_l =
    Utils.mapfold_left_2
      (refresh_variable Nir.Push)
      (Ident.Env.empty, [])
      x_l
      x_ck_l
  in
  let (conv, eqs), y'_l =
    Utils.mapfold_left_2
      (refresh_variable Nir.Pop)
      (conv, eqs)
      y_l
      y_ck_l
  in
  let block =
    make_block
      ~conv
      bid
      (make_eq (mk_desc x'_l y'_l) bck :: eqs)
  in
  make_eq (Block block) base_clock

let rec equation env eq =
  match eq.eq_base_clock with
  | Clock_types.St_var _ ->
    (* do not generate blocks for variables on base *)
    eq
  | Clock_types.St_on _ ->
    match eq.eq_desc with
    | Var _
    | Buffer _
    | Call (_, { c_op = Box | Unbox | BufferAccess _; }, _)
    | Delay _ ->
    (* TODO: optimize buffer *)
      eq

    | Const (x, c) ->
      let mk_desc x_l _ =
        let x = Utils.assert1 x_l in
        Const (x, c)
      in
      form_block env eq.eq_base_clock mk_desc [x] [fun ck -> ck] [] []

    | Pword (x, p) ->
      let mk_desc x_l _ =
        let x = Utils.assert1 x_l in
        Pword (x, p)
      in
      form_block env eq.eq_base_clock mk_desc [x] [fun ck -> ck] [] []

    | Call (x_l, ({ c_op = Node (ln, id); } as call), y_l) ->
      let input_sts, output_sts =
        find_node_clock_sig_sliced env.senv ln id
      in

      assert (List.length input_sts = List.length y_l);
      assert (List.length output_sts = List.length x_l);

      let mk_desc x_l y_l =
        Call (x_l, call, y_l)
      in
      form_block
        env
        eq.eq_base_clock
        mk_desc
        x_l (List.map (Utils.flip Clock_types.reroot_stream_type) output_sts)
        y_l (List.map (Utils.flip Clock_types.reroot_stream_type) input_sts)

    | Merge (x, y, c_l) ->
      let ec_l, z_l = List.split c_l in
      let mk_desc x_l z_l =
        let x, y = Utils.assert2 x_l in
        Merge (x, y, List.combine ec_l z_l)
      in
      form_block
        env
        eq.eq_base_clock
        mk_desc
        [x; y] [(fun ck -> ck); fun ck -> ck]
        z_l (List.map (mk_sampled_clock (clock_exp_of_id env y)) ec_l)

    | Split (x_l, y, z, ec_l) ->
      let mk_desc x_l z_l =
        let y, z = Utils.assert2 z_l in
        Split (x_l, y, z, ec_l)
      in
      form_block
        env
        eq.eq_base_clock
        mk_desc
        x_l (List.map (mk_sampled_clock (clock_exp_of_id env z)) ec_l)
        [y; z] [(fun ck -> ck); fun ck -> ck]

    | Block blk ->
      Nir_sliced.make_eq
        ~loc:eq.eq_loc
        (Block (block env blk))
        eq.eq_base_clock

and block env block =
  assert (let Block_id x = block.b_id in x < get_current_block_count env);
  let body = List.map (equation env) block.b_body in
  Nir_sliced.make_block
    ~loc:block.b_loc
    ~conv:block.b_conv
    block.b_id
    body

let node env nd =
  Ident.set_current_ctx nd.n_orig_info#ni_ctx;
  enter_node env nd;
  let block = block env nd.n_body in
  Nir_sliced.make_node
    ~loc:nd.n_loc
    ~input:nd.n_input
    ~output:nd.n_output
    ~env:(get_var_decs env)
    ~body:block
    nd.n_name
    nd.n_orig_info

module U = Middleend_utils.Make(Nir_sliced)(Nir_sliced)

let tr ctx file =
  let env = initial_env file in
  U.map_to_nodes (node env) ctx file

let pass =
  U.(make_transform "block_formation" tr)
