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

(** Construction functions *)

let make_var ?(loc = Loc.dummy) x data_ty ck scope annots =
  {
    v_name = x;
    v_data = data_ty;
    v_clock = ck;
    v_scope = scope;
    v_annots = annots;
    v_loc = loc;
    v_info = ();
  }

let make_clock_exp ?bounds ?(loc = Loc.dummy) desc data clock =
  let bounds =
    match bounds with
    | Some bounds -> bounds
    | None ->
      match data with
      | Data_types.Tys_bool -> Interval.bool
      | _ -> invalid_arg "make_clock_exp: could not infer bounds"
  in
  {
    ce_desc = desc;
    ce_bounds = bounds;
    ce_data = data;
    ce_clock = clock;
    ce_loc = loc;
  }

let make_eq desc ck =
  {
    eq_desc = desc;
    eq_base_clock = ck;
    eq_loc = Loc.dummy;
  }

let make_call op inst ck x_l y_l =
  make_eq
    (Call
       (x_l,
        { a_op = op; a_stream_inst = inst; },
        y_l))
    ck

let make_block ?(loc = Loc.dummy) id body ck =
  make_eq
    (Block
       {
         b_id = id;
         b_body = body;
         b_loc = loc;
       })
    ck

(** Node context to add equations / variables / blocks *)

type ctx =
  {
    c_eqs : Ident.t eq list;
    c_vars : unit var_dec Ident.Env.t;
    c_first_free_block_id : int;
  }

let add_eq ctx eq = { ctx with c_eqs = eq :: ctx.c_eqs; }

let add_var ctx vd =
  {
    ctx with
      c_vars = Ident.Env.add vd.v_name vd ctx.c_vars;
  }

let get_fresh_block_id ctx =
  Block_id ctx.c_first_free_block_id,
  { ctx with c_first_free_block_id = ctx.c_first_free_block_id + 1; }

(** Iterators *)

(* Map *)

let rec map_eq_desc f proc =
  match proc with
  | Var (x, y) ->
    Var (f x, f y)
  | Const (x, cst) ->
    Const (f x, cst)
  | Call (x_l, app, y_l) ->
    Call (List.map f x_l, app, List.map f y_l)
  | Merge (x, ce, c_l) ->
    Merge (f x, ce, List.map (fun (ec, c) -> ec, f c) c_l)
  | Split (x_l, ce, y, ec_l) ->
    Split (List.map f x_l, ce, f y, ec_l)
  | Valof (x, ce) ->
    Valof (f x, ce)
  | Buffer (x, bu, y) ->
    Buffer (f x, bu, f y)
  | Delay (x, y) ->
    Delay (f x, f y)
  | Block block ->
    Block (map_block f block)

and map_eq f eq = { eq with eq_desc = map_eq_desc f eq.eq_desc; }

and map_block f block =
  { block with b_body = List.map (map_eq f) block.b_body; }

(* Fold *)

let rec fold_eq_desc f proc acc =
  match proc with
  | Var (x, y) ->
    let acc = f y acc in
    let acc = f x acc in
    acc
  | Const (x, _) ->
    f x acc
  | Call (x_l, _, y_l) ->
    let acc = List.fold_right f y_l acc in
    let acc = List.fold_right f x_l acc in
    acc
  | Merge (x, _, c_l) ->
    let f_clause (_, c) acc = f c acc in
    let acc = List.fold_right f_clause c_l acc in
    f x acc
  | Split (x_l, _, y, _) ->
    let acc = f y acc in
    List.fold_right f x_l acc
  | Valof (x, _) ->
    f x acc
  | Buffer (x, _, y) | Delay (x, y) ->
    f x (f y acc)
  | Block block ->
    fold_block f block acc

and fold_eq f eq acc = fold_eq_desc f eq.eq_desc acc

and fold_block f block acc = List.fold_right (fold_eq f) block.b_body acc

(** Compute variale occurences *)

let vars_eq eq = fold_eq (fun v acc -> v :: acc) eq []

let vars_block block = fold_block (fun v acc -> v :: acc) block []

(** Compute block count *)

let rec block_count_eq count eq =
  match eq.eq_desc with
  | Var _ | Const _ | Call _ | Merge _ | Split _ | Valof _ | Buffer _ | Delay _
      ->
    count
  | Block block ->
    block_count_block count block

and block_count_block count block =
  List.fold_left block_count_eq (succ count) block.b_body

(** Misc functions *)

(* Conversion between AcidS and Nir *)

let rec clock_type_exp_of_nir_clock_exp ce =
  match ce.ce_desc with
  | Ce_condvar v ->
    let open Clock_types in
    let cev =
      {
        cecv_name = v;
        cecv_bounds = ce.ce_bounds;
        cecv_specs = []
      }
    in
    Ce_condvar cev
  | Ce_pword pw ->
    Clock_types.Ce_pword pw
  | Ce_equal (ce, ec) ->
    Clock_types.Ce_equal (clock_type_exp_of_nir_clock_exp ce, ec)

let rec nir_stream_type_of_stream_type (st : Clock_types.stream_type) =
  let open Clock_types in
  match st with
  | St_var i -> St_var (Cv_clock (Clock_id i))
  | St_on (st, ce) -> St_on (nir_stream_type_of_stream_type st, ce)

let rec is_on_id id st =
  let open Clock_types in
  match st with
  | St_var id' -> id = id'
  | St_on (st, _) -> is_on_id id st

(* Clock-exp manipulating functions *)

let rec var_clock_exp ce =
  match ce.ce_desc with
  | Ce_condvar x -> Some x
  | Ce_pword _ -> None
  | Ce_equal (ce, _) -> var_clock_exp ce

let rec reroot_clock_exp ce new_x =
  let ced =
    match ce.ce_desc with
    | Ce_condvar _ -> Ce_condvar new_x
    | Ce_pword _ -> ce.ce_desc
    | Ce_equal (ce, ec) -> Ce_equal (reroot_clock_exp ce new_x, ec)
  in
  { ce with ce_desc = ced; }

(* Sliced names-related functions *)

let greatest_invalid_clock_id_int = -1

let greatest_invalid_clock_id = Nir.Clock_id greatest_invalid_clock_id_int

let print_sliced_name fmt (s, Clock_id i) =
  if i <= greatest_invalid_clock_id_int
  then Format.fprintf fmt "%s" s
  else Format.fprintf fmt "%s_st%d" s i

let print_sliced_longname fmt ln id =
  print_sliced_name fmt (Names.string_of_longname ln, id)

(* Conversion functions for clock types.

   The next two functions handle a subtle point of clock and data
   signatures in Acid Synchrone / NIR.

   Consider the following node:

   let node f (x, y) = (x, y) when (true)

   It has the signature (s):
   f : forall 'x, 'x1. ('x * 'x1) -> ('x * 'x1)
   f :: forall 'a. ('a * 'a) -> 'a

   We would like to know the clock types of the two outputs of f. However, since
   the output of f is a stream of tuples rather than a tuple of stream, it only
   has the clock (stream) type 'a for the two components, rather than 'a * 'a.

   Calling the function [signature_skeleton data_sig clock_sig] with [data_sig]
   and [clock_sig] the signatures defined above, we get a pair of input and
   output stream type lists ['a; 'a] and ['a; 'a].

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
        (fst nd.n_name)
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

(* Comparison functions *)

let block_id_compare (Block_id i1) (Block_id i2) = Utils.int_compare i1 i2

let clock_id_compare (Clock_id i1) (Clock_id i2) = Utils.int_compare i1 i2

let clock_var_compare cv1 cv2 =
  let tag_to_int id =
    match id with
    | Cv_block _ -> 0
    | Cv_clock _ -> 1
  in
  match cv1, cv2 with
  | Cv_block id1, Cv_block id2 ->
    block_id_compare id1 id2
  | Cv_clock id1, Cv_clock id2 ->
    clock_id_compare id1 id2
  | (Cv_block _ | Cv_clock _), _ ->
    Utils.int_compare (tag_to_int cv1) (tag_to_int cv2)

let clock_compare (ck1 : Nir.clock) ck2 =
  Clock_types.raw_st_compare clock_var_compare ck1 ck2

(* Various kinds of environments *)

module BlockEnv =
  Utils.MakeMap(
    struct
      type t = block_id
      let compare = block_id_compare
    end
  )
