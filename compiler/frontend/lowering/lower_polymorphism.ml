(* Copyright (C) Adrien Guatto <adrien.guatto@laposte.net> 2013
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

(** {1 Add boxing/unboxing functions around polymorphic variables in function
    applications}

    f : int * 'x -> 'x * bool * 'x

    (x, y, (z, z')) = f (4, (2, k))

    ->

    bx1 = box (2, k)
    (bx2, y, bx3) = f (4, bx1)
    x = unbox bx2
    (z, z') = unbox bx3

    Applies after lower_tuples.

    TODO: generate well-typed code around functions. For this we would need to
    modify on the fly the data type signatures in the interface.
*)

module SUB = Acids_utils.MAP_SUB(Acids_causal)

open Acids_causal
open Acids_causal_utils

let poly_var_prefix = "bx"

type env =
  {
    intf_env : Interface.env;
    local_nodes : Data_types.data_sig Names.ShortEnv.t;
    current_eqs : eq list;
  }

let initial_env file =
  let add_node local_nodes phr =
    match phr with
    | Phr_node_def nd ->
      Names.ShortEnv.add nd.n_name nd.n_info#ni_data local_nodes
    | Phr_node_decl nd ->
      Names.ShortEnv.add nd.decl_name nd.decl_data local_nodes
    | Phr_type_def _ | Phr_const_def _ | Phr_pword_def _ ->
      local_nodes
  in
  {
    intf_env = file.f_info#interfaces;
    local_nodes = List.fold_left add_node Names.ShortEnv.empty file.f_body;
    current_eqs = [];
  }

let find_node env ln =
  let open Names in
  match ln.modn with
  | LocalModule ->
    Names.ShortEnv.find ln.shortn env.local_nodes
  | Module modn ->
    let intf = Names.ShortEnv.find modn env.intf_env in
    Interface.(data_signature_of_node_item (find_node intf ln.shortn))

let add_eq env eq = { env with current_eqs = eq :: env.current_eqs; }

let close_env env = { env with current_eqs = []; }, env.current_eqs

(** *)

let make_app sn ct =
  {
    a_op = Names.(make_longname (Module "Pervasives") sn);
    a_loc = Loc.dummy;
    a_info =
      object
        method ai_stream_inst = []
        method ai_clock_inst = [ 0, ct; ]
      end;
  }

let make_box_app = make_app "box"

let make_unbox_app = make_app "unbox"

let change_data_type_exp e ty =
  object
    method ei_data = ty
    method ei_clock = e.e_info#ei_clock
    method ei_relevant_deps = e.e_info#ei_relevant_deps
  end

let change_data_type_pat p ty =
  object
    method pi_data = ty
    method pi_clock = p.p_info#pi_clock
  end

(* We walk the data type of inputs and input argument and introduce boxes when
   we see a type variable. *)
let rec box_input env ty input =
  let open Data_types in
  match ty, input.e_desc with
  | (Ty_scal _ | Ty_cond _ | Ty_boxed _), _ ->
    env, input
  | Ty_prod ty_l, E_tuple e_l ->
    let env, e_l = Utils.mapfold_left_2 box_input env ty_l e_l in
    let ty_l = List.map (fun e -> e.e_info#ei_data) e_l in
    let ty = Ty_prod ty_l in
    env,
    {
       input with
         e_desc = E_tuple e_l;
         e_info = change_data_type_exp input ty;
    }
  | Ty_prod _, _ ->
    invalid_arg "box_input: non-normalized product type"
  | Ty_var _, _ ->
    let v = Ident.make_internal poly_var_prefix in
    let boxed_ty = Ty_boxed input.e_info#ei_data in
    let boxing_eq =
      let body =
        make_exp
          boxed_ty
          input.e_info#ei_clock
          (E_app (make_box_app input.e_info#ei_clock, input))
      in
      let pat =
        make_pat
          boxed_ty
          input.e_info#ei_clock
          (P_var v)
      in
      {
        eq_desc = Eq_plain (pat, body);
        eq_loc = Loc.dummy;
        eq_info = ();
      }
    in
    add_eq env boxing_eq,
    {
      input with
        e_desc = E_var v;
        e_info = change_data_type_exp input boxed_ty;
    }

(* Same technique for outputs *)
let rec unbox_output env ty output =
  let open Data_types in
  match ty, output.p_desc with
  | (Ty_scal _ | Ty_cond _ | Ty_boxed _), _ ->
    env, output
  | Ty_prod ty_l, P_tuple p_l ->
    let env, p_l = Utils.mapfold_left_2 unbox_output env ty_l p_l in
    let ty_l = List.map (fun p -> p.p_info#pi_data) p_l in
    let ty = Ty_prod ty_l in
    env,
    {
       output with
         p_desc = P_tuple p_l;
         p_info = change_data_type_pat output ty;
    }
  | Ty_prod _, _ ->
    invalid_arg "unbox_output: non-normalized product type"
  | Ty_var _, _ ->
    let v = Ident.make_internal poly_var_prefix in
    let boxed_ty = Ty_boxed output.p_info#pi_data in
    let unboxing_eq =
      let body =
        let unbox_arg =
          make_exp
            boxed_ty
            output.p_info#pi_clock
            (E_var v)
        in
        make_exp
          output.p_info#pi_data
          output.p_info#pi_clock
          (E_app (make_unbox_app output.p_info#pi_clock, unbox_arg))
      in
      {
        eq_desc = Eq_plain (output, body);
        eq_loc = Loc.dummy;
        eq_info = ();
      }
    in
    add_eq env unboxing_eq,
    {
      output with
        p_desc = P_var v;
        p_info = change_data_type_pat output boxed_ty;
    }

(** {2 AST traversal} *)

let rec do_eq env eq =
  match eq.eq_desc with
  | Eq_condvar _ ->
    env, eq
  | Eq_plain (lhs, rhs) ->
    let env, lhs, rhs =
      match rhs.e_desc with
      | E_where (e, block) ->
        env, lhs, { rhs with e_desc = E_where (e, do_block env block); }
      | E_app (app, e_arg) ->
        let ty_sig = find_node env app.a_op in
        let env, e_arg = box_input env ty_sig.Data_types.data_sig_input e_arg in
        let env, lhs = unbox_output env ty_sig.Data_types.data_sig_output lhs in
        env, lhs, { rhs with e_desc = E_app (app, e_arg); }
      | _ ->
        env, lhs, rhs
    in
    env, { eq with eq_desc = Eq_plain (lhs, rhs); }

and do_block env block =
  let env, body = Utils.mapfold_left do_eq env block.b_body in
  {
    b_body = env.current_eqs @ body;
    b_loc = block.b_loc;
    b_info = block.b_info;
  }

let do_node env input body =
  match body.e_desc with
  | E_where (e, block) ->
    input, { body with e_desc = E_where (e, do_block env block); };
  | _ ->
    invalid_arg "node_def: non-normalized"

let do_file file =
  let env = initial_env file in
  apply_to_node_defs (do_node env) file

(** {2 Putting it all together} *)

let pass = Lowering_utils.make_transform_by_file do_file "lower_polymorphism"
