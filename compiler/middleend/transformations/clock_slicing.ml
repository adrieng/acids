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

open Nir_acids

(** {1 Clock slicing}

    This pass slices a node into several ones, according to the clock variables
    present in its signature. For example, the following node will get sliced as
    two separate codes:

    let node f (x, y) = (0 fby x, 0 fby y)

    ->

    let node f_a0 x = 0 fby x
    let node f_a1 y = 0 fby y

    Invariant: after this pass, each node has at most one stream variable, its
    base clock variable.
*)

let mk_var i =
  Info.Cv_clock i
let unmk_var cv =
  match cv with
  | Info.Cv_base -> assert false
  | Info.Cv_clock i -> i

let var_compare cv1 cv2 =
  let open Info in
  let tag_to_int cv =
    match cv with
    | Cv_base -> 0
    | Cv_clock _ -> 1
  in
  match cv1, cv2 with
  | Cv_base, Cv_base ->
    0
  | Cv_clock i1, Cv_clock i2 ->
    Utils.int_compare i1 i2
  | (Cv_base | Cv_clock _), _ ->
    Utils.int_compare (tag_to_int cv1) (tag_to_int cv2)

module VarEnv =
  Utils.MakeMap(
    struct
      type t = Info.clock_var
      let compare = var_compare
    end)

(** {2 Utilities} *)

let clock_var_of_acids_stream_type st =
  Info.Cv_clock (Clock_types.base_var_of_stream_type st)

let clock_var_of_nir_stream_type st =
  match Clock_types.base_var_of_stream_type st with
  | Info.Cv_clock i -> Info.Cv_clock i
  | Info.Cv_base -> invalid_arg "clock_var_of_stream_type"

(** {2 Environments} *)

type env =
  {
    senv : signature_env;
    current_vars : var_dec Ident.Env.t;
    current_nodes : (Nir_sliced.var_dec Ident.Env.t *
                     int *
                     Nir_sliced.eq list) VarEnv.t;
  }

let print_env fmt env =
  let print_node fmt (var_env, i, eqs) =
    Format.fprintf fmt
      "(@[var_env = @[%a@],@ blocks = %d,@ eqs = @[%a@]@])"
      (Ident.Env.print Nir_sliced.print_var_dec ",") var_env
      i
      (Utils.print_list_r Nir_sliced.print_eq ",") eqs
  in
  Format.fprintf fmt "@[@[current_vars:@ %a@]@\n"
    (Ident.Env.print print_var_dec ";")
    env.current_vars;
  Format.fprintf fmt "@[current_nodes:@ %a@]@]"
    (VarEnv.print Info.print_clock_var print_node)
    env.current_nodes

let initial_env file =
  {
    senv = signature_env_of_file file;
    current_vars = Ident.Env.empty;
    current_nodes = VarEnv.empty;
  }

let set_current_var env current_vars = { env with current_vars = current_vars; }

let rec translate_clock st =
  let open Clock_types in
  match st with
  | St_var _ -> St_var Nir_sliced.Info.Cv_base
  | St_on (st, ce) -> St_on (translate_clock st, ce)

let translate_annot ann =
  match ann with
  | Ann_type ty -> Nir_sliced.Ann_type ty
  | Ann_clock ck -> Nir_sliced.Ann_clock (translate_clock ck)
  | Ann_spec spec -> Nir_sliced.Ann_spec spec

let translate_scope scope =
  match scope with
  | Scope_context -> Nir_sliced.Scope_context
  | Scope_internal bid -> Nir_sliced.Scope_internal bid

let translate_var_dec vd =
  Nir_sliced.make_var_dec
    ~loc:vd.v_loc
    ~annots:(List.map translate_annot vd.v_annots)
    vd.v_name
    vd.v_data
    (translate_clock vd.v_clock)
    (translate_scope vd.v_scope)

let add_eq_to_its_node env v (eq : Nir_sliced.eq) =
  let node_var_env, node_block_count, node_body =
    try VarEnv.find v env.current_nodes
    with Not_found -> Ident.Env.empty, 0, []
  in

  let node_var_env =
    let add node_var_env v =
      let vd = Ident.Env.find v env.current_vars in
      let vd = translate_var_dec vd in
      Ident.Env.add v vd node_var_env
    in
    List.fold_left add node_var_env (Nir_sliced.eq_vars [] eq)
  in

  let node_info =
    node_var_env,
    Nir_sliced.block_count_eq node_block_count eq,
    eq :: node_body
  in
  { env with current_nodes = VarEnv.add v node_info env.current_nodes; }

let find_var_clock env x =
  let x_vd = Ident.Env.find x env.current_vars in
  x_vd.v_clock

let find_node_sig env ln = find_node_sig env.senv ln

let has_several_clock_variables env ln =
  let ct_sig, _ = find_node_sig env ln in
  Clock_types.(VarKindSet.cardinal (base_sig_vars ct_sig) > 1)

let sliced_node_name op v =
  match op with
  | Node nn ->
    Nir_sliced.Node (nn, v)
  | Box ->
    Nir_sliced.Box
  | Unbox ->
    Nir_sliced.Unbox
  | BufferAccess (dir, pol) ->
    Nir_sliced.BufferAccess (dir, pol)

(** {2 AST traversal} *)

let base_clock_var_eq env eq =
  match eq.eq_desc with
  | Var _
  | Const _
  | Pword _
  | Merge _
  | Split _
  | Delay _
  | Block _
    ->
    clock_var_of_nir_stream_type eq.eq_base_clock

  | Call _ ->
    invalid_arg "base_var_eq"

  | Buffer (x, _, _) ->
    clock_var_of_nir_stream_type (find_var_clock env x)

let gather_vars var_env ck_env v_l =
  let add_var ck_env v =
    let vd = Ident.Env.find v var_env in
    let base_clock_var = clock_var_of_nir_stream_type vd.v_clock in
    let v_l =
      try VarEnv.find base_clock_var ck_env with Not_found -> []
    in
    VarEnv.add base_clock_var (v :: v_l) ck_env
  in
  List.fold_left add_var ck_env v_l

let equation env eq =
  match eq.eq_desc with
  | Call (x_l, ({ a_op = Node ln; } as app), y_l) ->
    let ty_sig, data_sig = find_node_sig env ln in

    (* For each clock variable 'a in signature instantiated with st, walk the
       list of inputs and outputs and gather the ones that correspond to
       parameters of base clock 'a. *)

    let input_st_list, output_st_list = signature_skeleton ty_sig data_sig in

    assert (List.length input_st_list = List.length y_l);
    assert (List.length output_st_list = List.length x_l);

    let gather_vars_on_base base_st_var acc var param_st =
      let base_input_st = clock_var_of_acids_stream_type param_st in
      if 0 = Utils.int_compare base_st_var base_input_st
      then var :: acc
      else acc
    in

    let make_call_st
        env
        (base_sig_var, (inst_st : Clock_types.stream_type))
        =
      let inst_st = Nir_of_acids.translate_stream_type inst_st in
      let base = mk_var base_sig_var in
      let relevant_y_l_rev =
        List.fold_left2 (gather_vars_on_base base) [] y_l input_st_list
      in
      let relevant_x_l_rev =
        List.fold_left2 (gather_vars_on_base base) [] x_l output_st_list
      in

      let app =
        {
          Nir_sliced.a_op = sliced_node_name app.a_op base_sig_var;
          Nir_sliced.a_stream_inst = [];
        }
      in
      let call_eq =
        Nir_sliced.make_eq
          ~loc:eq.eq_loc
          (Nir_sliced.Call
             (List.rev relevant_x_l_rev,
              app,
              List.rev relevant_y_l_rev))
          (translate_clock inst_st)
      in
      add_eq_to_its_node env (clock_var_of_nir_stream_type inst_st) call_eq
    in
    List.fold_left make_call_st env app.a_stream_inst

  | Call (x_l, { a_op = Box; }, _) ->
    (* Box expects a synchronized tuple as input *)
    let x = Utils.assert1 x_l in
    let base_clock_var = clock_var_of_nir_stream_type (find_var_clock env x) in
    add_eq_to_its_node env base_clock_var eq

  | Call (_, { a_op = Unbox; }, y_l) ->
    (* Same for unbox's output *)
    let y = Utils.assert1 y_l in
    let base_clock_var = clock_var_of_stream_type (find_var_clock env y) in
    add_eq_to_its_node env base_clock_var eq

  | Call (_, { a_op = BufferAccess _; }, _) ->
    (* Unhandled at this level *)
    assert false

  | Var _ | Const _ | Pword _ | Merge _ | Split _
  | Buffer _ | Delay _ | Block _ ->
    let base_clock_var = base_clock_var_eq env eq in
    add_eq_to_its_node env base_clock_var eq

let node env nd_l nd =
  let node_name, Clock_id dummy = nd.n_name in
  assert (dummy <= Nir_utils.greatest_invalid_clock_id_int);
  let env = set_current_var env nd.n_env in
  let env = List.fold_left equation env nd.n_body.b_body in
  let inputs_by_base_rev =
    gather_vars env.current_vars VarEnv.empty nd.n_input
  in
  let outputs_by_base_rev =
    gather_vars env.current_vars VarEnv.empty nd.n_output
  in

  let make_node base_clock_var (var_env, block_count, body) nd_l =
    let find_vars map =
      try List.rev (VarEnv.find base_clock_var map) with Not_found -> []
    in

    let inputs = find_vars inputs_by_base_rev in
    let outputs = find_vars outputs_by_base_rev in

    let nd =
      {
        n_name = node_name, base_clock_var;
        n_orig_info = nd.n_orig_info;
        n_input = inputs;
        n_output = outputs;
        n_env = var_env;
        n_block_count = succ block_count;
        n_body = { nd.n_body with b_body = body; };
        n_loc = nd.n_loc;
      }
    in
    nd :: nd_l
  in
  VarEnv.fold make_node env.current_nodes nd_l

let file ctx file =
  let env = initial_env file in
  let nodes = List.fold_left (node env) [] file.f_body in
  ctx, { file with f_body = List.rev nodes; }

let pass =
  Middleend_utils.(make_transform "clock_slicing" file)
