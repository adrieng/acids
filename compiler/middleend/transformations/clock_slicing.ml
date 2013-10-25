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

open Nir

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

type var = Stream of int

let mk_var i = Stream i
let unmk_var (Stream i) = i

let print_var fmt (Stream i) = Format.fprintf fmt "(stream %d)" i

let var_compare (Stream i1) (Stream i2) =
  Utils.int_compare i1 i2

module VarEnv = Utils.MakeMap(struct type t = var let compare = var_compare end)

(** {2 Utilities} *)

let rec base_var_of_stream_type st =
  let open Clock_types in
  match st with
  | St_var i -> Stream i
  | St_on (st, _) -> base_var_of_stream_type st

let base_var_of_clock_type ck =
  match ck with
  | Ck_block_base _ -> invalid_arg "base_var_of_clock_type"
  | Ck_stream st -> base_var_of_stream_type st

(** {2 Environments} *)

type env =
  {
    intf_env : Interface.env;
    local_clock_sigs : Clock_types.clock_sig Names.ShortEnv.t;
    current_vars : unit Nir.var_dec Ident.Env.t;
    current_nodes : (unit var_dec Ident.Env.t *
                     int *
                     Ident.t Nir.eq list) VarEnv.t;
  }

let initial_env file =
  let local_clock_sigs =
    let add local_clock_sigs nd =
      Names.ShortEnv.add nd.n_name nd.n_orig_info#ni_clock local_clock_sigs
    in
    List.fold_left add Names.ShortEnv.empty file.f_body
  in
  {
    intf_env = file.f_info;
    local_clock_sigs = local_clock_sigs;
    current_vars = Ident.Env.empty;
    current_nodes = VarEnv.empty;
  }

let set_current_var env current_vars = { env with current_vars = current_vars; }

let add_eq_to_its_node env v eq =
  let node_var_env, node_block_count, node_body =
    try VarEnv.find v env.current_nodes
    with Not_found -> Ident.Env.empty, 0, []
  in

  let node_var_env =
    let add node_var_env v =
      let vd = Ident.Env.find v env.current_vars in
      Ident.Env.add v vd node_var_env
    in
    List.fold_left add node_var_env (Nir_utils.vars_eq eq)
  in

  let node_info =
    node_var_env,
    Nir_utils.block_count_eq node_block_count eq,
    eq :: node_body
  in

  { env with current_nodes = VarEnv.add v node_info env.current_nodes; }

let find_var_clock env x =
  let x_vd = Ident.Env.find x env.current_vars in
  x_vd.v_clock

let find_node_sig env ln =
  let open Names in
  match ln.modn with
  | LocalModule ->
    ShortEnv.find ln.shortn env.local_clock_sigs
  | Module modn ->
    let intf = ShortEnv.find modn env.intf_env in
    Interface.(clock_signature_of_node_item (find_node intf ln.shortn))

let has_several_clock_variables env ln =
  let ct_sig = find_node_sig env ln in
  Clock_types.(VarKindSet.cardinal (base_sig_vars ct_sig) > 1)

let sliced_short_name sn (Stream i) = sn ^ "_st" ^ string_of_int i

let sliced_node_name env op v =
  match op with
  | Node nn ->
    Node
      (
        if has_several_clock_variables env nn
        then Names.({ nn with shortn = sliced_short_name nn.shortn v; })
        else nn
      )
  | Box | Unbox ->
    op

(** {2 AST traversal} *)

let base_clock_var_eq env eq =
  match eq.eq_desc with
  | Var _
  | Const _
  | Merge _
  | Valof _
  | Delay _
  | Block _
    ->
    base_var_of_clock_type eq.eq_base_clock

  | Call _ ->
    invalid_arg "base_var_eq"

  | Split (_, ce, _, _) ->
    base_var_of_clock_type ce.ce_clock

  | Buffer (x, _, _) ->
    base_var_of_clock_type (find_var_clock env x)

let gather_vars var_env ck_env v_l =
  let add_var ck_env v =
    let vd = Ident.Env.find v var_env in
    let base_clock_var = base_var_of_clock_type vd.v_clock in
    let v_l = try VarEnv.find base_clock_var ck_env with Not_found -> [] in
    VarEnv.add base_clock_var (v :: v_l) ck_env
  in
  List.fold_left add_var ck_env v_l

let equation env eq =
  match eq.eq_desc with
  | Call (x_l, ({ a_op = Node ln; } as app), y_l) ->
    (* For each clock variable 'a in signature instantiated with st, walk the
       list of inputs and outputs and gather the ones that correspond to
       parameters of base clock 'a. *)
    let ty_sig = find_node_sig env ln in

    let input_st_list =
      Clock_types.(flatten_clock_type [] ty_sig.ct_sig_input)
    in
    let output_st_list =
      Clock_types.(flatten_clock_type [] ty_sig.ct_sig_output)
    in

    (* Format.eprintf "Call to %a@." *)
    (*   Names.print_longname ln; *)
    (* Format.eprintf "input_st_list: @[%a@]@." *)
    (*   (Utils.print_list_r Clock_types.print_stream_type ",") input_st_list; *)
    (* Format.eprintf "x_l: @[%a@]@." *)
    (*   (Utils.print_list_r Ident.print ",") x_l; *)

    assert (List.length input_st_list = List.length y_l);
    assert (List.length output_st_list = List.length x_l);

    let gather_vars_on_base base_st_var acc var var_st =
      let var_st = Nir.Ck_stream var_st in
      let base_input_st = base_var_of_clock_type var_st in
      if 0 = var_compare base_st_var base_input_st then var :: acc else acc
    in

    let make_call_st
        env
        (base_st_var, base_st)
        =
      let base = mk_var base_st_var in
      let relevant_x_l_rev =
        List.fold_left2 (gather_vars_on_base base) [] y_l input_st_list in
      let relevant_y_l_rev =
        List.fold_left2 (gather_vars_on_base base) [] x_l output_st_list in

      let app =
        {
          a_op = sliced_node_name env app.a_op base;
          a_stream_inst = [base_st_var, base_st];
        }
      in
      let eq =
        {
          eq_desc =
            Call (List.rev relevant_x_l_rev, app, List.rev relevant_y_l_rev);
          eq_base_clock = Nir.Ck_stream base_st;
          eq_loc = eq.eq_loc;
        }
      in
      add_eq_to_its_node env base eq
    in
    List.fold_left make_call_st env app.a_stream_inst

  | Call (_, { a_op = Box | Unbox; }, _)
  | Var _ | Const _ | Merge _ | Split _ | Valof _
  | Buffer _ | Delay _ | Block _ ->
    let base_clock_var = base_clock_var_eq env eq in
    add_eq_to_its_node env base_clock_var eq

let node env nd_l nd =
  if has_several_clock_variables env (Names.make_local nd.n_name)
  then
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
          n_name = sliced_short_name nd.n_name base_clock_var;
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
  else
    nd :: nd_l

let file ctx file =
  let env = initial_env file in
  let nodes = List.fold_left (node env) [] file.f_body in
  ctx, { file with f_body = List.rev nodes; }

let pass =
  Middleend_utils.(make_transform "clock_slicing" file)
