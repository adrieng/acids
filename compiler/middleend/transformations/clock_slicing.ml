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

    This pass slices a node into several ones, according to clock variables. For
    example, the following node will get sliced as two separate codes:

    let node f (x, y) = (0 fby x, 0 fby y)

    ->

    let node f_a0 x = 0 fby x
    let node f_a1 y = 0 fby y

    Invariant: after this pass, each node has only one clock or stream variable, its
    base clock variable.
*)

type var =
  | Stream of int
  | Clock of int

let var_compare v1 v2 =
  let tag_to_int v =
    match v with
    | Stream _ -> 0
    | Clock _ -> 1
  in
  match v1, v2 with
  | Stream i1, Stream i2
  | Clock i1, Clock i2 ->
    Utils.int_compare i1 i2
  | (Stream _ | Clock _), _ ->
    Utils.int_compare (tag_to_int v1) (tag_to_int v2)

module VarEnv = Utils.MakeMap(struct type t = var let compare = var_compare end)

(** {2 Utilities} *)

let sliced_short_name sn v =
  match v with
  | Stream i -> sn ^ "_st" ^ string_of_int i
  | Clock i -> sn ^ "_ck" ^ string_of_int i

let sliced_node_name (Node nn) v =
  let open Names in
  Node { nn with shortn = sliced_short_name nn.shortn v; }

let rec base_var_of_stream_type st =
  let open Clock_types in
  match st with
  | St_var i -> Stream i
  | St_on (st, _) -> base_var_of_stream_type st

let base_var_of_clock_type ck =
  match ck with
  | Ck_var v ->
    Clock v
  | Ck_stream st -> base_var_of_stream_type st
  | Ck_block_base _ ->
    invalid_arg "base_var_of_clock_type: Ck_block_base"

let base_var_eq eq =
  match eq.eq_desc with
  | Var _
  | Const _
  | Merge _
  | Valof _
  | Buffer _
  | Delay _
  | Block _
    ->
    base_var_of_clock_type eq.eq_base_clock

  | Call _ ->
    invalid_arg "base_var_eq"

  | Split (_, ce, _, _) ->
    base_var_of_clock_type ce.ce_clock

(** {2 Environments} *)

type env =
  {
    current_vars : unit Nir.var_dec Ident.Env.t;
    current_nodes : (unit var_dec Ident.Env.t *
                     int *
                     Ident.t Nir.eq list) VarEnv.t;
  }

let initial_env current_vars =
  {
    current_vars = current_vars;
    current_nodes = VarEnv.empty;
  }

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

(** {2 AST traversal} *)

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
  | Call (x_l, app, y_l) ->
    let x_l_by_base_rev = gather_vars env.current_vars VarEnv.empty x_l in
    let y_l_by_base_rev = gather_vars env.current_vars VarEnv.empty y_l in

    let make_call env base_clock_var base_clock clock_inst stream_inst =
      let x_l = List.rev (VarEnv.find base_clock_var x_l_by_base_rev) in
      let y_l = List.rev (VarEnv.find base_clock_var y_l_by_base_rev) in
      let app =
        {
          a_op = sliced_node_name app.a_op base_clock_var;
          a_clock_inst = clock_inst;
          a_stream_inst = stream_inst;
        }
      in
      let eq =
        {
          eq_desc = Call (x_l, app, y_l);
          eq_base_clock = base_clock;
          eq_loc = eq.eq_loc;
        }
      in
      add_eq_to_its_node env base_clock_var eq
    in

    let make_call_ct env (ct_i_var, ct) =
      let base_clock_var = Clock ct_i_var in
      let base_clock = Ck_block_base (Block_id 0) in
      let stream_inst = [] in
      let clock_inst = [ct_i_var, ct] in
      make_call env base_clock_var base_clock clock_inst stream_inst
    in

    let make_call_st env (st_i_var, st) =
      let base_clock_var = Stream st_i_var in
      let base_clock = Ck_stream st in
      let stream_inst = [st_i_var, st] in
      let clock_inst = [] in
      make_call env base_clock_var base_clock clock_inst stream_inst
    in

    let env = List.fold_left make_call_ct env app.a_clock_inst in
    List.fold_left make_call_st env app.a_stream_inst
  | Var _ | Const _ | Merge _ | Split _ | Valof _
  | Buffer _ | Delay _ | Block _ ->
    let base_clock_var = base_var_eq eq in
    add_eq_to_its_node env base_clock_var eq

let node nd_l nd =
  let env = List.fold_left equation (initial_env nd.n_env) nd.n_body.b_body in
  let inputs_by_base_rev =
    gather_vars env.current_vars VarEnv.empty nd.n_input
  in
  let outputs_by_base_rev =
    gather_vars env.current_vars VarEnv.empty nd.n_output
  in

  let make_node base_clock_var (var_env, block_count, body) nd_l =
    let inputs = List.rev (VarEnv.find base_clock_var inputs_by_base_rev) in
    let outputs = List.rev (VarEnv.find base_clock_var outputs_by_base_rev) in

    let nd =
      {
        n_name = sliced_short_name nd.n_name base_clock_var;
        n_orig_info = nd.n_orig_info;
        n_input = inputs;
        n_output = outputs;
        n_env = var_env;
        n_block_count = block_count;
        n_body = { nd.n_body with b_body = body; };
        n_loc = nd.n_loc;
      }
    in
    nd :: nd_l
  in

  VarEnv.fold make_node env.current_nodes nd_l

let file ctx file =
  let nodes = List.fold_left node [] file.f_body in
  ctx, { file with f_body = List.rev nodes; }

let pass =
  Middleend_utils.(make_transform "clock_slicing" file)
