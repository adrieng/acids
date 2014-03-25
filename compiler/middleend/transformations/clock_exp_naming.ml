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

(*
  This pass names all clock expressions and replaces them with Ce_names
*)

open Nir_sliced

(* {2 Environments} *)

module CeEnv = Utils.MakeMap(
  struct
    type t = Clock_types.clock_exp
    let compare = Clock_types.ce_compare
  end)

type env =
  {
    current_blocks : Nir.block_id list;
    new_eqs_per_block : eq list Utils.Int_map.t;
    current_ce : Clock_types.clock_exp CeEnv.t;
    current_vars : var_dec Ident.Env.t;
  }

let initial_env =
  {
    current_blocks = [];
    new_eqs_per_block = Utils.Int_map.empty;
    current_ce = CeEnv.empty;
    current_vars = Ident.Env.empty;
  }

let get_current_block env = List.hd env.current_blocks

let get_parent_block env = List.(hd (tl env.current_blocks))

let enter_block env block =
  { env with current_blocks = block.b_id :: env.current_blocks; }

let leave_block env = { env with current_blocks = List.tl env.current_blocks; }

let get_vars env = env.current_vars

let add_var env vd =
  { env with current_vars = Ident.Env.add vd.v_name vd env.current_vars; }

let get_eqs_for_block env (Nir.Block_id b_id) =
  try Utils.Int_map.find b_id env.new_eqs_per_block
  with Not_found -> []

let add_eq_for_block env (Nir.Block_id b_id) eq =
  let eqs = get_eqs_for_block env (Nir.Block_id b_id) in
  let new_eqs_per_block =
    Utils.Int_map.add b_id (eq :: eqs) env.new_eqs_per_block
  in
  { env with new_eqs_per_block = new_eqs_per_block; }

let add_eq_for_current_block env = add_eq_for_block env (get_current_block env)

let find_ce env ce =
  CeEnv.find ce env.current_ce

let add_ce env b_id orig_ce st tys id bounds specs eq =
  let open Clock_types in
  let ce =
    Ce_condvar { cecv_name = id; cecv_bounds = bounds; cecv_specs = specs; }
  in
  let vd =
    make_var_dec
      id
      (Nir.Ty_scal tys)
      st
      (Nir.Scope_internal b_id)
  in
  let env = add_var env vd in
  let env = add_eq_for_block env b_id eq in
  { env with current_ce = CeEnv.add orig_ce ce env.current_ce; },
  ce

(* {2 Helper functions} *)

let get_ce_name ce =
  let open Clock_types in
  match ce with
  | Ce_condvar cecv -> cecv.cecv_name
  | _ -> invalid_arg "get_ce_name: not a condvar"

(* {2 AST Traversal} *)

let rec clock_exp env b_id base_st ce =
  let open Clock_types in
  match ce with
  | Ce_condvar _ ->
    env, ce
  | Ce_pword pw ->
    (
      try env, find_ce env ce
      with Not_found ->
        let id = Ident.make_internal "ce" in
        let ipw = Ast_misc.int_pword_of_econstr_pword pw in
        let bounds =
          let l, u = Ast_misc.bounds_of_int_pword ipw in
          Interval.make l u
        in
        let specs =
          [
            Ast_misc.Word ipw;
            Ast_misc.Interval bounds;
          ]
        in
        add_ce
          env
          b_id
          ce
          base_st
          Data_types.Tys_int (* TODO fix... not easy *)
          id
          bounds
          specs
          (
            make_eq
              (Pword (id, pw))
              base_st
          )
    )
  | Ce_equal (ice, ec) ->
    let env, ice = clock_exp env b_id base_st ice in
    let id_ec = Ident.make_internal "ec" in
    let ec_vd =
      make_var_dec
        id_ec
        (Nir.Ty_scal Data_types.Tys_int)
        base_st
        (Nir.Scope_internal b_id)
    in
    let ec_eq =
      make_eq
        (Const (id_ec, Ast_misc.Cconstr ec))
        base_st
    in
    let env = add_eq_for_block (add_var env ec_vd) b_id ec_eq in

    let id = Ident.make_internal "ce" in
    let bounds = Interval.bool in
    let specs =
      [
        Ast_misc.Interval bounds;
      ]
    in
    let call =
      {
        c_op = Node (Names.(make_longname (Module "Pervasives") "(=)"), 0);
        c_stream_inst = [];
      }
    in

    add_ce
      env
      b_id
      ce
      base_st
      Data_types.Tys_bool
      id
      bounds
      specs
      (
        make_eq
          (Call ([id], call, [get_ce_name ice; id_ec]))
          base_st
      )

let rec clock env b_id ck =
  let open Clock_types in
  match ck with
  | St_var _ ->
    env, ck
  | St_on (ck, ce) ->
    let env, ck = clock env b_id ck in
    let env, ce = clock_exp env b_id ck ce in
    env, St_on (ck, ce)

let var_dec vd env =
  let b_id =
    match vd.v_scope with
    | Nir.Scope_internal b_id ->
      b_id
    | Nir.Scope_context | Nir.Scope_input | Nir.Scope_output ->
      Nir.Block_id 0
  in
  let env, ck = clock env b_id vd.v_clock in
  let vd =
    make_var_dec
      ~loc:vd.v_loc
      ~annots:vd.v_annots
      vd.v_name
      vd.v_data
      ck
      vd.v_scope
  in
  add_var env vd

let rec equation env eq =
  let env, eqd =
    match eq.eq_desc with
    | Var _ | Const _ | Pword _ | Call _ | Merge _ | Split _ | Buffer _
    | Delay _ ->
      env, eq.eq_desc
    | Block bl ->
      let env, bl = block env bl in
      env, Block bl
  in
  let env, bst = clock env (get_current_block env) eq.eq_base_clock in
  env,
  make_eq
    ~loc:eq.eq_loc
    eqd
    bst

and block env bl =
  let env = enter_block env bl in
  let conv, env =
    let do_conv id cv (conv, env) =
      let env, int =
        clock env (get_current_block env) cv.cv_internal_clock
      in
      let env, ext =
        clock env (get_parent_block env) cv.cv_external_clock in
      Ident.Env.add
        id
        { cv with cv_internal_clock = int; cv_external_clock = ext; }
        conv,
      env
    in
    Ident.Env.fold do_conv bl.b_conv (Ident.Env.empty, env)
  in
  let env, body = Utils.mapfold_left equation env bl.b_body in
  leave_block env,
  make_block
    ~loc:bl.b_loc
    ~conv
    bl.b_id
    (get_eqs_for_block env bl.b_id @ body)

let node nd =
  Ident.set_current_ctx nd.n_orig_info#ni_ctx;
  let env = initial_env in
  let env = Ident.Env.fold (fun _ -> var_dec) nd.n_env env in
  let env, body = block env nd.n_body in
  make_node
    ~loc:nd.n_loc
    nd.n_name
    nd.n_orig_info
    ~input:nd.n_input
    ~output:nd.n_output
    ~env:(get_vars env)
    ~body

(* {2 Put it all together} *)

module U = Middleend_utils.Make(Nir_sliced)(Nir_sliced)

let pass =
  U.(make_transform "clock_exp_namin" (map_to_nodes node))
