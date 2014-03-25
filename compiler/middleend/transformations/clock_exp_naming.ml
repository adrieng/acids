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
    current_block : Nir.block_id;
    current_eqs : eq list;
    current_ce : Clock_types.clock_exp CeEnv.t;
    current_vars : var_dec Ident.Env.t;
  }

let initial_env nd =
  {
    current_block = nd.n_body.b_id;
    current_eqs = [];
    current_ce = CeEnv.empty;
    current_vars = Ident.Env.empty;
  }

let get_current_block env = env.current_block

let enter_block env block =
  { env with current_block = block.b_id; }

let fuse_envs env ~nested_env =
  {
    env with
      current_vars = Ident.Env.union env.current_vars nested_env.current_vars;
  }

let get_vars env = env.current_vars

let add_var env vd =
  { env with current_vars = Ident.Env.add vd.v_name vd env.current_vars; }

let get_eqs env = env.current_eqs

let add_eq env eq = { env with current_eqs = eq :: env.current_eqs; }

let find_ce env ce =
  CeEnv.find ce env.current_ce

let add_ce env orig_ce st tys id bounds specs eq =
  let open Clock_types in
  let ce =
    Ce_condvar { cecv_name = id; cecv_bounds = bounds; cecv_specs = specs; }
  in
  let vd =
    make_var_dec
      id
      (Nir.Ty_scal tys)
      st
      (Nir.Scope_internal (get_current_block env))
  in
  let env = add_var env vd in
  {
    env with
      current_ce = CeEnv.add orig_ce ce env.current_ce;
      current_eqs = eq :: env.current_eqs;
  },
  ce

(* {2 Helper functions} *)

let get_ce_name ce =
  let open Clock_types in
  match ce with
  | Ce_condvar cecv -> cecv.cecv_name
  | _ -> invalid_arg "get_ce_name: not a condvar"

(* {2 AST Traversal} *)

let rec clock_exp env base_st ce =
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
    let env, ice = clock_exp env base_st ice in
    let id_ec = Ident.make_internal "ec" in
    let ec_vd =
      make_var_dec
        id_ec
        (Nir.Ty_scal Data_types.Tys_int)
        base_st
        (Nir.Scope_internal (get_current_block env))
    in
    let ec_eq =
      make_eq
        (Const (id_ec, Ast_misc.Cconstr ec))
        base_st
    in
    let env = add_eq (add_var env ec_vd) ec_eq in

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

let rec clock env ck =
  let open Clock_types in
  match ck with
  | St_var _ ->
    env, ck
  | St_on (ck, ce) ->
    let env, ck = clock env ck in
    let env, ce = clock_exp env ck ce in
    env, St_on (ck, ce)

let var_dec vd env =
  let env, ck = clock env vd.v_clock in
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
  let env, bst = clock env eq.eq_base_clock in
  env,
  make_eq
    ~loc:eq.eq_loc
    eqd
    bst

and block env bl =
  let bl_env = enter_block env bl in
  let conv, env, bl_env =
    let do_conv id cv (conv, env, bl_env) =
      let bl_env, int = clock bl_env cv.cv_internal_clock in
      let env, ext = clock env cv.cv_external_clock in
      Ident.Env.add
        id
        { cv with cv_internal_clock = int; cv_external_clock = ext; }
        conv,
      env,
      bl_env
    in
    Ident.Env.fold do_conv bl.b_conv (Ident.Env.empty, env, bl_env)
  in
  let bl_env, body = Utils.mapfold_left equation bl_env bl.b_body in
  fuse_envs env ~nested_env:bl_env,
  make_block
    ~loc:bl.b_loc
    ~conv
    bl.b_id
    (get_eqs env @ body)

let node nd =
  Ident.set_current_ctx nd.n_orig_info#ni_ctx;
  let env = initial_env nd in
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
