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
    current_vars = nd.n_env;
  }

let get_current_block env = env.current_block

let enter_block env block =
  { env with current_block = block.b_id; }

let fuse_envs env ~nested_env =
  { env with current_vars = nested_env.current_vars; }

let get_vars env = env.current_vars

let add_var env vd =
  { env with current_vars = Ident.Env.add vd.v_name vd env.current_vars; }

let add_eq env eq = { env with current_eqs = eq :: env.current_eqs; }

let find_ce env ce =
  CeEnv.find ce env.current_ce

let add_ce env orig_ce ck tys id bounds specs eq =
  let open Clock_types in
  let ce =
    Ce_condvar { cecv_name = id; cecv_bounds = bounds; cecv_specs = specs; }
  in
  let vd =
    make_var_dec
      id
      (Nir.Ty_scal tys)
      ck
      (Nir.Scope_internal (get_current_block env))
  in
  let env = add_var env vd in
  {
    env with
      current_ce = CeEnv.add orig_ce ce env.current_ce;
      current_eqs = eq :: env.current_eqs;
  },
  ce

(* {2 Put it all together} *)

let rec clock_exp env base_ck ce =
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
          base_ck
          Data_types.Tys_int (* TODO fix *)
          id
          bounds
          specs
          (
            make_eq
              (Pword (id, pw))
              base_ck
          )
    )
  | Ce_equal (ce, ec) ->
    let env, ce = clock_exp env base_ck ce in
    let id_ec = Ident.make_internal "ec" in
    let ec_vd =
      make_var_dec
        id_ec
        (Nir.Ty_scal Data_types.Tys_int)
        base_ck
        (Nir.Scope_internal (get_current_block env))
    in
    let ec_eq =
      make_eq
        (Const (id_ec, Ast_misc.Cconstr ec))
        base_ck
    in
    let env = add_eq (add_var env ec_vd) ec_eq in

    assert false

let node nd =
  Ident.set_current_ctx nd.n_orig_info#ni_ctx;
  nd

module U = Middleend_utils.Make(Nir_sliced)(Nir_sliced)

let pass =
  U.(make_transform "name_clock_exprs" (map_to_nodes node))
