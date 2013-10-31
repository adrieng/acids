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

(** {2 Environments} *)

type env =
  {
    intf_env : Interface.env;
    local_clock_sigs : Clock_types.clock_sig Names.ShortEnv.t;
    mutable current_block_count : int;
    mutable var_decs : unit var_dec Ident.Env.t;
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
    current_block_count = 0;
    var_decs = Ident.Env.empty;
  }

let find_node_sig env ln =
  let open Names in
  match ln.modn with
  | LocalModule ->
    ShortEnv.find ln.shortn env.local_clock_sigs
  | Module modn ->
    let intf = ShortEnv.find modn env.intf_env in
    Interface.(clock_signature_of_node_item (find_node intf ln.shortn))

let enter_node env nd =
  env.var_decs <- nd.n_env;
  env.current_block_count <- nd.n_block_count

let get_current_block_count env = env.current_block_count

let fresh_block_id env =
  let next = env.current_block_count in
  env.current_block_count <- env.current_block_count + 1;
  Block_id next

let get_var_decs env = env.var_decs

let add_var_dec env vd =
  env.var_decs <- Ident.Env.add vd.v_name vd env.var_decs

let find_var_dec env id = Ident.Env.find id env.var_decs

(** {2 AST traversal} *)

let form_block env base_clock mk_desc x_l x_mk_ck_l y_l y_mk_ck_l =
  let bid = fresh_block_id env in
  let bck = Ck_block_base bid in

  let refresh_variable eqs x mk_ck =
    let x_vd = find_var_dec env x in
    let x' = Ident.make_prefix "blk_" x in
    let x'_ck = mk_ck bck in
    let x'_vd = { x_vd with v_name = x'; v_clock = x'_ck; } in
    add_var_dec env x'_vd;
    Nir_utils.make_eq (Var (x', x)) bck :: eqs, x'
  in

  let eqs, x'_l = Utils.mapfold_left_2 refresh_variable [] x_l x_mk_ck_l in
  let eqs, y'_l = Utils.mapfold_left_2 refresh_variable eqs y_l y_mk_ck_l in
  let block =
    {
      b_id = bid;
      b_body = Nir_utils.make_eq (mk_desc x'_l y'_l) bck :: eqs;
      b_loc = Loc.dummy;
    }
  in
  Nir_utils.make_eq (Block block) base_clock

let equation env eq =
  match eq.eq_desc with
  | Var _ | Buffer _ ->
    (* TODO: optimize buffer *)
    eq

  | Const (x, c) ->
    let mk_desc x_l _ =
      let x = Utils.assert1 x_l in
      Const (x, c)
    in
    form_block env eq.eq_base_clock mk_desc [x] [fun ck -> ck] [] []

  | Call _ ->
    assert false (* TODO *)

  | Merge (x, ce, c_l) ->
    let ec_l, y_l = List.split c_l in
    let mk_desc x_l y_l =
      let x = Utils.assert1 x_l in
      Merge (x, ce, List.combine ec_l y_l)
    in
    form_block env eq.eq_base_clock mk_desc [x] [fun ck -> ck] y_l (assert false)

  | _ ->
    assert false

let block env block =
  assert (let Block_id x = block.b_id in x < get_current_block_count env);
  let body = List.map (equation env) block.b_body in
  { block with b_body = body; }

let node env nd =
  Ident.set_current_ctx nd.n_orig_info#ni_ctx;
  enter_node env nd;
  let block = block env nd.n_body in
  {
    nd with
      n_body = block;
      n_block_count = get_current_block_count env;
      n_env = get_var_decs env;
  }

let tr ctx file =
  let env = initial_env file in
  Middleend_utils.map_to_nodes (node env) ctx file

let pass =
  Middleend_utils.(make_transform "block_formation" tr)
