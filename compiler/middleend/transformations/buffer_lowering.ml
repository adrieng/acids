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
open Nir_utils

(** {1 Buffer lowering}

    This pass translates buffers to (lazy/strict) push or pop pairs.
    Each push or pop is to be put inside the proper block.
*)

(** {2 Environments} *)

type env =
  {
    new_eqs_per_block : Ident.t eq list BlockEnv.t;
    local_vars : unit var_dec Ident.Env.t;
    current_blocks : Nir.block_id list;
  }

let initial_env_for_node node =
  {
    new_eqs_per_block = BlockEnv.empty;
    local_vars = node.n_env;
    current_blocks = [];
  }

let current_block env =
  match env.current_blocks with
  | [] -> invalid_arg "current_block: no block entered"
  | bid :: _ -> bid

let add_new_eq_to_block env eq =
  let new_eqs_per_block =
    try BlockEnv.find (current_block env) env.new_eqs_per_block
    with Not_found -> []
  in
  {
    env with
      new_eqs_per_block =
      BlockEnv.add
        (current_block env)
        (eq :: new_eqs_per_block)
        env.new_eqs_per_block;
  }

let enter_block env block_id =
  { env with current_blocks = block_id :: env.current_blocks; }

let leave_current_block env =
  let block_id = current_block env in
  {
    env with
      current_blocks = List.tl env.current_blocks;
      new_eqs_per_block = BlockEnv.remove block_id env.new_eqs_per_block;
  },
  try BlockEnv.find block_id env.new_eqs_per_block
  with Not_found -> []

let add_local_var env vd =
  {
    env with
      local_vars = Ident.Env.add vd.v_name vd env.local_vars;
  }

let local_vars env = env.local_vars

let find_var env x = Ident.Env.find x env.local_vars

let find_var_type env x =
  let vd = find_var env x in
  vd.v_data

(** {2 AST walking} *)

let rec eq env eq =
  match eq.eq_desc with
  | Var _ | Const _ | Call _ | Merge _ | Split _ | Valof _ | Delay _ ->
    env, Some eq
  | Block bl ->
    let env, bl = block env bl in
    env, Some { eq with eq_desc = Block bl; }
  | Buffer (x, bu, y) ->
    let pol = if bu.b_delay then Lazy else Strict in
    (* Regarding buffer size, consider the following clocks.

          (1 1 0 1)
       <: (0 1 1 1)

       Since there is an instantaneous dependence at step 4, the corresponding
       buffer is strict: push has to be done before pop.

       According to the theory in Florence's PhD thesis, the maximal size is one
       since at the end of each instant it holds only one datum. In practice,
       since we generate sequential code, at instant three there is a point when
       we have pushed but not yet poped at which the buffers hold *two* datum.

       For this reason, we use the [real_size] (that disregards the bypass)
       field of the buffer for strict ones, and the [size] one for lazy buffers.
    *)
    let size =
      match pol with
      | Lazy -> bu.b_size
      | Strict -> bu.b_real_size
    in
    let b = Ident.make_internal "buff" in
    let b_vd =
      make_var
        b
        (Ty_buffer (find_var_type env x, size, pol))
        (Clock_types.St_var (Cv_block (Block_id 0)))
        Scope_context
        []
    in
    let env = add_local_var env b_vd in

    let mk_access_eq dir v =
      let base_ck = (find_var env y).v_clock in
      let op =
        {
          a_op = BufferAccess (dir, pol);
          a_stream_inst = [];
        }
      in

      let x_l, y_l =
        match pol, dir with
        | Strict, Push -> [], [v]
        | Strict, Pop -> [v], []
        | Lazy, Push -> [v; b], []
        | Lazy, Pop -> [], [b; v]
      in

      make_eq
        (Call (x_l, op, b :: y_l))
        base_ck
    in

    let push_eq = mk_access_eq Push y in
    let pop_eq = mk_access_eq Pop x in

    add_new_eq_to_block (add_new_eq_to_block env push_eq) pop_eq, None

and block env block =
  let env = enter_block env block.b_id in
  let env, body = Utils.mapfold_left eq env block.b_body in
  let body = Utils.flatten_option_list body in
  let env, new_eqs = leave_current_block env in
  env, { block with b_body = new_eqs @ body; }

let node nd =
  Ident.set_current_ctx nd.n_orig_info#ni_ctx;
  let env = initial_env_for_node nd in
  let env, body = block env nd.n_body in
  { nd with n_body = body; n_env = local_vars env; }

let pass =
  let open Middleend_utils in
  make_transform "buffer_lowering" (map_to_nodes node)
