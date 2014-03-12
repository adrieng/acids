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
open Nir_sliced

(** {1 Buffer lowering}

    This pass translates buffers to (lazy/strict) push or pop pairs.
    Each push or pop is to be put inside the proper block.
*)

(** {2 Environments} *)

type env =
  {
    current_block : block_id;
    replacements : Ident.t Ident.Env.t;
    local_vars : var_dec Ident.Env.t;
    eqs_for_current_block : eq list;
  }

let initial_env_for_node node =
  {
    current_block = Block_id 0;
    replacements = Ident.Env.empty;
    local_vars = node.n_env;
    eqs_for_current_block = [];
  }

let get_parent_block env = env.current_block

let get_locals env = env.local_vars

let get_current_eqs env = env.eqs_for_current_block

let enter_new_block env block =
  { env with eqs_for_current_block = []; current_block = block.b_id; }

let add_eq env eq =
  { env with eqs_for_current_block = eq :: env.eqs_for_current_block; }

let find_var env x =
  Ident.Env.find x env.local_vars

let find_var_type env x = (find_var env x).v_data

let add_local_var env vd =
  { env with local_vars = Ident.Env.add vd.v_name vd env.local_vars; }

let add_replacement env x y =
  { env with replacements = Ident.Env.add x y env.replacements; }

let add_copy env ck x =
  let x_vd = find_var env x in
  let y = Ident.make_suffix x "_blint" in
  let y_vd =
    make_var_dec
      ~annots:x_vd.v_annots
      y
      x_vd.v_data
      ck
      (Scope_internal (get_parent_block env))
  in
  add_local_var
    { env with replacements = Ident.Env.add x y env.replacements; }
    y_vd,
  y

let substitute env x = try Ident.Env.find x env.replacements with Not_found -> x

(** {2 AST walking} *)

let mk_access_eq env b pol dir v =
  let base_ck = (find_var env v).v_clock in
  let op =
    {
      c_op = BufferAccess (dir, pol);
      c_stream_inst = [];
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

let make_buffer env ?(scope = Scope_context) ty size pol =
  let b = Ident.make_internal "buff" in
  let b_vd =
    make_var_dec
      b
      (Ty_buffer (ty, size, pol))
      (Clock_types.St_var (Info.Cv_base))
      scope
  in
  add_local_var env b_vd, b

let rec equation env eq =
  match eq.eq_desc with
  | Var (x, y) ->
    add_eq
      env
      (make_eq
         ~loc:eq.eq_loc
         (Var (substitute env x, substitute env y))
         eq.eq_base_clock)

  | Const _ | Pword _ | Call _ | Merge _ | Split _
  | Delay _ ->
    add_eq env eq

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
    let env, b = make_buffer env (find_var_type env x) size pol in

    let push_eq = mk_access_eq env b pol Push y in
    let pop_eq = mk_access_eq env b pol Pop x in

    add_eq (add_eq env push_eq) pop_eq

  | Block bl ->
    let env, bl = block env bl in
    add_eq
      env
      (make_eq ~loc:eq.eq_loc (Block bl) eq.eq_base_clock)

and block env block =
  let env' = enter_new_block env block in

  let add_push_and_pop_for_conv x cv (env, env') =
    let size = Clock_types.max_burst_stream_type cv.cv_external_clock in

    let env, b =
      make_buffer
        env
        ~scope:(Scope_internal (get_parent_block env))
        (find_var_type env x)
        size
        Strict
    in

    let env, y = add_copy env cv.cv_internal_clock x in

    match cv.cv_direction with
    | Push ->
      (* x is being defined inside the block. *)
      let push_eq = mk_access_eq env b Strict Push y in
      let pop_eq = mk_access_eq env b Strict Pop x in
      add_eq env pop_eq, add_eq env' push_eq

    | Pop ->
      (* x is being used inside the block. *)
      let push_eq = mk_access_eq env b Strict Push x in
      let pop_eq = mk_access_eq env b Strict Pop y in
      add_eq env push_eq, add_eq env' pop_eq
  in

  let env, env' =
    Ident.Env.fold add_push_and_pop_for_conv block.b_conv (env, env')
  in

  let block =
    let env' = List.fold_left equation env' block.b_body in
    make_block
      ~loc:block.b_loc
      ~conv:block.b_conv
      block.b_id
      (get_current_eqs env')
  in
  env, block

let node nd =
  Ident.set_current_ctx nd.n_orig_info#ni_ctx;
  let env = initial_env_for_node nd in
  let env, body = block env nd.n_body in
  make_node
    ~loc:nd.n_loc
    nd.n_name
    nd.n_orig_info
    ~input:nd.n_input
    ~output:nd.n_output
    ~env:(get_locals env)
    ~body

module U = Middleend_utils.Make(Nir_sliced)(Nir_sliced)

let pass = U.make_transform "buffer_lowering" (U.map_to_nodes node)
