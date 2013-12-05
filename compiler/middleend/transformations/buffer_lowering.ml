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
  }

let initial_env_for_node node =
  {
    new_eqs_per_block = BlockEnv.empty;
    local_vars = node.n_env;
  }

let add_new_eq_to_block env block_id eq =
  let new_eqs_per_block =
    try BlockEnv.find block_id env.new_eqs_per_block
    with Not_found -> []
  in
  {
    env with
      new_eqs_per_block =
      BlockEnv.add block_id (eq :: new_eqs_per_block) env.new_eqs_per_block;
  }

let take_eqs_for_block env block_id =
  {
    env with
      new_eqs_per_block = BlockEnv.remove block_id env.new_eqs_per_block;
  },
  BlockEnv.find block_id env.new_eqs_per_block

let local_vars env = env.local_vars

let add_local_var env vd =
  {
    env with
      local_vars = Ident.Env.add vd.v_name vd env.local_vars;
  }

(** {2 AST walking} *)

let node nd =
  ignore (initial_env_for_node nd);
  nd

let pass =
  let open Middleend_utils in
  make_transform "buffer_lowering" (map_to_nodes node)
