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

open Acids_preclock

(** {2 Values and related functions} *)

type value =
  | Const of Ast_misc.const
  | Tuple of value list

(** {2 Environments} *)

type env =
  {
    intf_env : Interface.env;
    current_nodes : node_def Names.ShortEnv.t;
    idents : value Ident.Env.t;
    seen : Ident.Set.t;
  }

(** {2 Static evaluation itself} *)

let eval_file ctx (file : < interfaces : Interface.env > Acids_preclock.file) =
  ctx, file

(** {2 Putting it all together} *)

let eval =
  let open Pass_manager in
  P_transform
    (Frontend_utils.make_transform
       ~print_out:Acids_preclock.print_file
       "static_eval"
       eval_file)
