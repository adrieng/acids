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

type error =
  | Non_causal of Ident.t
  | Unimplemented_builtin of Loc.t * Names.longname

exception Error of error

type value = desc Lazy.t

and desc =
  | Const of Ast_misc.const
  | Tuple of value list

type env

val make_env : Interface.env -> env

val add_node_def : env -> Acids_const.node_def -> env

val add_local_defs : env -> Acids_const.block -> env

val add_const : env -> Names.shortname -> desc -> env

val add_pword : env -> Names.shortname -> Acids_const.const_word -> env

val eval_exp : env -> Acids_const.exp -> desc

val eval_const_exp : env -> Acids_const.const_exp -> desc

val eval_var : env -> Ident.t -> desc
