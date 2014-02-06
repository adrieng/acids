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

type value =
  | Bool of bool
  | Int of Int.t
  | String of string

type t

val print : Format.formatter -> t -> unit

val make : string -> value -> t

type env

val print_env : Format.formatter -> env -> unit

val empty : env

val is_empty : env -> bool

val add : env -> t -> env

(* may raise Not_found *)
val find : env -> string -> value

type option_name = string
type expected_type = string
type actual_type = string

exception Option_error of option_name * expected_type * actual_type

(* convenience function, may raise Option_error *)
val find_bool : default : bool -> env -> string -> bool

(* convenience function, may raise Option_error *)
val find_int : default : Int.t -> env -> string -> Int.t

(* convenience function, may raise Option_error *)
val find_string : default : string -> env -> string -> string
