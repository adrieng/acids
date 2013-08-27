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

(** {2 Exceptions} *)

type error =
  | Duplicate_variable of string
  | No_objective
  | No_bounds
  | Internal_error of string
  | Internal_solver_error of int

exception Error of error

val print_error : Format.formatter -> error -> unit

(** {2 Systems} *)

type system

val make_system : unit -> system

type var

val make_var : system -> string -> var

(** {2 Terms and constraints} *)

type term

type cstr

val var : var -> term

val const : Int.t -> term

val ( + ) : term -> term -> term

val ( - ) : term -> term -> term

val ( * ) : Int.t -> term -> term

val ( < ) : term -> term -> cstr

val ( <= ) : term -> term -> cstr

val ( > ) : term -> term -> cstr

val ( >= ) : term -> term -> cstr

val ( = ) : term -> term -> cstr

(** {2 System construction functions} *)

val add_constraint : system -> cstr -> system

type objective =
  | Minimize of term
  | Mazimize of term

val minimize_all_variables : system -> objective

val set_objective : system -> objective -> system

val bound_all : system -> Int.t * Int.t -> system

(** {2 System solving} *)

type solution

type solver =
  | Glpk

val solve :
  ?solver:solver ->
  ?verbose : bool ->
  ?profile : bool ->
  system ->
  solution option

val value_of : solution -> var -> Int.t
