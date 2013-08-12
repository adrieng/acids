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

(* {2 Errors} *)

type error =
  | Ill_formed_objective_function
  | Solver_internal_error of int
  | Could_not_parse_solution of string (* file name *)
  | Library_internal_error
  | Could_not_solve

exception Error of error

val print_error : Format.formatter -> error -> unit

(* {2 Building linear systems} *)

type var

type terms = (Int.t * var) list

type linear_system

and linear_constraint =
    {
      lc_terms : terms;
      lc_comp : linear_comp;
      lc_const : Int.t;
    }

and linear_comp = Leq | Lgt | Lge | Llt | Lle

val add_variable : linear_system -> string -> linear_system * var

val negate_terms : terms -> terms

(*
  [make_equality x c y c'] creates the linear constraint x + c = y + c'
*)
val make_equality : terms -> Int.t -> terms -> Int.t -> linear_constraint

val empty_system : linear_system

val add_constraint : linear_system -> linear_constraint -> linear_system

(* Bounds *)

val bound_variable : Int.t * Int.t -> linear_system -> var -> linear_system

val bound_all_variables : linear_system -> Int.t * Int.t -> linear_system

val minimize_all_variables : linear_system -> terms

val set_objective_function
  : linear_system -> terms -> linear_system

(** {2 Printing linear systems} *)

val print_var : Format.formatter -> var -> unit

val print_system : Format.formatter -> linear_system -> unit

(** {2 Solving linear systems} *)

module Env : Utils.MyMap with type key = var

(** ex. gpsol --cpxlp -o %OUT -w %SOL --log %LOG %SYS >/dev/null *)
type solver_command = string

val solve
  : ?command : solver_command
  -> ?verbose:bool
  -> ?profile:bool
  -> linear_system
  -> Int.t Env.t
