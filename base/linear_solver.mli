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

type terms = (Int.t * string) list

type linear_system

and linear_constraint =
    {
      lc_terms : terms;
      lc_comp : linear_comp;
      lc_const : Int.t;
    }

and linear_comp = Leq | Lgt | Lge | Llt | Lle

val negate_terms : terms -> terms

(*
  [make_equality x c y c'] creates the linear constraint x + c = y + c'
*)
val make_equality : terms -> Int.t -> terms -> Int.t -> linear_constraint

val empty_system : linear_system

val add_linear_constraint : linear_system -> linear_constraint -> linear_system

(* Bounds *)

val bound_variable : Int.t * Int.t -> linear_system -> string -> linear_system

val bound_all_variables : linear_system -> linear_comp -> Int.t -> linear_system

val minimize_all_variables : linear_system -> terms

val set_objective_function
  : linear_system -> terms -> linear_system

val print_linear_system : Format.formatter -> linear_system -> unit

exception Ill_formed_objective_function
exception Solver_internal_error of int
exception Library_internal_error
exception Could_not_solve

val solve_linear_system
  : ?verbose:bool -> linear_system -> Int.t Utils.Env.t
