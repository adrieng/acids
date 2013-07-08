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

type reason = string

type error =
| Constant_inconsistency
| Rate_inconsistency
| Precedence_inconsistency
| Internal_error of (Int.t, Int.t) Tree_word.t Utils.Env.t

exception Could_not_solve of error

let constant_inconsistency () =
  raise (Could_not_solve Constant_inconsistency)

let rate_inconsistency () =
  raise (Could_not_solve Rate_inconsistency)

let precedence_inconsistency () =
  raise (Could_not_solve Precedence_inconsistency)

let internal_error bad_sol =
  raise (Could_not_solve (Internal_error bad_sol))
