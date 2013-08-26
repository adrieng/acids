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

(** {2 Type definitions} *)

type state_open
type state_closed
type state_solved

type 'state system

type 'a var

type 'a term

type 'a cstr

(** {2 Constraint construction functions} *)

val var : 'a var -> 'a term

val ( * ) : 'a -> 'a term -> 'a term

val ( + ) : 'a term -> 'a term -> 'a term

val ( < ) : 'a term -> 'a term -> 'a cstr

val ( <= ) : 'a term -> 'a term -> 'a cstr

val ( > ) : 'a term -> 'a term -> 'a cstr

val ( >= ) : 'a term -> 'a term -> 'a cstr

val ( = ) : 'a term -> 'a term -> 'a cstr

(** {2 System construction functions} *)

val make_system : unit -> state_open system

val add_constraint : state_open system -> 'a cstr -> state_open system

val set_objective : state_open system -> 'a term -> state_closed system

(** {2 System solving} *)

val solve : state_closed system -> state_solved system

val value_of : state_solved system -> 'a var -> 'a

