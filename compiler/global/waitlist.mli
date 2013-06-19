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

type id = int

type 'a t

val create : unit -> 'a t

val print : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a t -> unit

val add_constraint : 'a t -> id -> 'a -> unit

val fuse_constraints : 'a t -> id -> id -> unit

val take_constraints : 'a t -> id -> 'a list
