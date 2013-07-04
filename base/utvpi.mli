(* Copyright (C) Adrien Guatto <adrien.guatto@laposte.net> 2012
 *
 * This file is part of nsched.
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

type t
type var

val make_system : unit -> t * var

val print_system : Format.formatter -> t -> unit

val print_system_dot : out_channel -> t -> unit

val add_variable : t -> string -> var

(** [add_constraint sys x y c] returns the system [sys] with the added
    constraint [y - x >= c]
*)
val add_constraint : t -> var -> var -> Int.t -> unit

exception No_solution

type objective = Maximize | Minimize

val solve_system
  : ?verbose:bool -> ?bound:Int.t -> obj:objective -> t -> Int.t Utils.Env.t

