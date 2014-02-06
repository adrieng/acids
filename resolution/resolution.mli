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

type word = (Int.t, Int.t) Tree_word.t

type const = word list

type side =
  {
    var : string option;
    const : const;
  }

type constr =
  {
    loc : Loc.t;
    lhs : side;
    kind : Problem.constr_kind;
    rhs : side;
  }

type system =
  {
    body : constr list;
    options : Resolution_options.env;
  }

val print_system : Format.formatter -> system -> unit

module Solution :
sig
  type t
  val get : t -> string -> word option
  val fold : (string -> word -> 'a -> 'a) -> t -> 'a -> 'a
end

val solve : system -> Solution.t
