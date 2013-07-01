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

module Make(S : sig end) =
struct
  type word = (Int.t, Int.t) Tree_word.t

  type side =
    {
      var : string option;
      const : word list;
    }

  type constr_kind = Equal | Adapt

  type constr =
    {
      lhs : side;
      kind : constr_kind;
      rhs : side;
    }

  type system =
    {
      body : constr list;
    }

  module Solution =
  struct
    type t = word Utils.String_map.t
    let get m x = try Some (Utils.String_map.find x m) with Not_found -> None
  end

  let solve _ = assert false
end
