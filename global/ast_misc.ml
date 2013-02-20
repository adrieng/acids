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

type 'a var_dec =
    {
      v_ident : Ident.t;
      v_info : 'a;
      v_loc : Loc.t;
    }

type const =
  | Cbool of bool
  | Cint of Int.t
  | Cfloat of float

type ('a, 'b) power_tree =
  | Leaf of 'a
  | Concat of ('a, 'b) power_tree list
  | Power of ('a, 'b) power_tree * 'b

module MakeVar =
  functor
    (S :
      sig
        type ('a, 'b) t
        val print :
          (Format.formatter -> 'a -> unit) ->
          Format.formatter ->
          ('a, 'b) t ->
          unit
      end) ->
struct
  type 'b t =
    {
      v_id : int;
      mutable v_link : ('b t, 'b) S.t;
    }

  let rec print_var fmt (v : 'b t) =
    Format.fprintf fmt "%a%d"
      (S.print print_var) v.v_link
      v.v_id
end
