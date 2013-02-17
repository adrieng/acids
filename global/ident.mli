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

val reset : unit -> unit

val make_source : string -> t

val make_internal : string -> t

val make_concat : t -> string -> t

val compare : t -> t -> int

val hash : t -> int

val equal : t -> t -> bool

module Env :
  sig
    include Map.S with type key = t
    val of_assoc_list : (key * 'a) list -> 'a t
    val union : 'a t -> 'a t -> 'a t
    val print :
      (Format.formatter -> key * 'a -> unit) ->
      string ->
      Format.formatter ->
      'a t ->
      unit
    val mapfold :
      (key * 'a -> 'b -> (key * 'a) * 'b) ->
      'a t ->
      'b ->
      'a t * 'b
    val mapfold_elems :
      ('a -> 'b -> 'a * 'b) ->
      'a t ->
      'b ->
      'a t * 'b
  end

module Set :
  sig
    include Set.S with type elt = t
    val print : Format.formatter -> t -> unit
  end

val print : Format.formatter -> t -> unit

val to_string : t -> string
