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

type word

val print_word : Format.formatter -> word -> unit

val empty : word

val singleton : Int.t -> word

val concat : word -> word -> word

val power : word -> Int.t -> word

val size : word -> Int.t

val nbones : word -> Int.t

val make_word_alap :
  max_burst:Int.t -> size:Int.t -> nbones:Int.t -> (Int.t * Int.t) list -> word

val word_compare : word -> word -> int

val to_tree_word : word -> (Int.t, Int.t) Tree_word.power_tree

type pword =
  private
    {
      u : word;
      v : word;
    }

val make : word -> word -> pword

val unit_pword : pword

val is_constant_pword : pword -> bool

val is_unit_pword : pword -> bool

val print_pword : Format.formatter -> pword -> unit

val ones : pword -> Int.t -> Int.t

val iof : pword -> Int.t -> Int.t

val lengthen_prefix : pword -> Int.t -> pword

val repeat_period : pword -> Int.t -> pword

val on : pword -> pword -> pword

val rate : pword -> Rat.t

val equal : pword -> pword -> bool

val adapt : ?delay : Int.t -> pword -> pword -> bool

val to_tree_pword : pword -> (Int.t, Int.t) Tree_word.t

val simplify : pword -> pword

val bounds : pword -> Interval.t

(* When consider_bypass is true, buffer_size computes the size of a buffer with
   a true "bypass" mechanism, that is a buffer that at a given tick does not
   need to store its whole input burst before producing its output burst.

   It is false by default.

   Examples:

   buffer_size ~consider_bypass:false (1 1 0) (0 1 1) = 2

   buffer_size ~consider_bypass:true (1 1 0) (0 1 1) = 1

   buffer_size ~consider_bypass:false (2 0) (1 1) = 2

   buffer_size ~consider_bypass:true (2 0) (1 1) = 1
*)
val buffer_size : ?consider_bypass : bool -> pword -> pword -> Int.t

(** {2 Precomputations} *)

type iof_cached

val cache_iof : pword -> iof_cached

val iof_cached : iof_cached -> Int.t -> Int.t

type ones_cached

val cache_ones : pword -> ones_cached

val ones_cached : ones_cached -> Int.t -> Int.t

val pword_compare : pword -> pword -> int
