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

type word

val print_word : Format.formatter -> word -> unit

val empty : word

val singleton : Int.t -> word

val concat : word -> word -> word

val power : word -> Int.t -> word

val size : word -> Int.t

val nbones : word -> Int.t

val word_of_iof :
  max_burst:Int.t -> size:Int.t -> nbones:Int.t -> (Int.t * Int.t) list -> word

type pword =
  private
    {
      u : word;
      v : word;
    }

val make : word -> word -> pword

val print_pword : Format.formatter -> pword -> unit

val ones : pword -> Int.t -> Int.t

val iof : pword -> Int.t -> Int.t

val lengthen_prefix : pword -> Int.t -> pword

val repeat_period : pword -> Int.t -> pword

val on : pword -> pword -> pword

val rate : pword -> Rat.t

val equal : pword -> pword -> bool

val adapt : pword -> pword -> bool

val to_tree_pword : pword -> (Int.t, Int.t) Tree_word.t
