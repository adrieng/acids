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

let rec word_of_tree pt =
  match pt with
  | Tree_word.Leaf i -> Pword.singleton i
  | Tree_word.Concat pt_l ->
    let w_l = List.map word_of_tree pt_l in
    List.fold_right Pword.concat w_l Pword.empty
  | Tree_word.Power (pt, i) -> Pword.power (word_of_tree pt) i

let pword_of_tree { Tree_word.u = u; Tree_word.v = v; } =
  Pword.make (word_of_tree u) (word_of_tree v)
