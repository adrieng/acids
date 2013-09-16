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

(** {1 Add boxing/unboxing functions around polymorphic function parameters}

    f : int * 'x -> 'x * bool * 'x

      (x, y, z) = f (4, k)

    ->

      bx1 = box k
      (bx2, y, bx3) = f (4, bx1)
      x = unbox bx2
      z = unbox bx3

    Applies after lower_subexps since it expects code to be in flat form.
*)

module SUB = Acids_utils.MAP_SUB(Acids_causal)

open Acids_causal
open Acids_causal_utils

let poly_var_prefix = "bx"

let node_def input body =
  input, body

(** {2 Putting it all together} *)

let pass = Lowering_utils.make_transform_by_node node_def "lower_psplit"
