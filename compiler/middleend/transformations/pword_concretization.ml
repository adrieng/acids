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

(* The goal of this pass is to remove the Ce_pword constructors from clock
   expressions (Nir module) and stream types (Clock_types module). Each one is
   replaced with a fresh name properly annotated with the corresponding Spec.
*)

module PwordEnv =
  Utils.MakeMap(
    struct
      type t = Nir.clock * Pword.pword
      let compare ((ck1 : Nir.clock), p1) (ck2, p2) =
        let i = Nir_utils.clock_compare ck1 ck2 in
        Utils.compare_both i (fun () -> Pword.pword_compare p1 p2)
    end
  )

let tr ctx file =
  Middleend_utils.map_to_nodes (fun x -> x) ctx file

let pass =
  Middleend_utils.(make_transform "pword_concretization" tr)
