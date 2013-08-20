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

(** {1 Remove split patterns from the language}

        (<x^2 (y^4 z^5)>, k) = e

    ->
        (ps, k) = e
    and (x, y, z) = split ps by 0^2 (1^4 2^5) with 0, 1, 2
*)

module SUB = Acids_utils.MAP_SUB(Acids_causal)
module SUBST = Acids_utils.SUBST(Acids_causal)

open Acids_causal
open Acids_causal_utils

(** {2 Handling patterns} *)

(** {2 Putting it all together} *)

let lower_file
    ctx
    (file :
     <
       interfaces : Interface.env;
       static_nodes : Acids_static.node_def list;
     >
       Acids_causal.file)
    =
  (* let file = apply_to_node_bodies remove_psplit file in *)
  ctx, file

let pass =
  let open Pass_manager in
  P_transform
    (Frontend_utils.make_transform
       ~print_out:Acids_causal.print_file
       "lower_psplit"
       lower_file)
