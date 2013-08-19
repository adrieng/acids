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

(** {1 Remove tuple from the language}

    This pass assumes that the input is in three-addess form and have no
    if/then/else or fbys, and thus must come after Lower_constructs and
    Lower_subexps.
*)

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
  ctx, file

let pass =
  let open Pass_manager in
  P_transform
    (Frontend_utils.make_transform
       ~print_out:Acids_causal.print_file
       "lower_tuples"
       lower_file)
