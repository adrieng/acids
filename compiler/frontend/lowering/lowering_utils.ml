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

type annotated_file =
  <
    interfaces : Interface.env;
    static_nodes : Acids_static.node_def list;
  > Acids_causal.file

let make_transform_by_file (do_file : annotated_file -> annotated_file) name =
  let open Pass_manager in
  P_transform
    (Frontend_utils.make_transform
       ~print_out:Acids_causal.print_file
       name
       (fun ctx file -> ctx, do_file file))

let make_transform_by_node do_node name =
  make_transform_by_file (Acids_causal_utils.apply_to_node_defs do_node) name
