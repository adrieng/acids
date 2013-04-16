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

(** {2 Scoping pass}

    The scoping pass is responsible for converting plain strings from the parsed
    AST to identifiers, guaranteed to be unique. It also loads relevant modules,
    that is modules that either appear in an "import Modname" statement, or that
    are explicitely refered to through a node call "Modname.nodename (x, y)".
*)

let find_module_with_node mod_env ln = assert false

let scope_longname local_nodes ln mod_env =
  let open Names in
  match ln.modn with
  | LocalModule ->
    (* If the node exists in the local module, this is a local node call.
       Otherwise we look it up in the imported modules. *)
    if ShortEnv.mem ln.shortn local_nodes
    then { modn = LocalModule; shortn = ln.shortn; }
    else { modn = Module (find_module_with_node mod_env ln); shortn = ln.shortn; }
  | Module modn ->
    assert false

let scope_file ctx (file : unit Acids_parsetree.file) =
  ctx, (file : unit Acids_parsetree.file)

let scope =
  let open Pass_manager in
  P_transform
    (Frontend_utils.make_transform
       ~print_out:Acids_parsetree.print_file
       "scoping"
       scope_file)
