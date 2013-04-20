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

(** {1 Scoping pass}

    The scoping pass is responsible for converting plain strings from the parsed
    AST to identifiers, guaranteed to be unique. It also loads relevant modules,
    that is modules that either appear in an "import Modname" statement, or that
    are explicitely refered to through a node call "Modname.nodename (x, y)".

    Scoping rules for node names:

    - A node shortname that is not not found in the current module is looked up
    in the imported modules, in the reverse (text) order.

    - A node full name is looked up in the corresponding module. It is loaded if
    needed.

    - Module files are searched in Compiler.search_path, in order.
*)

(** {2 Error handling} *)

type error =
  | Unknown_node of Names.shortname * Loc.t
  | Node_not_found of Names.modname * Names.shortname * Loc.t
  | Unbound_var of string * Loc.t

exception Scoping_error of error

let print_error fmt err =
  match err with
  | Unknown_node (shortn, l) ->
    Format.fprintf fmt "%aUnknown node %a"
      Loc.print l
      Names.print_shortname shortn
  | Node_not_found (modn, shortn, l) ->
    Format.fprintf fmt "%aNode %a not found in module %a"
      Loc.print l
      Names.print_shortname shortn
      Names.print_modname modn
  | Unbound_var (v, l) ->
    Format.fprintf fmt "%aUnknown identifier %s" Loc.print l v

let unknown_node shortn loc = raise (Scoping_error (Unknown_node (shortn, loc)))

let node_not_found modn shortn loc =
  raise (Scoping_error (Node_not_found (modn, shortn, loc)))

let unbound_var v loc = raise (Scoping_error (Unbound_var (v, loc)))

(** {2 Scoping function} *)

(** Find which of the imported module (if any) provides the corresponding node
    name.

    @param imported_mods list of explicitely imported modules, in reverse order
    @param intf_env an environment mapping module names to Interface.t
    @param shortn the node name to look-up
    @returns module name defining shortn
*)
let find_module_with_node imported_mods intf_env shortn loc =
  let mod_has_node modn =
    let intf = Names.ShortEnv.find modn intf_env in
    Names.ShortEnv.mem modn intf.Interface.i_body
  in
  try List.find mod_has_node imported_mods
  with Not_found -> unknown_node shortn loc

let check_module_with_node intf_env modn shortn loc =
  let intf, intf_env =
    try Names.ShortEnv.find modn intf_env, intf_env
    with Not_found ->
      let intf = Interface.load_interface_from_module_name modn in
      intf, Names.ShortEnv.add modn intf intf_env
  in
  if not (Names.ShortEnv.mem shortn intf.Interface.i_body)
  then node_not_found modn shortn loc;
  intf_env

let scope_longname local_nodes imported_mods intf_env ln loc =
  let open Names in
  match ln.modn with
  | LocalModule ->
    (* If the node exists in the local module, this is a local node call.
       Otherwise we look it up in the imported modules. *)
    if ShortEnv.mem ln.shortn local_nodes
    then ln, intf_env
    else
      let modn =
        find_module_with_node imported_mods intf_env ln.shortn loc
      in
      { ln with modn = Module modn; }, intf_env
  | Module modn ->
    let intf_env = check_module_with_node intf_env modn ln.shortn loc in
    ln, intf_env

let add_var id_env v =
  let id = Ident.make_source v in
  id, Utils.String_map.add v id id_env

let find_var id_env v loc =
  try Utils.String_map.find v id_env
  with Not_found -> unbound_var v loc

(** {2 AST traversal} *)

open Acids_parsetree

let rec scope_clock_annot imported_mods cka acc =
  match cka with
  | Ca_var i ->
    Acids_scoped.Ca_var i, acc
  | Ca_on (cka, ce) ->
    let ce, acc = scope_clock_exp imported_mods ce acc in
    let cka, acc = scope_clock_annot imported_mods cka acc in
    Acids_scoped.Ca_on (cka, ce), acc

and scope_clock_exp imported_mods ce ((local_nodes, intf_env, id_env) as acc) =
  let ced, acc =
    match ce.ce_desc with
    | Ce_var v ->
      let id = find_var id_env v ce.ce_loc in
      Acids_scoped.Ce_var id, acc
    | Ce_pword upw ->
      let pw, acc =
        Ast_misc.mapfold_upword
          (scope_exp imported_mods)
          (scope_exp imported_mods)
          upw acc
      in
      Acids_scoped.Ce_pword pw, acc
    | Ce_equal (ce, e) ->
      let ce, acc = scope_clock_exp imported_mods ce acc in
      let e, acc = scope_exp imported_mods e acc in
      Acids_scoped.Ce_equal (ce, e), acc
    | Ce_iter ce ->
      let ce, acc = scope_clock_exp imported_mods ce acc in
      Acids_scoped.Ce_iter ce, acc
  in
  {
    Acids_scoped.ce_desc = ced;
    Acids_scoped.ce_loc = ce.ce_loc;
    Acids_scoped.ce_info = ();
  },
  acc

and scope_exp imported_mods e acc = assert false

and scope_pattern imported_mods p ((local_nodes, intf_env, id_env) as acc) =
  let pd, acc =
    match p.p_desc with
    | P_var v ->
      let id, id_env = add_var id_env v in
      Acids_scoped.P_var id, (local_nodes, intf_env, id_env)
    | P_tuple p_l ->
      let p_l, acc = Utils.mapfold (scope_pattern imported_mods) p_l acc in
      Acids_scoped.P_tuple p_l, acc
    | P_clock_annot (p, cka) ->
      let cka, acc = scope_clock_annot imported_mods cka acc in
      let p, acc = scope_pattern imported_mods p acc in
      Acids_scoped.P_clock_annot (p, cka), acc
    | P_split upw ->
      let p_l, acc =
        Ast_misc.mapfold_upword
          (scope_pattern imported_mods)
          (scope_exp imported_mods)
          upw acc
      in
      Acids_scoped.P_split p_l, acc
  in
  {
    Acids_scoped.p_desc = pd;
    Acids_scoped.p_loc = p.p_loc;
    Acids_scoped.p_info = ();
  },
  acc

let scope_file ctx (file : unit Acids_parsetree.file) =
  ctx, (file : unit Acids_parsetree.file)

(** {2 Putting it all together} *)

let scope =
  let open Pass_manager in
  P_transform
    (Frontend_utils.make_transform
       ~print_out:Acids_parsetree.print_file
       "scoping"
       scope_file)
