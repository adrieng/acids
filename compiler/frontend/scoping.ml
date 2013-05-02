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
  | Unknown_constr of Names.shortname * Loc.t
  | Node_not_found of Names.modname * Names.shortname * Loc.t
  | Constr_not_found of Names.modname * Names.shortname * Loc.t
  | Unbound_var of string * Loc.t
  | Multiple_binding_pattern of string * Loc.t
  | Multiple_binding_block of string * Loc.t
  | Duplicate_node of Names.shortname * Loc.t
  | Duplicate_constr of Names.shortname * Loc.t
  | Duplicate_type of Names.shortname * Loc.t

exception Scoping_error of error

let print_error fmt err =
  match err with
  | Unknown_node (shortn, l) ->
    Format.fprintf fmt "%aUnknown node %a"
      Loc.print l
      Names.print_shortname shortn
  | Unknown_constr (shortn, l) ->
    Format.fprintf fmt "%aUnknown constructor %a"
      Loc.print l
      Names.print_shortname shortn
  | Node_not_found (modn, shortn, l) ->
    Format.fprintf fmt "%aNode %a not found in module %a"
      Loc.print l
      Names.print_shortname shortn
      Names.print_modname modn
  | Constr_not_found (modn, constrn, l) ->
    Format.fprintf fmt "%aConstructor %a not found in module %a"
      Loc.print l
      Names.print_shortname constrn
      Names.print_modname modn
  | Unbound_var (v, l) ->
    Format.fprintf fmt "%aUnknown identifier %s" Loc.print l v
  | Multiple_binding_pattern (s, l) ->
    Format.fprintf fmt "%a%s is bound several times in this pattern"
      Loc.print l
      s
  | Multiple_binding_block (s, l) ->
    Format.fprintf fmt "%a%s is bound several times in this block"
      Loc.print l
      s
  | Duplicate_node (shortn, l) ->
    Format.fprintf fmt "%a%a is declared several times in this module"
      Loc.print l
      Names.print_shortname shortn
  | Duplicate_constr (constrn, l) ->
    Format.fprintf fmt
      "%aConstructor %a has already been declared in this module"
      Loc.print l
      Names.print_shortname constrn
  | Duplicate_type (typen, l) ->
    Format.fprintf fmt "%aType %a is defined several times in this module"
      Loc.print l
      Names.print_shortname typen

let unknown_node shortn loc = raise (Scoping_error (Unknown_node (shortn, loc)))

let unknown_constr shortn loc =
  raise (Scoping_error (Unknown_constr (shortn, loc)))

let node_not_found modn shortn loc =
  raise (Scoping_error (Node_not_found (modn, shortn, loc)))

let constr_not_found modn shortn loc =
  raise (Scoping_error (Constr_not_found (modn, shortn, loc)))

let unbound_var v loc = raise (Scoping_error (Unbound_var (v, loc)))

let multiple_binding_pattern shortn loc =
  raise (Scoping_error (Multiple_binding_pattern (shortn, loc)))

let multiple_binding_block shortn loc =
  raise (Scoping_error (Multiple_binding_block (shortn, loc)))

let duplicate_node shortn loc =
  raise (Scoping_error (Duplicate_node (shortn, loc)))

let duplicate_constr constrn loc =
  raise (Scoping_error (Duplicate_constr (constrn, loc)))

let duplicate_type typen loc =
  raise (Scoping_error (Duplicate_type (typen, loc)))

(** {2 Scoping function} *)

(** Find which of the imported modules (if any) provides the corresponding
    name. This function is used for finding both node names and
    type constructors.

    @param access a function for specifying where to look in the interface
    @param error a function to call in case the constructor is not found
    @param imported_mods list of explicitely imported modules, in reverse order
    @param intf_env an environment mapping module names to Interface.t
    @param shortn the node or constructor name to look-up
    @returns module name defining shortn
*)
let find_module_with_shortname access error imported_mods intf_env shortn loc =
  let mod_has_node modn =
    let intf = Names.ShortEnv.find modn intf_env in
    Names.ShortEnv.mem modn (access intf)
  in
  try List.find mod_has_node imported_mods
  with Not_found -> error shortn loc

let find_module_with_node =
  find_module_with_shortname (fun i -> i.Interface.i_nodes) unknown_node

let find_module_with_constr =
  find_module_with_shortname (fun i -> i.Interface.i_constrs) unknown_constr

(** Check if the given module name holds the item designated by shortn.
    Works for both node and constructor names. This function loads module as
    needed.

    @param access a function for specifying where to look in the interface
    @param error a function to call in case the constructor is not found
    @param intf_env an environment mapping module names to Interface.t
    @param modn name of the module to check
    @param shortn the node or constructor name to look-up
    @returns potentially updated [intf_env]
*)
let check_module_with_name access error intf_env modn shortn loc =
  let intf, intf_env =
    try Names.ShortEnv.find modn intf_env, intf_env
    with Not_found ->
      let intf = Interface.load_interface_from_module_name modn in
      intf, Names.ShortEnv.add modn intf intf_env
  in
  if not (Names.ShortEnv.mem shortn (access intf))
  then error modn shortn loc;
  intf_env

let check_module_with_node =
  check_module_with_name (fun i -> i.Interface.i_nodes) node_not_found

let check_module_with_constr =
  check_module_with_name (fun i -> i.Interface.i_constrs) constr_not_found

(** Scope a name in the proper name-space (nodes or constructors) *)
let scope_longname find check locals imported_mods intf_env ln loc =
  let open Names in
  match ln.modn with
  | LocalModule ->
    (* We check in [locals] whether the name is indeed known
       at this point. Otherwise we look it up in the imported
       modules. *)
    if ShortSet.mem ln.shortn locals
    then ln, intf_env (* ln is indeed local *)
    else
      let modn = find imported_mods intf_env ln.shortn loc in
      { ln with modn = Module modn; }, intf_env
  | Module modn ->
    (* Check that the module indeed holds the name (loading it if needed). *)
    ln, check intf_env modn ln.shortn loc

let scope_node = scope_longname find_module_with_node check_module_with_node

let scope_constr =
  scope_longname find_module_with_constr check_module_with_constr

let add_var id_env v =
  let id = Ident.make_source v in
  id, Utils.String_map.add v id id_env

let find_var id_env v loc =
  try Utils.String_map.find v id_env
  with Not_found -> unbound_var v loc

(** {2 AST traversal} *)

open Acids_parsetree

(** {3 Multiple binding checks} *)

let check_pattern block_loc block_env p =
  let pat_loc = p.p_loc in
  let rec walk pat_env p =
    match p.p_desc with
    | P_var s ->
        if Utils.String_set.mem s pat_env
        then multiple_binding_pattern s pat_loc;
        if Utils.String_set.mem s block_env
        then multiple_binding_block s block_loc;
        Utils.String_set.add s pat_env
    | P_tuple p_l -> List.fold_left walk pat_env p_l
    | P_clock_annot (p, _) -> walk pat_env p
    | P_split pw ->
        let rec walk_ptree pat_env pt =
          match pt with
          | Ast_misc.Leaf p -> walk pat_env p
          | Ast_misc.Concat p_l -> List.fold_left walk_ptree pat_env p_l
          | Ast_misc.Power (p, _) -> walk_ptree pat_env p
        in
        walk_ptree (walk_ptree pat_env pw.Ast_misc.u) pw.Ast_misc.v
  in
  let pat_env = walk Utils.String_set.empty p in
  Utils.String_set.union block_env pat_env

(** The following function checks both multiple bindings spanning a pattern
    or a block. *)
let check_block block =
  let walk_eq block_env eq = check_pattern block.b_loc block_env eq.eq_lhs in
  ignore (List.fold_left walk_eq Utils.String_set.empty block.b_body)

(** Stand-alone checker for patterns (used for inputs of nodes defs) *)
let check_pattern p = ignore (check_pattern Loc.dummy Utils.String_set.empty p)

let check_node_name local_nodes nn loc =
  if Names.ShortSet.mem nn local_nodes then duplicate_node nn loc

let check_type_constr local_constrs cn loc =
  if Names.ShortSet.mem cn local_constrs then duplicate_constr cn loc

let check_type_name local_types tn loc =
  if Names.ShortSet.mem tn local_types then duplicate_type tn loc

(** {3 Scoping} *)

let rec scope_econstr local_constrs imported_mods loc ec acc =
  match ec with
  | Ast_misc.Ec_int _ | Ast_misc.Ec_bool _ -> ec, acc
  | Ast_misc.Ec_constr ln ->
    let (intf_env, id_env) = acc in
    let ln, intf_env =
      scope_constr local_constrs imported_mods intf_env ln loc
    in
    Ast_misc.Ec_constr ln, (intf_env, id_env)

and scope_const local_constrs imported_mods loc c acc =
  match c with
  | Ast_misc.Cconstr ec ->
    let ec, acc = scope_econstr local_constrs imported_mods loc ec acc in
    Ast_misc.Cconstr ec, acc
  | Ast_misc.Cfloat _ | Ast_misc.Cword _ -> c, acc

and scope_clock_annot local_nodes local_constrs imported_mods cka acc =
  let scope_clock_exp =
    scope_clock_exp local_nodes local_constrs imported_mods
  in
  let scope_clock_annot =
    scope_clock_annot local_nodes local_constrs imported_mods
  in
  match cka with
  | Ca_var i ->
    Acids_scoped.Ca_var i, acc
  | Ca_on (cka, ce) ->
    let ce, acc = scope_clock_exp ce acc in
    let cka, acc = scope_clock_annot cka acc in
    Acids_scoped.Ca_on (cka, ce), acc

and scope_clock_exp
    local_nodes local_constrs imported_mods ce ((_, id_env) as acc) =
  let scope_exp = scope_exp local_nodes local_constrs imported_mods in
  let scope_clock_exp =
    scope_clock_exp local_nodes local_constrs imported_mods
  in
  let ced, acc =
    match ce.ce_desc with
    | Ce_var v ->
      let id = find_var id_env v ce.ce_loc in
      Acids_scoped.Ce_var id, acc
    | Ce_pword upw ->
      let pw, acc = Ast_misc.mapfold_upword scope_exp scope_exp upw acc in
      Acids_scoped.Ce_pword pw, acc
    | Ce_equal (ce, e) ->
      let ce, acc = scope_clock_exp ce acc in
      let e, acc = scope_exp e acc in
      Acids_scoped.Ce_equal (ce, e), acc
    | Ce_iter ce ->
      let ce, acc = scope_clock_exp ce acc in
      Acids_scoped.Ce_iter ce, acc
  in
  {
    Acids_scoped.ce_desc = ced;
    Acids_scoped.ce_loc = ce.ce_loc;
    Acids_scoped.ce_info = ce.ce_info;
  },
  acc

and scope_exp
    local_nodes local_constrs imported_mods e ((intf_env, id_env) as acc) =
  let scope_exp = scope_exp local_nodes local_constrs imported_mods in
  let scope_clock_exp =
    scope_clock_exp local_nodes local_constrs imported_mods
  in
  let ed, acc =
    match e.e_desc with
    | E_var v ->
      let id = find_var id_env v e.e_loc in
      Acids_scoped.E_var id, (intf_env, id_env)
    | E_const c ->
      let c, acc = scope_const local_constrs imported_mods e.e_loc c acc in
      Acids_scoped.E_const c, acc
    | E_fst e ->
      let e, acc = scope_exp e acc in
      Acids_scoped.E_fst e, acc
    | E_snd e ->
      let e, acc = scope_exp e acc in
      Acids_scoped.E_snd e, acc
    | E_tuple e_l ->
      let e_l, acc = Utils.mapfold scope_exp e_l acc in
      Acids_scoped.E_tuple e_l, acc
    | E_fby (e1, e2) ->
      let e1, acc = scope_exp e1 acc in
      let e2, acc = scope_exp e2 acc in
      Acids_scoped.E_fby (e1, e2), acc
    | E_ifthenelse (e1, e2, e3) ->
      let e1, acc = scope_exp e1 acc in
      let e2, acc = scope_exp e2 acc in
      let e3, acc = scope_exp e3 acc in
      Acids_scoped.E_ifthenelse (e1, e2, e3), acc
    | E_app (app, e) ->
      let app, acc = scope_app local_constrs imported_mods app acc in
      let e, acc = scope_exp e acc in
      Acids_scoped.E_app (app, e), acc
    | E_where (e, block) ->
      let block, acc =
        scope_block local_nodes local_constrs imported_mods block acc
      in
      let e, acc = scope_exp e acc in
      Acids_scoped.E_where (e, block), acc
    | E_when (e, ce) ->
      let e, acc = scope_exp e acc in
      let ce, acc = scope_clock_exp ce acc in
      Acids_scoped.E_when (e, ce), acc
    | E_split (ce, e) ->
      let e, acc = scope_exp e acc in
      let ce, acc = scope_clock_exp ce acc in
      Acids_scoped.E_split (ce, e), acc
    | E_bmerge (ce, e1, e2) ->
      let ce, acc = scope_clock_exp ce acc in
      let e1, acc = scope_exp e1 acc in
      let e2, acc = scope_exp e2 acc in
      Acids_scoped.E_bmerge (ce, e1, e2), acc
    | E_merge (ce, c_l) ->
      let ce, acc = scope_clock_exp ce acc in
      let c_l, acc =
        Utils.mapfold
          (scope_merge_clause local_nodes local_constrs imported_mods)
          c_l
          acc
      in
      Acids_scoped.E_merge (ce, c_l), acc
    | E_valof ce ->
      let ce, acc = scope_clock_exp ce acc in
      Acids_scoped.E_valof ce, acc
    | E_clockannot (e, cka) ->
      let e, acc = scope_exp e acc in
      let cka, acc =
        scope_clock_annot local_nodes local_constrs imported_mods cka acc
      in
      Acids_scoped.E_clockannot (e, cka), acc
    | E_dom (e, dom) ->
      let e, acc = scope_exp e acc in
      let dom, acc =
        scope_domain local_nodes local_constrs imported_mods dom acc
      in
      Acids_scoped.E_dom (e, dom), acc
  in
  {
    Acids_scoped.e_desc = ed;
    Acids_scoped.e_loc = e.e_loc;
    Acids_scoped.e_info = e.e_info;
  },
  acc

and scope_app local_nodes imported_mods app (intf_env, id_env) =
  let op, acc =
    match app.a_op with
    | O_node ln ->
      let ln, intf_env =
        scope_node local_nodes imported_mods intf_env ln app.a_loc
      in
      Acids_scoped.O_node ln, (intf_env, id_env)
  in
  {
    Acids_scoped.a_op = op;
    Acids_scoped.a_info = app.a_info;
    Acids_scoped.a_loc = app.a_loc;
  },
  acc

and scope_block local_nodes local_constrs imported_mods block acc =
  check_block block;

  let p_l, acc =
    let scope_eq_pat eq acc =
      scope_pattern local_nodes local_constrs imported_mods eq.eq_lhs acc
    in
    Utils.mapfold scope_eq_pat block.b_body acc
  in

  let body, acc =
    Utils.mapfold
      (scope_eq local_nodes local_constrs imported_mods)
      (List.combine p_l block.b_body)
      acc
  in
  {
    Acids_scoped.b_body = body;
    Acids_scoped.b_loc = block.b_loc;
    Acids_scoped.b_info = block.b_info;
  },
  acc

and scope_eq local_nodes local_constrs imported_mods (p, eq) acc =
  let e, acc =
    scope_exp local_nodes local_constrs imported_mods eq.eq_rhs acc
  in
  {
    Acids_scoped.eq_lhs = p;
    Acids_scoped.eq_rhs = e;
    Acids_scoped.eq_loc = eq.eq_loc;
    Acids_scoped.eq_info = eq.eq_info;
  },
  acc

and scope_merge_clause local_nodes local_constrs imported_mods c acc =
  let ec, acc = scope_econstr local_constrs imported_mods c.c_loc c.c_sel acc in
  let e, acc = scope_exp local_nodes local_constrs imported_mods c.c_body acc in
  {
    Acids_scoped.c_sel = ec;
    Acids_scoped.c_body = e;
    Acids_scoped.c_loc = c.c_loc;
  }, acc

and scope_pattern
    local_nodes local_constrs imported_mods p ((intf_env, id_env) as acc) =
  let scope_pattern = scope_pattern local_nodes local_constrs imported_mods in
  let scope_exp = scope_exp local_nodes local_constrs imported_mods in
  let pd, acc =
    match p.p_desc with
    | P_var v ->
      let id, id_env = add_var id_env v in
      Acids_scoped.P_var id, (intf_env, id_env)
    | P_tuple p_l ->
      let p_l, acc = Utils.mapfold scope_pattern p_l acc in
      Acids_scoped.P_tuple p_l, acc
    | P_clock_annot (p, cka) ->
      let cka, acc =
        scope_clock_annot local_nodes local_constrs imported_mods cka acc
      in
      let p, acc = scope_pattern p acc in
      Acids_scoped.P_clock_annot (p, cka), acc
    | P_split upw ->
      let p_l, acc = Ast_misc.mapfold_upword scope_pattern scope_exp upw acc in
      Acids_scoped.P_split p_l, acc
  in
  {
    Acids_scoped.p_desc = pd;
    Acids_scoped.p_loc = p.p_loc;
    Acids_scoped.p_info = p.p_info;
  },
  acc

and scope_domain local_nodes local_constrs imported_mods dom acc =
  let scope_clock_annot =
    scope_clock_annot local_nodes local_constrs imported_mods
  in
  let base_clock, acc =
    Utils.mapfold_opt scope_clock_annot dom.d_base_clock acc
  in
  {
    Acids_scoped.d_base_clock = base_clock;
    Acids_scoped.d_par = dom.d_par;
  },
  acc

let scope_node_def
    imported_mods node (local_nodes, local_constrs, local_types, intf_env) =
  check_node_name local_nodes node.n_name node.n_loc;
  check_pattern node.n_input;
  Ident.reset ();
  let acc = (intf_env, Utils.String_map.empty) in
  let inp, acc =
    scope_pattern local_nodes local_constrs imported_mods node.n_input acc
  in
  let body, (intf_env, _) =
    scope_exp local_nodes local_constrs imported_mods node.n_body acc
  in
  let node =
    {
      Acids_scoped.n_name = node.n_name;
      Acids_scoped.n_input = inp;
      Acids_scoped.n_body = body;
      Acids_scoped.n_pragma = node.n_pragma;
      Acids_scoped.n_static = node.n_static;
      Acids_scoped.n_loc = node.n_loc;
      Acids_scoped.n_info = node.n_info;
    }
  in
  let local_nodes = Names.ShortSet.add node.Acids_scoped.n_name local_nodes in
  node, (local_nodes, local_constrs, local_types, intf_env)

let scope_node_decl
    decl (local_nodes, local_constrs, local_types, intf_env) =
  check_node_name local_nodes decl.decl_name decl.decl_loc;
  let decl =
    {
      Acids_scoped.decl_name = decl.decl_name;
      Acids_scoped.decl_data = decl.decl_data;
      Acids_scoped.decl_static = decl.decl_static;
      Acids_scoped.decl_interv = decl.decl_interv;
      Acids_scoped.decl_clock = decl.decl_clock;
      Acids_scoped.decl_loc = decl.decl_loc;
    }
  in
  decl,
  (Names.ShortSet.add decl.Acids_scoped.decl_name local_nodes,
   local_constrs,
   local_types,
   intf_env)

let scope_type_def
    tdef (local_nodes, local_constrs, local_types, intf_env) =
  check_type_name local_types tdef.ty_name tdef.ty_loc;
  let check_type_constr local_constrs constr =
    if Names.ShortSet.mem constr local_constrs
    then duplicate_constr constr tdef.ty_loc
    else Names.ShortSet.add constr local_constrs
  in
  let local_constrs =
    List.fold_left check_type_constr local_constrs tdef.ty_body
  in
  let tdef =
    {
      Acids_scoped.ty_name = tdef.ty_name;
      Acids_scoped.ty_body = tdef.ty_body;
      Acids_scoped.ty_loc = tdef.ty_loc;
    }
  in
  tdef,
  (local_nodes,
   local_constrs,
   Names.ShortSet.add tdef.Acids_scoped.ty_name local_types,
   intf_env)

let scope_phrase imported_mods acc phr =
  match phr with
  | Phr_node_def def ->
    let def, acc = scope_node_def imported_mods def acc in
    acc, Acids_scoped.Phr_node_def def
  | Phr_node_decl decl ->
    let decl, acc = scope_node_decl decl acc in
    acc, Acids_scoped.Phr_node_decl decl
  | Phr_type_def td ->
    let td, acc = scope_type_def td acc in
    acc, Acids_scoped.Phr_type_def td

let scope_file ctx (file : unit Acids_parsetree.file) =
  let intf_env =
    let load intf_env modn =
      let intf = Interface.load_interface_from_module_name modn in
      Names.ShortEnv.add modn intf intf_env
    in
    List.fold_left load Names.ShortEnv.empty file.f_imports
  in
  let acc =
    Names.ShortSet.empty, Names.ShortSet.empty, Names.ShortSet.empty, intf_env
  in
  let (_, _, _, intf_env), body =
    Utils.mapfold_left (scope_phrase file.f_imports) acc file.f_body
  in
  ctx,
  {
    Acids_scoped.f_name = file.f_name;
    Acids_scoped.f_imports = file.f_imports;
    Acids_scoped.f_info = object method interfaces = intf_env end;
    Acids_scoped.f_body = body;
  }

(** {2 Putting it all together} *)

let scope =
  let open Pass_manager in
  P_transform
    (Frontend_utils.make_transform
       ~print_out:Acids_scoped.print_file
       "scoping"
       scope_file)
