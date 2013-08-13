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
  | Unknown_type of Names.shortname * Loc.t
  | Node_not_found of Names.modname * Names.shortname * Loc.t
  | Constr_not_found of Names.modname * Names.shortname * Loc.t
  | Type_not_found of Names.modname * Names.shortname * Loc.t
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
  | Unknown_type (shortn, l) ->
    Format.fprintf fmt "%aUnknown type %a"
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
  | Type_not_found (modn, constrn, l) ->
    Format.fprintf fmt "%aType %a not found in module %a"
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

let unknown_type shortn loc =
  raise (Scoping_error (Unknown_type (shortn, loc)))

let node_not_found modn shortn loc =
  raise (Scoping_error (Node_not_found (modn, shortn, loc)))

let constr_not_found modn shortn loc =
  raise (Scoping_error (Constr_not_found (modn, shortn, loc)))

let type_not_found modn shortn loc =
  raise (Scoping_error (Type_not_found (modn, shortn, loc)))

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

(** {2 Environments} *)

type env =
  {
    local_nodes : Names.ShortSet.t;
    local_constrs : Names.ShortSet.t;
    local_constrs_ranks : Int.t Names.ShortEnv.t;
    local_types : Names.ShortSet.t;
    imported_mods : string list;
    id_env : Ident.t Utils.Env.t;
    mutable intf_env : Interface.env;
  }

let initial_env intf_env imported_mods =
  {
    local_nodes = Names.ShortSet.empty;
    local_constrs = Names.ShortSet.empty;
    local_constrs_ranks = Names.ShortEnv.empty;
    local_types = Names.ShortSet.empty;
    imported_mods = imported_mods;
    id_env = Utils.Env.empty;
    intf_env = intf_env;
  }

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
    Names.ShortEnv.mem shortn (access intf)
  in
  try List.find mod_has_node imported_mods
  with Not_found -> error shortn loc

let find_module_with_node =
  find_module_with_shortname (fun i -> i.Interface.i_nodes) unknown_node

let find_module_with_constr =
  find_module_with_shortname (fun i -> i.Interface.i_constrs) unknown_constr

let find_module_with_type_name =
  find_module_with_shortname (fun i -> i.Interface.i_types) unknown_type

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
let check_module_with_name access error env modn shortn loc =
  let intf, intf_env =
    try Names.ShortEnv.find modn env.intf_env, env.intf_env
    with Not_found ->
      let intf = Interface.load_interface_from_module_name modn in
      intf, Names.ShortEnv.add modn intf env.intf_env
  in
  if not (Names.ShortEnv.mem shortn (access intf))
  then error modn shortn loc;
  env.intf_env <- intf_env

let check_module_with_node =
  check_module_with_name (fun i -> i.Interface.i_nodes) node_not_found

let check_module_with_constr =
  check_module_with_name (fun i -> i.Interface.i_constrs) constr_not_found

let check_module_with_type_name =
  check_module_with_name (fun i -> i.Interface.i_types) type_not_found

(** Scope a name in the proper name-space (nodes or constructors) *)
let scope_longname find check access env loc ln =
  let open Names in
  match ln.modn with
  | LocalModule ->
    (* We check in [locals] whether the name is indeed known
       at this point. Otherwise we look it up in the imported
       modules. *)
    if ShortSet.mem ln.shortn (access env)
    then ln
    else
      let modn = find env.imported_mods env.intf_env ln.shortn loc in
      { ln with modn = Module modn; }
  | Module modn ->
    (* Check that the module indeed holds the name (loading it if needed). *)
    check env modn ln.shortn loc;
    ln

let scope_node =
  let access env = env.local_nodes in
  scope_longname find_module_with_node check_module_with_node access

let scope_constr =
  let access env = env.local_constrs in
  scope_longname find_module_with_constr check_module_with_constr access

let scope_type_name =
  let access env = env.local_types in
  scope_longname find_module_with_type_name check_module_with_type_name access

let add_var env v =
  let id = Ident.make_source v in
  id, { env with id_env = Utils.Env.add v id env.id_env; }

let add_local_node env n =
  { env with local_nodes = Names.ShortSet.add n env.local_nodes; }

let find_var env loc v =
  try Utils.Env.find v env.id_env
  with Not_found -> unbound_var v loc

let add_local_constrs_ranks env cn_l =
  let add (rank, local_constrs_ranks) cn =
    Int.succ rank, Names.ShortEnv.add cn rank local_constrs_ranks
  in
  let _, local_constrs_ranks =
    List.fold_left add (Int.zero, env.local_constrs_ranks) cn_l
  in
  { env with local_constrs_ranks = local_constrs_ranks; }

(** {2 AST traversal} *)

open Acids_parsetree

(** {3 Multiple binding checks} *)

let check_pattern block_loc block_env p =
  let pat_loc = p.p_loc in
  let rec walk pat_env p =
    match p.p_desc with
    | P_var s | P_condvar (s, _) ->
        if Utils.String_set.mem s pat_env
        then multiple_binding_pattern s pat_loc;
        if Utils.String_set.mem s block_env
        then multiple_binding_block s block_loc;
        Utils.String_set.add s pat_env
    | P_tuple p_l -> List.fold_left walk pat_env p_l
    | P_clock_annot (p, _) | P_type_annot (p, _) | P_spec_annot (p, _) ->
      walk pat_env p
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

let check_node_name env nn loc =
  if Names.ShortSet.mem nn env.local_nodes then duplicate_node nn loc

let check_type_constr loc env cn =
  if Names.ShortSet.mem cn env.local_constrs
  then duplicate_constr cn loc
  else { env with local_constrs = Names.ShortSet.add cn env.local_constrs; }

let check_type_name env tn loc =
  if Names.ShortSet.mem tn env.local_types then duplicate_type tn loc

let find_scoped_constr_rank env cstr =
  let open Names in
  match cstr.modn with
  | LocalModule -> Names.ShortEnv.find cstr.shortn env.local_constrs_ranks
  | Module modn ->
    let intf = Names.ShortEnv.find modn env.intf_env in
    Int.of_int (Interface.find_constructor_rank intf cstr.shortn)

(** {3 Scoping} *)

let rec scope_econstr env loc ec =
  match ec with
  | Ast_misc.Ec_int _ | Ast_misc.Ec_bool _ -> ec
  | Ast_misc.Ec_constr (ln, rank) ->
    assert Int.(rank = of_int (- 1));
    let ln = scope_constr env loc ln in
    let rank = find_scoped_constr_rank env ln in
    Ast_misc.Ec_constr (ln, rank)

and scope_const env loc c =
  match c with
  | Ast_misc.Cconstr ec -> Ast_misc.Cconstr (scope_econstr env loc ec)
  | Ast_misc.Cfloat _ -> c

and scope_clock_annot env cka =
  let scope_clock_exp = scope_clock_exp env in
  let scope_clock_annot = scope_clock_annot env in
  match cka with
  | Ca_var i ->
    Acids_scoped.Ca_var i
  | Ca_on (cka, ce) ->
    let cka = scope_clock_annot cka in
    let ce = scope_clock_exp ce in
    Acids_scoped.Ca_on (cka, ce)

and scope_clock_exp env ce =
  let scope_static_exp_one = scope_static_exp_one env in
  let scope_clock_exp = scope_clock_exp env in
  let ced =
    match ce.ce_desc with
    | Ce_condvar v ->
      let v = find_var env ce.ce_loc v in
      Acids_scoped.Ce_condvar v
    | Ce_pword upw ->
      let upw = scope_static_word env upw in
      Acids_scoped.Ce_pword upw
    | Ce_equal (ce, se) ->
      let ce = scope_clock_exp ce in
      let se = scope_static_exp_one se in
      Acids_scoped.Ce_equal (ce, se)
  in
  {
    Acids_scoped.ce_desc = ced;
    Acids_scoped.ce_loc = ce.ce_loc;
    Acids_scoped.ce_info = ce.ce_info;
  }

(* Because of Se_fword, one static exp may get scoped into several ones *)
and scope_static_exps env se =
  let mk sed =
    {
      Acids_scoped.se_desc = sed;
      Acids_scoped.se_loc = se.se_loc;
      Acids_scoped.se_info = se.se_info;
    }
  in
  let ed_l =
    match se.se_desc with
    | Acids_parsetree.Info.Se_var v ->
      let id = find_var env se.se_loc v in
      [Acids_scoped.Info.Se_var id]
    | Acids_parsetree.Info.Se_econstr ec ->
      [Acids_scoped.Info.Se_econstr ec]
    | Acids_parsetree.Info.Se_fword i_l ->
      let mk i = Acids_scoped.Info.Se_econstr (Ast_misc.Ec_int i) in
      List.map mk i_l
    | Acids_parsetree.Info.Se_add (se1, se2) ->
      let se1 = scope_static_exp_one env se1 in
      let se2 = scope_static_exp_one env se2 in
      [Acids_scoped.Info.Se_add (se1, se2)]
  in
  List.map mk ed_l

and scope_static_exp_one env se =
  match scope_static_exps env se with
  | [se] -> se
  | _ -> assert false

and scope_static_word env upw =
  let open Tree_word in

  let { u = u; v = v; } =
    Ast_misc.map_upword
      (scope_static_exps env)
      (scope_static_exp_one env)
      upw
  in

  (* Remove list leaves coming from Se_fword *)

  let rec flatten_tree t =
    match t with
    | Leaf [se] -> Leaf se
    | Leaf se_l -> Concat (List.map (fun se -> Leaf se) se_l)
    | Concat t_l -> Concat (List.map flatten_tree t_l)
    | Power (t, se) -> Power (flatten_tree t, se)
  in

  { u = flatten_tree u; v = flatten_tree v; }

and scope_exp env e =
  let scope_exp' = scope_exp env in
  let scope_clock_exp = scope_clock_exp env in
  let ed =
    match e.e_desc with
    | E_var v ->
      let id = find_var env e.e_loc v in
      Acids_scoped.E_var id

    | E_const c ->
      let c = scope_const env e.e_loc c in
      Acids_scoped.E_const c

    | E_fst e ->
      let e = scope_exp' e in
      Acids_scoped.E_fst e

    | E_snd e ->
      let e = scope_exp' e in
      Acids_scoped.E_snd e

    | E_tuple e_l ->
      let e_l = List.map scope_exp' e_l in
      Acids_scoped.E_tuple e_l

    | E_fby (e1, e2) ->
      let e1 = scope_exp' e1 in
      let e2 = scope_exp' e2 in
      Acids_scoped.E_fby (e1, e2)

    | E_ifthenelse (e1, e2, e3) ->
      let e1 = scope_exp' e1 in
      let e2 = scope_exp' e2 in
      let e3 = scope_exp' e3 in
      Acids_scoped.E_ifthenelse (e1, e2, e3)

    | E_app (app, e) ->
      let app = scope_app env app in
      let e = scope_exp' e in
      Acids_scoped.E_app (app, e)

    | E_where (e, block) ->
      let block, env = scope_block env block in
      let e = scope_exp env e in
      Acids_scoped.E_where (e, block)

    | E_when (e, ce) ->
      let e = scope_exp' e in
      let ce = scope_clock_exp ce in
      Acids_scoped.E_when (e, ce)

    | E_split (ce, e', ec_l) ->
      let e' = scope_exp' e' in
      let ce = scope_clock_exp ce in
      let ec_l = List.map (scope_econstr env e.e_loc) ec_l in
      Acids_scoped.E_split (ce, e', ec_l)

    | E_bmerge (ce, e1, e2) ->
      let ce = scope_clock_exp ce in
      let e1 = scope_exp' e1 in
      let e2 = scope_exp' e2 in
      Acids_scoped.E_bmerge (ce, e1, e2)

    | E_merge (ce, c_l) ->
      let ce = scope_clock_exp ce in
      let c_l = List.map (scope_merge_clause env) c_l in
      Acids_scoped.E_merge (ce, c_l)

    | E_valof ce ->
      let ce = scope_clock_exp ce in
      Acids_scoped.E_valof ce

    | E_clock_annot (e, cka) ->
      let e = scope_exp' e in
      let cka = scope_clock_annot env cka in
      Acids_scoped.E_clock_annot (e, cka)

    | E_type_annot (e, ty) ->
      let e = scope_exp' e in
      let ty = scope_type env e.Acids_scoped.e_loc ty in
      Acids_scoped.E_type_annot (e, ty)

    | E_spec_annot (e, spec) ->
      let e = scope_exp' e in
      let spec = scope_spec env spec in
      Acids_scoped.E_spec_annot (e, spec)

    | E_dom (e, dom) ->
      let e = scope_exp' e in
      let dom = scope_domain env dom in
      Acids_scoped.E_dom (e, dom)

    | E_buffer (e, bu) ->
      let e = scope_exp' e in
      Acids_scoped.E_buffer (e, scope_buffer bu)
  in
  {
    Acids_scoped.e_desc = ed;
    Acids_scoped.e_loc = e.e_loc;
    Acids_scoped.e_info = e.e_info;
  }

and scope_app env app =
  let nn = scope_node env app.a_loc app.a_op in
  {
    Acids_scoped.a_op = nn;
    Acids_scoped.a_info = app.a_info;
    Acids_scoped.a_loc = app.a_loc;
  }

and scope_block env block =
  check_block block;

  let p_l, env =
    let scope_eq_pat eq env = scope_pattern eq.eq_lhs env in
    Utils.mapfold scope_eq_pat block.b_body env
  in

  let body = List.map (scope_eq env) (List.combine p_l block.b_body) in
  {
    Acids_scoped.b_body = body;
    Acids_scoped.b_loc = block.b_loc;
    Acids_scoped.b_info = block.b_info;
  },
  env

and scope_eq env (p, eq) =
  let e = scope_exp env eq.eq_rhs in
  {
    Acids_scoped.eq_lhs = p;
    Acids_scoped.eq_rhs = e;
    Acids_scoped.eq_loc = eq.eq_loc;
    Acids_scoped.eq_info = eq.eq_info;
  }

and scope_merge_clause env c =
  let ec = scope_econstr env c.c_loc c.c_sel in
  let e = scope_exp env c.c_body in
  {
    Acids_scoped.c_sel = ec;
    Acids_scoped.c_body = e;
    Acids_scoped.c_loc = c.c_loc;
  }

and scope_type_scal env loc tys =
  let open Data_types in
  match tys with
  | Tys_bool | Tys_int | Tys_float -> tys
  | Tys_user ln -> Tys_user (scope_type_name env loc ln)

and scope_type env loc ty =
  let open Data_types in
  let scope_type = scope_type env loc in
  match ty with
  | Ty_var i -> Ty_var i
  | Ty_scal tys -> Ty_scal (scope_type_scal env loc tys)
  | Ty_cond ty -> Ty_cond (scope_type ty)
  | Ty_prod ty_l -> Ty_prod (List.map scope_type ty_l)

and scope_pattern p env =
  let pd, env =
    match p.p_desc with
    | P_var v ->
      let id, env = add_var env v in
      Acids_scoped.P_var id, env
    | P_condvar (v, specs) ->
      let id, env = add_var env v in
      let specs = List.map (scope_spec env) specs in
      Acids_scoped.P_condvar (id, specs), env
    | P_tuple p_l ->
      let p_l, env = Utils.mapfold scope_pattern p_l env in
      Acids_scoped.P_tuple p_l, env
    | P_clock_annot (p, cka) ->
      let cka = scope_clock_annot env cka in
      let p, env = scope_pattern p env in
      Acids_scoped.P_clock_annot (p, cka), env
    | P_type_annot (p, ty) ->
      let p, env = scope_pattern p env in
      let ty = scope_type env p.Acids_scoped.p_loc ty in
      Acids_scoped.P_type_annot (p, ty), env
    | P_spec_annot (p, spec) ->
      let p, env = scope_pattern p env in
      let spec = scope_spec env spec in
      Acids_scoped.P_spec_annot (p, spec), env
    | P_split upw ->
      let scope_static_exp se env = scope_static_exp_one env se, env in
      let p_l, env =
        Ast_misc.mapfold_upword scope_pattern scope_static_exp upw env
      in
      Acids_scoped.P_split p_l, env
  in
  {
    Acids_scoped.p_desc = pd;
    Acids_scoped.p_loc = p.p_loc;
    Acids_scoped.p_info = p.p_info;
  },
  env

and scope_domain env dom =
  let scope_clock_annot = scope_clock_annot env in
  let base_clock = Utils.map_opt scope_clock_annot dom.d_base_clock in
  {
    Acids_scoped.d_base_clock = base_clock;
    Acids_scoped.d_par = dom.d_par;
    Acids_scoped.d_info = dom.d_info;
  }

and scope_buffer bu =
  {
    Acids_scoped.bu_info = bu.bu_info;
  }

and scope_spec env spec =
  let scope_static_exp_one = scope_static_exp_one env in
  let sd =
    match spec.s_desc with
    | Unspec ->
      Acids_scoped.Unspec
    | Word upw ->
      Acids_scoped.Word (scope_static_word env upw)
    | Interval (l, u) ->
      let l = scope_static_exp_one l in
      let u = scope_static_exp_one u in
      Acids_scoped.Interval (l, u)
  in
  {
    Acids_scoped.s_desc = sd;
    Acids_scoped.s_loc = spec.s_loc;
  }

let scope_node_def env node =
  check_node_name env node.n_name node.n_loc;
  check_pattern node.n_input;
  Ident.reset_ctx ();
  let inp, env = scope_pattern node.n_input env in
  let body = scope_exp env node.n_body in
  let node =
    {
      Acids_scoped.n_name = node.n_name;
      Acids_scoped.n_input = inp;
      Acids_scoped.n_body = body;
      Acids_scoped.n_pragma = node.n_pragma;
      Acids_scoped.n_static = node.n_static;
      Acids_scoped.n_loc = node.n_loc;
      Acids_scoped.n_info = Ident.get_current_ctx ();
    }
  in
  let env = add_local_node env node.Acids_scoped.n_name in
  node, env

let scope_data_sig env loc dsig =
  let open Data_types in
  let inp_ty = scope_type env loc dsig.data_sig_input in
  let out_ty = scope_type env loc dsig.data_sig_output in
  { data_sig_input = inp_ty; data_sig_output = out_ty; }

let scope_node_decl env decl =
  check_node_name env decl.decl_name decl.decl_loc;
  let dsig = scope_data_sig env decl.decl_loc decl.decl_data in
  let decl =
    {
      Acids_scoped.decl_name = decl.decl_name;
      Acids_scoped.decl_data = dsig;
      Acids_scoped.decl_static = decl.decl_static;
      Acids_scoped.decl_clock = decl.decl_clock;
      Acids_scoped.decl_loc = decl.decl_loc;
    }
  in
  decl, add_local_node env decl.Acids_scoped.decl_name

let scope_type_def env tdef =
  check_type_name env tdef.ty_name tdef.ty_loc;
  let env = List.fold_left (check_type_constr tdef.ty_loc) env tdef.ty_body in
  let env = add_local_constrs_ranks env tdef.ty_body in
  let tdef =
    {
      Acids_scoped.ty_name = tdef.ty_name;
      Acids_scoped.ty_body = tdef.ty_body;
      Acids_scoped.ty_loc = tdef.ty_loc;
    }
  in
  tdef, env

let scope_phrase env phr =
  match phr with
  | Phr_node_def def ->
    let def, env = scope_node_def env def in
    env, Acids_scoped.Phr_node_def def
  | Phr_node_decl decl ->
    let decl, env = scope_node_decl env decl in
    env, Acids_scoped.Phr_node_decl decl
  | Phr_type_def td ->
    let td, env = scope_type_def env td in
    env, Acids_scoped.Phr_type_def td

let scope_file ctx (file : unit Acids_parsetree.file) =
  let intf_env =
    let load intf_env modn =
      let intf = Interface.load_interface_from_module_name modn in
      Names.ShortEnv.add modn intf intf_env
    in
    List.fold_left load Names.ShortEnv.empty file.f_imports
  in
  let env = initial_env intf_env file.f_imports in
  let _, body = Utils.mapfold_left scope_phrase env file.f_body in
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
