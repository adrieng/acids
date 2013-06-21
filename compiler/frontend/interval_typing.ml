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

open Acids_typed
open Interval_types

(** {1 Interval typing}

    Nothing special for now. *)

(** {2 Utility functions} *)

let pat_type p = p.Acids_interval.p_info#pi_interv

let exp_type e = e.Acids_interval.e_info#ei_interv

let clock_exp_type ce = ce.Acids_interval.ce_info#ci_interv

let pat_annotate p ty =
  object
    method pi_data = p.p_info#pi_data
    method pi_interv = ty
  end

let exp_annotate e ty =
  object
    method ei_data = e.e_info#ei_data
    method ei_interv = ty
  end

let clock_exp_annotate ce ty =
  object
    method ci_data = ce.ce_info#ci_data
    method ci_interv = ty
  end

let pword_exp_annotate pwe ty =
  object
    method pwi_data = pwe.pwe_info#pwi_data
    method pwi_interv = ty
  end

let node_annotate nd ty =
  object
    method ni_data = nd.n_info#ni_data
    method ni_interv = ty
  end

(** {2 Errors} *)

type error =
  | Non_exhaustive_pattern of Loc.t * Ast_misc.econstr
  | Unexpected_pattern of Loc.t * Ast_misc.econstr * Ast_misc.econstr list
  | Duplicate_pattern of Loc.t * Ast_misc.econstr
  | Not_subset_pat of Acids_interval.pat * Acids_interval.exp
  | Not_subset_ce of Acids_interval.clock_exp * Interval.t
  | Bad_annot of Loc.t * Ident.t
  | Exp_not_inter of Acids_interval.exp
  | Bad_application of Acids_typed.exp * Interval_types.ty * Interval_types.ty

exception Typing_error of error

let print_error fmt err =
  match err with
  | Non_exhaustive_pattern (l, ec) ->
    Format.fprintf fmt "%aThis pattern-matching is not exhaustive@\n"
      Loc.print l;
    Format.fprintf fmt "Here is an example of a value that is not matched:@\n%a"
      Ast_misc.print_econstr ec
  | Unexpected_pattern (l, ec, exp) ->
    Format.fprintf fmt "%aThe pattern %a was unexpected@\n"
      Loc.print l
      Ast_misc.print_econstr ec;
    Format.fprintf fmt "Expected patterns are: @[%a@]"
      (Utils.print_list_r Ast_misc.print_econstr ",") exp
  | Duplicate_pattern (l, ec) ->
    Format.fprintf fmt "%aDuplicate pattern %a"
      Loc.print l
      Ast_misc.print_econstr ec
  | Not_subset_pat (p, e) ->
    Format.fprintf fmt
      "%aThe declared value range for %a (%a) is smaller than@ the inferred value range of %a (%a)"
      Loc.print p.Acids_interval.p_loc
      Acids_interval.print_pat p
      print_ty (pat_type p)
      Acids_interval.print_exp e
      print_ty (exp_type e)
  | Not_subset_ce (ce, it) ->
    Format.fprintf fmt
      "%aThe inferred value range for clock expression %a is not included in %a"
      Loc.print ce.Acids_interval.ce_loc
      Acids_interval.print_clock_exp ce
      Interval.print it
  | Bad_annot (l, id) ->
    Format.fprintf fmt "%aThe clock variable %a has no interval annotation"
      Loc.print l
      Ident.print id
  | Exp_not_inter e ->
    Format.fprintf fmt
      "%aThe expression %a appears in a clock and has no interval annotation"
      Loc.print e.Acids_interval.e_loc
      Acids_interval.print_exp e
  | Bad_application (e, ty_exp, ty_actual) ->
    Format.fprintf fmt
      "%aThe application %a expects %a but was applied to %a"
      Loc.print e.Acids_typed.e_loc
      Acids_typed.print_exp e
      print_ty ty_exp
      print_ty ty_actual

let non_exhaustive_pattern loc ec =
  raise (Typing_error (Non_exhaustive_pattern (loc, ec)))

let unexpected_pattern loc ec exp =
  raise (Typing_error (Unexpected_pattern (loc, ec, exp)))

let duplicate_pattern loc ec =
  raise (Typing_error (Duplicate_pattern (loc, ec)))

let not_subset_pat p e =
  raise (Typing_error (Not_subset_pat (p, e)))

let not_subset_ce ce it =
  raise (Typing_error (Not_subset_ce (ce, it)))

let bad_annot loc v =
  raise (Typing_error (Bad_annot (loc, v)))

let exp_not_inter e =
  raise (Typing_error (Exp_not_inter e))

let bad_application e ty_exp ty_actual =
  raise (Typing_error (Bad_application (e, ty_exp, ty_actual)))

(** {2 High-level utilities} *)

let ty_top = It_scal Is_top

let ty_inter it = It_scal (Is_inter it)

let ty_bool = ty_inter Interval.bool

let iter it = Interval.make Int.zero (Int.pred it.Interval.u)

let join_l ty_l = Utils.fold_left_1 join ty_l

let fst_ty ty =
  match ty with
  | It_prod [ty; _] -> ty
  | _ -> invalid_arg "fst_ty"

let snd_ty ty =
  match ty with
  | It_prod [_; ty] -> ty
  | _ -> invalid_arg "fst_ty"

(** {2 Typing environments} *)

type typing_env =
  {
    intf_env : Interface.t Names.ShortEnv.t;
    current_types : Names.shortname list Names.ShortEnv.t;
    current_nodes : ty_sig Names.ShortEnv.t;
    idents : ty Ident.Env.t;
  }

let initial_typing_env intf_env =
  {
    intf_env = intf_env;
    current_types = Names.ShortEnv.empty;
    current_nodes = Names.ShortEnv.empty;
    idents = Ident.Env.empty;
  }

let reset_idents env = { env with idents = Ident.Env.empty; }

let find_ident env v = Ident.Env.find v env.idents

let add_ident env v ty = { env with idents = Ident.Env.add v ty env.idents; }

let find_constructors_for_type env ln =
  let open Names in
  let sn_l =
    match ln.modn with
    | LocalModule -> Names.ShortEnv.find ln.shortn env.current_types
    | Module modn ->
      let intf = Names.ShortEnv.find modn env.intf_env in
      (Interface.find_type intf ln.shortn).Interface.td_constr
  in
  List.map (fun sn -> { ln with shortn = sn; }) sn_l

let add_type_constructors env name constructors =
  {
    env with
      current_types = Names.ShortEnv.add name constructors env.current_types;
  }

let find_signature env ln =
  let open Names in
  match ln.modn with
  | LocalModule ->
    Names.ShortEnv.find ln.shortn env.current_nodes
  | Module modn ->
    let intf = Names.ShortEnv.find modn env.intf_env in
    let node = Interface.find_node intf ln.shortn in
    Interface.interval_signature_of_node_item node

let add_local_signature env sn isig =
  { env with current_nodes = Names.ShortEnv.add sn isig env.current_nodes; }

(** {2 Typing AST nodes} *)

(** The algorithm proceeds in one pass: all variables have to be explicitely
    tagged with their intervals if the user wishes to. *)

let rec free_type_for_data_type ty =
  let open Data_types in
  match ty with
  | Ty_var _ -> ty_top (* unsure *)
  | Ty_scal _ -> ty_top
  | Ty_prod ty_l -> It_prod (List.map free_type_for_data_type ty_l)

let check_pattern_range env loc it ty c_l =
  let open Data_types in
  let open Ast_misc in
  let ec_l =
    match ty with
    | Tys_float -> invalid_arg "check_pattern_range: float"
    | Tys_bool -> [Ec_bool true; Ec_bool false]
    | Tys_int ->
      let range =
        Utils.range
          (Int.to_int it.Interval.l)
          (Int.to_int it.Interval.u) (* TODO may fail with big patterns *)
      in
      List.map (fun i -> Ec_int (Int.of_int i)) range
    | Tys_user ln ->
      let ec_l = find_constructors_for_type env ln in
      List.map (fun constr -> Ec_constr constr) ec_l
  in

  let rec check_exhaustive expected seen actual =
    match actual with
    | [] -> ()
    | ec :: actual ->
      if not (List.mem ec expected)
      then unexpected_pattern loc ec expected;
      if List.mem ec seen
      then duplicate_pattern loc ec;
      check_exhaustive expected (ec :: seen) actual
  in
  check_exhaustive ec_l [] c_l

let rec enrich_env_pat env p =
  match p.p_desc with
  | P_var (v, info) ->
    let ty =
      match info with
      | None -> free_type_for_data_type p.p_info#pi_data
      | Some it -> ty_inter it
    in
    add_ident env v ty
  | P_tuple p_l ->
    List.fold_left enrich_env_pat env p_l
  | P_clock_annot (p, _) | P_type_annot (p, _) ->
    enrich_env_pat env p
  | P_split w ->
    Ast_misc.fold_upword
      (fun p env -> enrich_env_pat env p)
      (fun _ env -> env)
      w
      env

let enrich_env_eq env eq = enrich_env_pat env eq.eq_lhs

let rec type_pat env p =
  let pd, ty =
    match p.p_desc with
    | P_var (v, info) ->
      Acids_interval.P_var (v, info), find_ident env v

    | P_tuple p_l ->
      let p_l = List.map (type_pat env) p_l in
      let ty_l = List.map pat_type p_l in
      Acids_interval.P_tuple p_l, It_prod ty_l

    | P_clock_annot (p, cka) ->
      let p = type_pat env p in
      let cka = type_clock_annot env cka in
      Acids_interval.P_clock_annot (p, cka), pat_type p

    | P_type_annot (p, tya) ->
      let p = type_pat env p in
      Acids_interval.P_type_annot (p, tya), pat_type p

    | P_split w ->
      let w = Ast_misc.map_upword (type_pat env) (type_exp env) w in
      let ty_l =
        Ast_misc.fold_upword
          (fun p acc -> pat_type p :: acc)
          (fun _ acc -> acc)
          w
          []
      in
      Acids_interval.P_split w, Utils.fold_left_1 Interval_types.join ty_l
  in
  {
    Acids_interval.p_desc = pd;
    Acids_interval.p_info = pat_annotate p ty;
    Acids_interval.p_loc = p.p_loc;
  }

and type_clock_annot env cka =
  match cka with
  | Ca_var i -> Acids_interval.Ca_var i
  | Ca_on (cka, ce) ->
    let cka = type_clock_annot env cka in
    let ce = type_clock_exp env ce in
    Acids_interval.Ca_on (cka, ce)

and type_exp env e =
  let ed, ty =
    match e.e_desc with
    | E_const c ->
      Acids_interval.E_const c, type_const env e.e_info#ei_data c

    | E_var v ->
      Acids_interval.E_var v, find_ident env v

    | E_fst e ->
      let e = type_exp env e in
      Acids_interval.E_fst e, fst_ty (exp_type e)

    | E_snd e ->
      let e = type_exp env e in
      Acids_interval.E_snd e, snd_ty (exp_type e)

    | E_tuple e_l ->
      let e_l = List.map (type_exp env) e_l in
      Acids_interval.E_tuple e_l, It_prod (List.map exp_type e_l)

    | E_ifthenelse (e1, e2, e3) ->
      let e1 = type_exp env e1 in
      let e2 = type_exp env e2 in
      let e3 = type_exp env e3 in
      Acids_interval.E_ifthenelse (e1, e2, e3), join (exp_type e1) (exp_type e2)

    | E_fby (e1, e2) ->
      let e1 = type_exp env e1 in
      let e2 = type_exp env e2 in
      Acids_interval.E_fby (e1, e2), join (exp_type e1) (exp_type e2)

    | E_app (app, e') ->
      let isig = find_signature env app.a_op in
      let e' = type_exp env e' in
      let app =
        {
          Acids_interval.a_op = app.a_op;
          Acids_interval.a_loc = app.a_loc;
          Acids_interval.a_info = app.a_info;
        }
      in
      Acids_interval.E_app (app, e'),
      if not (subset (exp_type e') isig.input)
      then bad_application e isig.input (exp_type e')
      else isig.output

    | E_where (e, block) ->
      let block, env = type_block block env in
      let e = type_exp env e in
      Acids_interval.E_where (e, block), exp_type e

    | E_when (e, ce) ->
      let e = type_exp env e in
      let ce = type_clock_exp env ce in
      Acids_interval.E_when (e, ce), exp_type e

    | E_bmerge (ce, e1, e2) ->
      let ce = type_clock_exp env ce in
      let e1 = type_exp env e1 in
      let e2 = type_exp env e2 in
      Acids_interval.E_bmerge (ce, e1, e2), join (exp_type e1) (exp_type e2)

    | E_merge (ce, c_l) ->
      let ce = type_clock_exp env ce in
      check_pattern_range
        env
        e.e_loc
        (clock_exp_type ce)
        ce.Acids_interval.ce_info#ci_data
        (List.map (fun c -> c.c_sel) c_l);
      let c_l = List.map (type_merge_clause env) c_l in
      let ty_l = List.map (fun c -> exp_type c.Acids_interval.c_body) c_l in
      Acids_interval.E_merge (ce, c_l), join_l ty_l

    | E_split (ce, e', ec_l) ->
      let ce = type_clock_exp env ce in
      check_pattern_range
        env
        e.e_loc
        (clock_exp_type ce)
        ce.Acids_interval.ce_info#ci_data
        ec_l;
      let e' = type_exp env e' in
      Acids_interval.E_split (ce, e', ec_l), exp_type e'

    | E_valof ce ->
      let ce = type_clock_exp env ce in
      Acids_interval.E_valof ce, ty_inter (clock_exp_type ce)

    | E_type_annot (e, ty) ->
      let e = type_exp env e in
      Acids_interval.E_type_annot (e, ty), exp_type e

    | E_clock_annot (e, cka) ->
      let e = type_exp env e in
      let cka = type_clock_annot env cka in
      Acids_interval.E_clock_annot (e, cka), exp_type e

    | E_dom (e, dom) ->
      let e = type_exp env e in
      let dom = type_domain env dom in
      Acids_interval.E_dom (e, dom), exp_type e

    | E_buffer e ->
      let e = type_exp env e in
      Acids_interval.E_buffer e, exp_type e

  in
  {
    Acids_interval.e_desc = ed;
    Acids_interval.e_loc = e.e_loc;
    Acids_interval.e_info = exp_annotate e ty;
  }

and type_merge_clause env c =
  {
    Acids_interval.c_sel = c.c_sel;
    Acids_interval.c_body = type_exp env c.c_body;
    Acids_interval.c_loc = c.c_loc;
  }

and type_domain env dom =
  {
    Acids_interval.d_base_clock =
      Utils.map_opt (type_clock_annot env) dom.d_base_clock;
    Acids_interval.d_par = dom.d_par;
    Acids_interval.d_info = dom.d_info;
  }

and type_const env ty c =
  let open Ast_misc in
  match c with
  | Cconstr ec -> It_scal (Is_inter (type_econstr env ty ec))
  | Cfloat _ -> It_scal Is_top

and type_econstr env ty ec =
  let open Ast_misc in
  match ec with
  | Ec_bool b -> Interval.singleton (if b then 1n else 0n)
  | Ec_int i -> Interval.singleton i
  | Ec_constr c ->
    let ln =
      let open Data_types in
      match ty with
      | Ty_scal (Tys_user ln) -> ln
      | _ -> invalid_arg "type_econstr"
    in
    let c_l = find_constructors_for_type env ln in
    Interval.singleton (Int.of_int (Utils.index c c_l))

and type_clock_exp env ce =
  let ced, ty =
    match ce.ce_desc with
    | Ce_var v ->
      Acids_interval.Ce_var v,
      (
        match find_ident env v with
        | It_scal (Is_inter it) -> it
        | It_scal Is_top -> bad_annot ce.ce_loc v
        | It_prod _ -> invalid_arg "ill typed"
      )

    | Ce_pword w ->
      let w =
        let type_fun = type_pword_exp env in
        Ast_misc.map_upword type_fun type_fun w
      in
      let w, ty_l =
        let pword_exp_type_inter (pwe, ty) acc = pwe, ty :: acc in
        Ast_misc.mapfold_upword
          pword_exp_type_inter
          (fun (pw, _) ty_l -> pw, ty_l)
          w
          []
      in
      Acids_interval.Ce_pword w, Utils.fold_left_1 Interval.join ty_l

    | Ce_equal (ce, e) ->
      let ce = type_clock_exp env ce in
      let e = type_exp env e in
      Acids_interval.Ce_equal (ce, e), Interval.bool

    | Ce_iter ce ->
      let ce = type_clock_exp env ce in
      Acids_interval.Ce_iter ce, iter (clock_exp_type ce)
  in
  {
    Acids_interval.ce_desc = ced;
    Acids_interval.ce_loc = ce.ce_loc;
    Acids_interval.ce_info = clock_exp_annotate ce ty;
  }

and type_pword_exp env pwe =
  let pwed, it =
    match pwe.pwe_desc with
    | Pwe_var v ->
      (
        match find_ident env v with
        | It_scal (Is_inter it) -> Acids_interval.Pwe_var v, it
        | _ -> bad_annot pwe.pwe_loc v
      )
    | Pwe_econstr ec ->
      let it = type_econstr env (Data_types.Ty_scal pwe.pwe_info#pwi_data) ec in
      Acids_interval.Pwe_econstr ec, it
    | Pwe_fword i_l ->
      let it_l = List.map Interval.singleton i_l in
      let it = Utils.fold_left_1 Interval.join it_l in
      Acids_interval.Pwe_fword i_l, it
  in
  {
    Acids_interval.pwe_desc = pwed;
    Acids_interval.pwe_loc = pwe.pwe_loc;
    Acids_interval.pwe_info = pword_exp_annotate pwe it;
  },
  it

and type_block block env =
  let env = List.fold_left enrich_env_eq env block.b_body in

  let type_eq eq =
    let p = type_pat env eq.eq_lhs in
    let e = type_exp env eq.eq_rhs in
    let ty_e = exp_type e in
    let ty_p = pat_type p in
    if not (subset ty_e ty_p) then not_subset_pat p e;
    {
      Acids_interval.eq_lhs = p;
      Acids_interval.eq_rhs = e;
      Acids_interval.eq_loc = eq.eq_loc;
      Acids_interval.eq_info = eq.eq_info;
    }
  in
  {
    Acids_interval.b_body = List.map type_eq block.b_body;
    Acids_interval.b_loc = block.b_loc;
    Acids_interval.b_info = block.b_info;
  },
  env

let type_node_def env nd =
  let env = reset_idents env in
  let env = enrich_env_pat env nd.n_input in
  let input = type_pat env nd.n_input in
  let body = type_exp env nd.n_body in
  let isig = { input = pat_type input; output = exp_type body; } in
  add_local_signature env nd.n_name isig,
  {
    Acids_interval.n_name = nd.n_name;
    Acids_interval.n_input = input;
    Acids_interval.n_body = body;
    Acids_interval.n_pragma = nd.n_pragma;
    Acids_interval.n_static = nd.n_static;
    Acids_interval.n_loc = nd.n_loc;
    Acids_interval.n_info = node_annotate nd isig;
  }

let type_node_decl env ndecl =
  add_local_signature env ndecl.decl_name ndecl.decl_interv,
  {
    Acids_interval.decl_name = ndecl.decl_name;
    Acids_interval.decl_data = ndecl.decl_data;
    Acids_interval.decl_static = ndecl.decl_static;
    Acids_interval.decl_interv = ndecl.decl_interv;
    Acids_interval.decl_clock = ndecl.decl_clock;
    Acids_interval.decl_loc = ndecl.decl_loc;
  }

let type_type_def env tdef =
  add_type_constructors env tdef.ty_name tdef.ty_body,
  {
    Acids_interval.ty_name = tdef.ty_name;
    Acids_interval.ty_body = tdef.ty_body;
    Acids_interval.ty_loc = tdef.ty_loc;
  }

let type_phrase env phr =
  match phr with
  | Phr_node_def nd ->
    let env, nd = type_node_def env nd in
    env, Acids_interval.Phr_node_def nd
  | Phr_node_decl ndecl ->
    let env, ndecl = type_node_decl env ndecl in
    env, Acids_interval.Phr_node_decl ndecl
  | Phr_type_def tdef ->
    let env, tdef = type_type_def env tdef in
    env, Acids_interval.Phr_type_def tdef

let type_file file =
  let env = initial_typing_env file.f_info#interfaces in
  let _, body = Utils.mapfold_left type_phrase env file.f_body in
  {
    Acids_interval.f_name = file.f_name;
    Acids_interval.f_imports = file.f_imports;
    Acids_interval.f_info = file.f_info;
    Acids_interval.f_body = body;
  }

let type_file
    ctx
    (file : < interfaces : Interface.t Names.ShortEnv.t > Acids_typed.file) =
  ctx, type_file file

(** {2 Putting it all together} *)

let type_ =
  let open Pass_manager in
  P_transform
    (Frontend_utils.make_transform
       ~print_out:Acids_interval.print_file
       "interval_typing"
       type_file)


