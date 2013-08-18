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

open Acids_prespec

(** {2 Errors} *)

type error =
  | Non_cond_declared_var of Loc.t * Ident.t
  | Non_interval_annotated_var of Loc.t * Ident.t
  | Negative_bounds of Acids_spec.clock_exp * Interval.t
  | Non_exhaustive_pattern_match of Loc.t * Ast_misc.econstr
  | Duplicate_pattern_match of Loc.t * Ast_misc.econstr

exception Annotation_error of error

let print_error fmt err =
  match err with
  | Non_cond_declared_var (l, id) ->
    Format.fprintf fmt
      "%aVariable %a must be of type cond but has not been declared so"
      Loc.print l
      Ident.print id
  | Non_interval_annotated_var (l, id) ->
    Format.fprintf fmt
      "%aVariable %a has not been annotated with bounds"
      Loc.print l
      Ident.print id
  | Negative_bounds (ce, it) ->
    Format.fprintf fmt
      "%aClock expression %a has negative bounds %a"
      Loc.print ce.Acids_spec.ce_loc
      Acids_spec.print_clock_exp ce
      Interval.print it
  | Non_exhaustive_pattern_match (l, ec) ->
    Format.fprintf fmt
      "%aThis pattern-matching is not exhaustive (for example, %a is unmatched)"
      Loc.print l
      Ast_misc.print_econstr ec
  | Duplicate_pattern_match (l, ec) ->
    Format.fprintf fmt
      "%aThe pattern %a appears several times in this matching"
      Loc.print l
      Ast_misc.print_econstr ec

let non_cond_declared_var l id =
  raise (Annotation_error (Non_cond_declared_var (l, id)))

let non_interval_annotated_var l id =
  raise (Annotation_error (Non_interval_annotated_var (l, id)))

let negative_bounds ce it =
  raise (Annotation_error (Negative_bounds (ce, it)))

let non_exhaustive_pattern_match l ec =
  raise (Annotation_error (Non_exhaustive_pattern_match (l, ec)))

let duplicate_pattern_match l ec =
  raise (Annotation_error (Duplicate_pattern_match (l, ec)))

(** {2 Environment} *)

type env =
  {
    intf_env : Interface.t Names.ModEnv.t;
    env : Ast_misc.spec list Ident.Env.t;
    constrs : Names.shortname list Names.ShortEnv.t;
    pword_specs : ((Int.t, Int.t) Tree_word.t * Interval.t) Names.ShortEnv.t;
  }

let initial_env intf_env =
  {
    intf_env = intf_env;
    env = Ident.Env.empty;
    constrs = Names.ShortEnv.empty;
    pword_specs = Names.ShortEnv.empty;
  }

let add_type_def env td =
  { env with constrs = Names.ShortEnv.add td.ty_name td.ty_body env.constrs }

let add_spec id specs env =
  { env with env = Ident.Env.add id specs env.env; }

let find_spec env v = try Ident.Env.find v env.env with Not_found -> []

let find_pword_specs env ln =
  let open Names in
  match ln.modn with
  | LocalModule ->
    ShortEnv.find ln.shortn env.pword_specs
  | Module modn ->
    let intf = ModEnv.find (Module modn) env.intf_env in
    let pw = Interface.((find_pword intf ln.shortn).pi_value) in
    let p = Tree_word.map_upword Ast_misc.int_of_econstr (fun x -> x) pw in
    let l, u = Ast_misc.bounds_of_int_pword p in
    p, Interval.make l u

let add_pword_spec env pn pw =
  let get se = Ast_misc.int_of_econstr se.Acids_spec.se_desc in
  let p = Tree_word.map_upword get get pw in
  let l, u = Ast_misc.bounds_of_int_pword p in
  let pword_specs =
    Names.ShortEnv.add pn (p, Interval.make l u) env.pword_specs
  in
  { env with pword_specs = pword_specs; }

(** {2 Exhaustiveness checking for patterns} *)

let check_exhaustiveness env loc ty it present_cases =
  let open Ast_misc in
  let open Data_types in
  let open Names in

  (* TODO use a set-like datastructure *)

  let econstr_list_of_shortname_list modul n_l =
    let make rank n =
      rank + 1, Ec_constr ({ modn = modul; shortn = n; }, Int.of_int rank)
    in
    let _, ec_l = Utils.mapfold_left make 0 n_l in
    ec_l
  in

  let module S =
        Set.Make(
          struct
            type t = Ast_misc.econstr
            let compare = Ast_misc.econstr_compare
          end) in

  let all_cases =
    match ty with
    | Tys_bool -> [Ec_bool false; Ec_bool true]
    | Tys_float -> invalid_arg "ill-typed"
    | Tys_user { modn = LocalModule; shortn = shortn; } ->
      let n_l = Names.ShortEnv.find shortn env.constrs in
      econstr_list_of_shortname_list LocalModule n_l
    | Tys_user { modn = Module modn; shortn = shortn; } ->
      let intf = Names.ModEnv.find (Module modn) env.intf_env in
      let n_l = Interface.find_constructors_of_type intf shortn in
      econstr_list_of_shortname_list (Module modn) n_l
    | Tys_int ->
      let open Int in
      let l = to_int it.Interval.l in
      let u = to_int it.Interval.u in
      List.map (fun i -> Ec_int (of_int i)) (Utils.range l u)
  in

  let all_cases =
    List.fold_left (fun set case -> S.add case set) S.empty all_cases
  in

  let rec check remaining_cases present_cases =
    match present_cases with
    | [] ->
      if not (S.is_empty remaining_cases)
      then non_exhaustive_pattern_match loc (S.min_elt remaining_cases)
      else ()
    | case :: present_cases ->
      if not (S.mem case remaining_cases)
      then duplicate_pattern_match loc case
      else check (S.remove case remaining_cases) present_cases
  in
  check all_cases present_cases

(** {2 AST walking} *)

let trad_spec spec =
  match spec.s_desc with
  | Unspec -> Ast_misc.Unspec
  | Interval (l, u) ->
    let l = Ast_misc.get_int l.se_desc in
    let u = Ast_misc.get_int u.se_desc in
    Ast_misc.Interval (Interval.make l u)
  | Word p ->
    let get_int se = Ast_misc.get_int se.se_desc in
    Ast_misc.Word (Tree_word.map_upword get_int get_int p)

let rec enrich_env_with_pattern env p =
  match p.p_desc with
  | P_var id ->
    let rec check_no_cond loc id ty =
      let open Data_types in
      match ty with
      | Ty_scal _ | Ty_var _ -> ()
      | Ty_cond _ -> non_cond_declared_var loc id
      | Ty_prod ty_l -> List.iter (check_no_cond loc id) ty_l
    in
    check_no_cond p.p_loc id p.p_info#pi_data; env
  | P_tuple p_l -> List.fold_left enrich_env_with_pattern env p_l
  | P_clock_annot (p, _) | P_type_annot (p, _) | P_spec_annot (p, _) ->
    enrich_env_with_pattern env p
  | P_split pw ->
    Tree_word.fold_upword
      (fun p env -> enrich_env_with_pattern env p)
      (fun _ env -> env)
      pw
      env

let specs_of_upword pw =
  let p =
    let get se = Ast_misc.int_of_econstr se.se_desc in
    Tree_word.map_upword get get pw
  in

  let l, u = Ast_misc.bounds_of_int_pword p in
  p, Interval.make l u

let rec annot_clock_exp env ce =
  let ced, it, specs =
    match ce.ce_desc with
    | Ce_condvar v ->
      let specs = find_spec env v in
      let rec find_it specs =
        match specs with
        | [] -> non_interval_annotated_var ce.ce_loc v
        | Ast_misc.Interval it :: _ -> it
        | _ :: specs -> find_it specs
      in
      Acids_spec.Ce_condvar v, find_it specs, specs

    | Ce_pword pd ->
      let p, it, desc =
        match pd with
        | Pd_lit pw ->
          let p, it = specs_of_upword pw in

          let pw =
            Tree_word.map_upword
              (annot_static_exp env)
              (annot_static_exp env)
              pw
          in

          p, it, Acids_spec.Pd_lit pw

        | Pd_global ln ->
          let p, it = find_pword_specs env ln in
          p, it, Acids_spec.Pd_global ln
      in
      Acids_spec.Ce_pword desc, it, [Ast_misc.Interval it; Ast_misc.Word p]

    | Ce_equal (ce, se) ->
      let ce, it, specs = annot_clock_exp env ce in
      let se = annot_static_exp env se in

      let i_se = Ast_misc.int_of_econstr se.Acids_spec.se_desc in

      let rec update_specs acc specs =
        let open Ast_misc in
        match specs with
        | [] -> acc
        | (Interval _ | Unspec) :: specs -> update_specs acc specs
        | Word p :: specs ->
          let mk_eq i = Int.of_bool (Int.equal i i_se) in
          update_specs
            (Word (Tree_word.map_upword mk_eq (fun i -> i) p) :: acc)
            specs
      in

      Acids_spec.Ce_equal (ce, se), it, update_specs [] specs
  in

  let ce =
    {
      Acids_spec.ce_desc = ced;
      Acids_spec.ce_info =
        object
          method ci_data = ce.ce_info#ci_data
          method ci_bounds = it
          method ci_specs = specs;
        end;
      Acids_spec.ce_loc = ce.ce_loc;
    }
  in

  if it.Interval.l < Int.zero then negative_bounds ce it else (ce, it, specs)

and annot_static_exp _ se =
  let i = Ast_misc.int_of_econstr se.se_desc in
  {
    Acids_spec.se_desc = se.se_desc;
    Acids_spec.se_loc = se.se_loc;
    Acids_spec.se_info =
      object
        method pwi_data = se.se_info#pwi_data
        method pwi_spec = [Ast_misc.Interval (Interval.singleton i)]
      end;
  }

and annot_exp env e =
  let ed =
    match e.e_desc with
    | E_var v ->
      Acids_spec.E_var v
    | E_const c ->
      Acids_spec.E_const c
    | E_fst e ->
      let e = annot_exp env e in
      Acids_spec.E_fst e
    | E_snd e ->
      let e = annot_exp env e in
      Acids_spec.E_snd e
    | E_tuple e_l ->
      let e_l = List.map (annot_exp env) e_l in
      Acids_spec.E_tuple e_l
    | E_fby (e1, e2) ->
      let e1 = annot_exp env e1 in
      let e2 = annot_exp env e2 in
      Acids_spec.E_fby (e1, e2)
    | E_ifthenelse (e1, e2, e3) ->
      let e1 = annot_exp env e1 in
      let e2 = annot_exp env e2 in
      let e3 = annot_exp env e3 in
      Acids_spec.E_ifthenelse (e1, e2, e3)
    | E_app (app, e) ->
      let app = annot_app env app in
      let e = annot_exp env e in
      Acids_spec.E_app (app, e)
    | E_where (e, block) ->
      let block, env = annot_block env block in
      let e = annot_exp env e in
      Acids_spec.E_where (e, block)
    | E_when (e, ce) ->
      let e = annot_exp env e in
      let ce, _, _ = annot_clock_exp env ce in
      Acids_spec.E_when (e, ce)
    | E_split (ce, e', ec_l) ->
      let ce, _, _ = annot_clock_exp env ce in
      let e' = annot_exp env e' in
      check_exhaustiveness
        env
        e.e_loc
        ce.Acids_spec.ce_info#ci_data
        ce.Acids_spec.ce_info#ci_bounds
        ec_l;
      Acids_spec.E_split (ce, e', ec_l)
    | E_bmerge (ce, e1, e2) ->
      let ce, _, _ = annot_clock_exp env ce in
      let e1 = annot_exp env e1 in
      let e2 = annot_exp env e2 in
      Acids_spec.E_bmerge (ce, e1, e2)
    | E_merge (ce, c_l) ->
      let annot_clause ec =
        {
          Acids_spec.c_sel = ec.c_sel;
          Acids_spec.c_body = annot_exp env ec.c_body;
          Acids_spec.c_loc = ec.c_loc;
        }
      in
      let ce, _, _ = annot_clock_exp env ce in
      let c_l = List.map annot_clause c_l in
      check_exhaustiveness
        env
        e.e_loc
        ce.Acids_spec.ce_info#ci_data
        ce.Acids_spec.ce_info#ci_bounds
        (List.map (fun c -> c.Acids_spec.c_sel) c_l);
      Acids_spec.E_merge (ce, c_l)
    | E_valof ce ->
      let ce, _, _ = annot_clock_exp env ce in
      Acids_spec.E_valof ce
    | E_clock_annot (e, cka) ->
      let e = annot_exp env e in
      let cka = annot_clock_annot env cka in
      Acids_spec.E_clock_annot (e, cka)
    | E_type_annot (e, tya) ->
      let e = annot_exp env e in
      Acids_spec.E_type_annot (e, tya)
    | E_spec_annot (e, spec) ->
      let e = annot_exp env e in
      let spec = annot_spec env spec in
      Acids_spec.E_spec_annot (e, spec)
    | E_dom (e, dom) ->
      let e = annot_exp env e in
      let dom = annot_dom env dom in
      Acids_spec.E_dom (e, dom)
    | E_buffer (e, bu) ->
      let e = annot_exp env e in
      let bu = annot_buffer env bu in
      Acids_spec.E_buffer (e, bu)
  in
  {
    Acids_spec.e_desc = ed;
    Acids_spec.e_loc = e.e_loc;
    Acids_spec.e_info = e.e_info;
  }

and annot_app _ app =
  {
    Acids_spec.a_op = app.a_op;
    Acids_spec.a_loc = app.a_loc;
    Acids_spec.a_info = app.a_info;
  }

and annot_clock_annot env cka =
  match cka with
  | Ca_var id -> Acids_spec.Ca_var id
  | Ca_on (cka, ce) ->
    let cka = annot_clock_annot env cka in
    let ce, _, _ = annot_clock_exp env ce in
    Acids_spec.Ca_on (cka, ce)

and annot_spec env spec =
  let sd =
    match spec.s_desc with
    | Unspec -> Acids_spec.Unspec
    | Word p ->
      let p =
        Tree_word.map_upword (annot_static_exp env) (annot_static_exp env) p
      in
      Acids_spec.Word p
    | Interval (l, u) ->
      let l = annot_static_exp env l in
      let u = annot_static_exp env u in
      Acids_spec.Interval (l, u)
  in
  {
    Acids_spec.s_desc = sd;
    Acids_spec.s_loc = spec.s_loc;
  }

and annot_pattern env p =
  let pd =
    match p.p_desc with
    | P_var v ->
      Acids_spec.P_var v
    (* | P_condvar (v, specs) -> *)
    (*   let specs = List.map (annot_spec env) specs in *)
    (*   Acids_spec.P_condvar (v, specs) *)
    | P_tuple p_l ->
      Acids_spec.P_tuple (List.map (annot_pattern env) p_l)
    | P_clock_annot (p, cka) ->
      let p = annot_pattern env p in
      let cka = annot_clock_annot env cka in
      Acids_spec.P_clock_annot (p, cka)
    | P_type_annot (p, tya) ->
      let p = annot_pattern env p in
      Acids_spec.P_type_annot (p, tya)
    | P_spec_annot (p, spec) ->
      let p = annot_pattern env p in
      let spec = annot_spec env spec in
      Acids_spec.P_spec_annot (p, spec)
    | P_split w ->
      let w =
        Tree_word.map_upword (annot_pattern env) (annot_static_exp env) w
      in
      Acids_spec.P_split w
  in
  {
    Acids_spec.p_desc = pd;
    Acids_spec.p_loc = p.p_loc;
    Acids_spec.p_info = p.p_info;
  }

and annot_block env block =
  let enrich env eq =
    match eq.eq_desc with
    | Eq_plain (lhs, _) -> enrich_env_with_pattern env lhs
    | Eq_condvar (lhs, specs, rhs) ->
      let specs = List.map trad_spec specs in
      let specs =
        let open Data_types in
        match rhs.e_info#ei_data with
        | Ty_scal Tys_bool -> Ast_misc.Interval Interval.bool :: specs
        | _ -> specs
      in
      add_spec lhs specs env
  in
  let env = List.fold_left enrich env block.b_body in
  {
    Acids_spec.b_body = List.map (annot_eq env) block.b_body;
    Acids_spec.b_loc = block.b_loc;
    Acids_spec.b_info = block.b_info;
  },
  env

and annot_eq env eq =
  let desc =
    match eq.eq_desc with
    | Eq_plain (lhs, rhs) ->
      Acids_spec.Eq_plain (annot_pattern env lhs, annot_exp env rhs)
    | Eq_condvar (lhs, specs, rhs) ->
      let specs = List.map (annot_spec env) specs in
      Acids_spec.Eq_condvar (lhs, specs, annot_exp env rhs)
  in
  {
    Acids_spec.eq_desc = desc;
    Acids_spec.eq_loc = eq.eq_loc;
    Acids_spec.eq_info = eq.eq_info;
  }

and annot_dom env dom =
  {
    Acids_spec.d_base_clock =
      Utils.map_opt (annot_clock_annot env) dom.d_base_clock;
    Acids_spec.d_par = dom.d_par;
    Acids_spec.d_info = dom.d_info;
  }

and annot_buffer _ bu =
  {
    Acids_spec.bu_info = bu.bu_info;
  }

let annot_node_def env nd =
  let env = enrich_env_with_pattern env nd.n_input in
  let input = annot_pattern env nd.n_input in
  let body = annot_exp env nd.n_body in
  {
    Acids_spec.n_name = nd.n_name;
    Acids_spec.n_input = input;
    Acids_spec.n_body = body;
    Acids_spec.n_pragma = nd.n_pragma;
    Acids_spec.n_static = nd.n_static;
    Acids_spec.n_loc = nd.n_loc;
    Acids_spec.n_info = nd.n_info;
  }

let annot_node_decl _ ndecl =
  {
    Acids_spec.decl_name = ndecl.decl_name;
    Acids_spec.decl_data = ndecl.decl_data;
    Acids_spec.decl_static = ndecl.decl_static;
    Acids_spec.decl_clock = ndecl.decl_clock;
    Acids_spec.decl_loc = ndecl.decl_loc;
  }

let annot_type_def _ tdef =
  {
    Acids_spec.ty_name = tdef.ty_name;
    Acids_spec.ty_body = tdef.ty_body;
    Acids_spec.ty_loc = tdef.ty_loc;
  }

let annot_static_def env sd =
  {
    Acids_spec.sd_name = sd.sd_name;
    Acids_spec.sd_body = annot_exp env sd.sd_body;
    Acids_spec.sd_loc = sd.sd_loc;
  }

let annot_pword_def env pd =
  let body =
    Tree_word.map_upword
      (annot_static_exp env)
      (annot_static_exp env)
      pd.pd_body
  in
  {
    Acids_spec.pd_name = pd.pd_name;
    Acids_spec.pd_body = body;
    Acids_spec.pd_loc = pd.pd_loc;
  },
  add_pword_spec env pd.pd_name body

let annot_ty_phrase env phr =
  match phr with
  | Phr_node_def nd ->
    env, Acids_spec.Phr_node_def (annot_node_def env nd)
  | Phr_node_decl nd ->
    env, Acids_spec.Phr_node_decl (annot_node_decl env nd)
  | Phr_type_def td ->
    env, Acids_spec.Phr_type_def (annot_type_def env td)
  | Phr_static_def sd ->
    env, Acids_spec.Phr_static_def (annot_static_def env sd)
  | Phr_pword_def pd ->
    let pd, env = annot_pword_def env pd in
    env, Acids_spec.Phr_pword_def pd

let annot_file file =
  let interfaces = Names.mod_env_of_short_env file.f_info#interfaces in
  let env = initial_env interfaces in
  let _, body = Utils.mapfold_left annot_ty_phrase env file.f_body in
  {
    Acids_spec.f_name = file.f_name;
    Acids_spec.f_imports = file.f_imports;
    Acids_spec.f_info = file.f_info;
    Acids_spec.f_body = body;
  }

(** {2 Putting it all together} *)

let annot_file
    ctx
    (file :
     <
       interfaces : Interface.env;
       static_nodes : Acids_static.node_def list
     > Acids_prespec.file) =
  ctx, annot_file file

let annot =
  let open Pass_manager in
  P_transform
    (Frontend_utils.make_transform
       ~print_out:Acids_spec.print_file
       "spec_annot"
       annot_file)
