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

let non_cond_declared_var l id =
  raise (Annotation_error (Non_cond_declared_var (l, id)))

let non_interval_annotated_var l id =
  raise (Annotation_error (Non_interval_annotated_var (l, id)))

let negative_bounds ce it =
  raise (Annotation_error (Negative_bounds (ce, it)))

(** {2 Environment} *)

type env =
  {
    intf_env : Interface.env;
    env : Ast_misc.spec list Ident.Env.t;
  }

let initial_env intf_env =
  {
    intf_env = intf_env;
    env = Ident.Env.empty;
  }

let add_spec id specs env =
  { env with env = Ident.Env.add id specs env.env; }

let find_spec env v = try Ident.Env.find v env.env with Not_found -> []

let find_constructor_rank env cstr =
  assert false (* TODO *)

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
  | P_condvar (id, specs) ->
    let specs = List.map trad_spec specs in
    let specs =
      let open Data_types in
      match p.p_info#pi_data with
      | Ty_scal Tys_bool -> Ast_misc.Interval Interval.bool :: specs
      | _ -> specs
    in
    add_spec id specs env
  | P_tuple p_l -> List.fold_left enrich_env_with_pattern env p_l
  | P_clock_annot (p, _) | P_type_annot (p, _) | P_spec_annot (p, _) ->
    enrich_env_with_pattern env p
  | P_split pw ->
    Tree_word.fold_upword
      (fun p env -> enrich_env_with_pattern env p)
      (fun _ env -> env)
      pw
      env

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

    | Ce_pword p ->
      (* Compute bounds *)
      let it =
        (* We now that there is no negative integer in p (TODO ugly, invar) *)
        let l = ref (Int.of_int (- 1)) in
        let u = ref (Int.of_int (- 1)) in
        let check se =
          assert (!l >= Int.zero || !u < Int.zero);
          let i = Ast_misc.get_int se.se_desc in
          if !l < Int.zero
          then (l := i; u := i)
          else (l := Int.min !l i; u := Int.max !u i)
        in
        Ast_misc.iter_upword check (fun _ -> ()) p;
        Interval.make !l !u
      in

      let pw =
        Tree_word.map_upword (annot_static_exp env) (annot_static_exp env) p
      in

      let p =
        let get se = Ast_misc.get_int se.Acids_spec.se_desc in
        Tree_word.map_upword get get pw
      in

      Acids_spec.Ce_pword pw, it, [Ast_misc.Interval it; Ast_misc.Word p]

    | Ce_equal (ce, se) ->
      let ce, it, specs = annot_clock_exp env ce in
      let se = annot_static_exp env se in

      let i_se =
        match se.Acids_spec.se_desc with
        | Ast_misc.Ec_int i -> i
        | Ast_misc.Ec_bool b -> Int.of_bool b
        | Ast_misc.Ec_constr cstr -> find_constructor_rank env cstr
      in

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
          method ci_interv = it
          method ci_spec = specs;
        end;
      Acids_spec.ce_loc = ce.ce_loc;
    }
  in

  if it.Interval.l < Int.zero then negative_bounds ce it else (ce, it, specs)

and annot_static_exp env se =
  let i =
    let open Ast_misc in
    match se.se_desc with
    | Ec_bool b -> Int.of_bool b
    | Ec_int i -> i
    | Ec_constr cstr -> find_constructor_rank env cstr
  in
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
    | E_where _ -> assert false (* TODO *)
    | E_when (e, ce) ->
      let e = annot_exp env e in
      let ce, _, _ = annot_clock_exp env ce in
      Acids_spec.E_when (e, ce)
    | E_split (ce, e, ec_l) ->
      let ce, _, _ = annot_clock_exp env ce in
      let e = annot_exp env e in
      Acids_spec.E_split (ce, e, ec_l)
    | E_bmerge (ce, e1, e2) ->
      let ce, _, _ = annot_clock_exp env ce in
      let e1 = annot_exp env e1 in
      let e2 = annot_exp env e2 in
      Acids_spec.E_bmerge (ce, e1, e2)
    | E_merge (ce, ec_l) ->
      let annot_clause ec =
        {
          Acids_spec.c_sel = ec.c_sel;
          Acids_spec.c_body = annot_exp env ec.c_body;
          Acids_spec.c_loc = ec.c_loc;
        }
      in
      let ce, _, _ = annot_clock_exp env ce in
      Acids_spec.E_merge (ce, List.map annot_clause ec_l)
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
    | E_buffer e ->
      let e = annot_exp env e in
      Acids_spec.E_buffer e
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
    | P_condvar (v, specs) ->
      let specs = List.map (annot_spec env) specs in
      Acids_spec.P_condvar (v, specs)
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
  let enrich env eq = enrich_env_with_pattern env eq.eq_lhs in
  let env = List.fold_left enrich env block.b_body in
  {
    Acids_spec.b_body = List.map (annot_eq env) block.b_body;
    Acids_spec.b_loc = block.b_loc;
    Acids_spec.b_info = block.b_info;
  },
  env

and annot_eq env eq =
  let lhs = annot_pattern env eq.eq_lhs in
  let rhs = annot_exp env eq.eq_rhs in
  {
    Acids_spec.eq_lhs = lhs;
    Acids_spec.eq_rhs = rhs;
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

let annot_ty_phrase env phr =
  match phr with
  | Phr_node_def nd ->
    Acids_spec.Phr_node_def (annot_node_def env nd)
  | Phr_node_decl nd ->
    Acids_spec.Phr_node_decl (annot_node_decl env nd)
  | Phr_type_def td ->
    Acids_spec.Phr_type_def (annot_type_def env td)

let annot_file file =
  let env = initial_env file.f_info#interfaces in
  {
    Acids_spec.f_name = file.f_name;
    Acids_spec.f_imports = file.f_imports;
    Acids_spec.f_info = file.f_info;
    Acids_spec.f_body = List.map (annot_ty_phrase env) file.f_body;
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
