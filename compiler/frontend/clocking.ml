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

open Clock_types
open Acids_preclock
open PreTySt
open PreTy

(** {2 Low-level utilities} *)

let get_int se =
  let open Info in
  let open Ast_misc in
  match se.se_desc with
  | Se_econstr (Ec_int i) -> i
  | Se_econstr (Ec_bool _ | Ec_constr _) | Se_fword _ -> invalid_arg "psplit_length"

(** {2 Exceptions} *)

type error =
  | Could_not_unify of Loc.t * VarTy.t * VarTy.t

exception Clocking_error of error

let print_error fmt err =
  match err with
  | Could_not_unify (loc, ct1, ct2) ->
    Format.fprintf fmt "%aCould not unify clock type @[%a@] with @[%a@]"
      Loc.print loc
      VarTy.print ct1
      VarTy.print ct2

(** {2 Utilities} *)

let reset_st, fresh_st =
  let r = ref 0 in
  (fun () -> r := 0),
  (fun () ->
    let v = !r in
    incr r;
    Pst_var { VarTySt.v_id = v; VarTySt.v_link = None; })

let reset_ty, fresh_ty =
  let r = ref 0 in
  (fun () -> r := 0),
  (fun () ->
    let v = !r in
    incr r;
    Pct_var { VarTy.v_id = v; VarTy.v_link = None; })

(** {2 Environments} *)

type env =
  {
    intf_env : Interface.env;
    local_nodes : Clock_types.clock_sig Names.ShortEnv.t;
    mutable ck_vars : VarTySt.t Utils.Int_map.t;
  }

let initial_env intf_env =
  {
    intf_env = intf_env;
    local_nodes = Names.ShortEnv.empty;
    ck_vars = Utils.Int_map.empty;
  }

let reset_env env = { env with ck_vars = Utils.Int_map.empty; }

let find_ck_var env v =
  try Utils.Int_map.find v env.ck_vars
  with Not_found ->
    let t = fresh_st () in
    env.ck_vars <- Utils.Int_map.add v t env.ck_vars;
    t

let add_local_node env name csig =
  { env with local_nodes = Names.ShortEnv.add name csig env.local_nodes; }

let find_node_signature env ln =
  let open Names in
  match ln.modn with
  | LocalModule -> ShortEnv.find ln.shortn env.local_nodes
  | Module modn ->
    let intf = ShortEnv.find modn env.intf_env in
    Interface.clock_signature_of_node_item (Interface.find_node intf ln.shortn)

(** {2 Utility functions} *)

let singleton_ctx v =
  let ty = fresh_ty () in
  ty, Ident.Env.singleton v ty

let merge_ctx loc ctx1 ctx2 constrs =
  let unify_occ id ty (ctx, constrs) =
    try
      let ty' = Ident.Env.find id ctx1 in
      ctx, { loc = loc; desc = Tc_equal (ty, ty') } :: constrs
    with Not_found ->
      Ident.Env.add id ty ctx, constrs
  in
  Ident.Env.fold unify_occ ctx2 (ctx1, constrs)

let unify loc t1 t2 constrs =
  { loc = loc; desc = Tc_equal (t1, t2); } :: constrs

let prod_ty t_l = Pct_prod t_l

let trad_static_exp se =
  match se.se_desc with
  | Info.Se_econstr ec -> [ec]
  | Info.Se_fword i_l -> List.map (fun i -> Ast_misc.Ec_int i) i_l

let trad_static_exp_int se =
  match trad_static_exp se with
  | [Ast_misc.Ec_int i] -> i
  | _ -> invalid_arg "trad_static_exp_int"

let trad_static_exp_econstr se =
  match trad_static_exp se with
  | [ec] -> ec
  | _ -> invalid_arg "trad_static_exp_econstr" (* TODO *)

let rec trad_clock_exp ce =
  match ce.ce_desc with
  | Ce_var v ->
    Clock_types.Ce_var v
  | Ce_pword pw ->
    let pw = Ast_misc.map_upword trad_static_exp trad_static_exp_int pw in
    Clock_types.Ce_pword pw
  | Ce_equal (ce, se) ->
    Clock_types.Ce_equal (trad_clock_exp ce, trad_static_exp_econstr se)
  | Ce_iter ce ->
    Clock_types.Ce_iter (trad_clock_exp ce)

let rec int_ptree_of_ptree current pt =
  let open Ast_misc in
  match pt with
  | Leaf _ -> Int.succ current, Leaf ([Ec_int current])
  | Power (pt, se) ->
    let current, pt = int_ptree_of_ptree current pt in
    current, Power (pt, get_int se)
  | Concat pt_l ->
    let current, pt_l = Utils.mapfold_left int_ptree_of_ptree current pt_l in
    current, Concat pt_l

let int_pword_of_pword pw =
  let open Ast_misc in
  let current, u = int_ptree_of_ptree Int.zero pw.u in
  let _, v = int_ptree_of_ptree current pw.v in
  Clock_types.Ce_pword { u = u; v = v; }

let rec psplit_length pt =
  let open Ast_misc in
  let open Info in
  match pt with
  | Leaf _ -> Int.of_int 1
  | Power (pt, se) ->
    (
      match se.se_desc with
      | Se_econstr (Ec_int i) ->
        Int.mul i (psplit_length pt)
      | Se_econstr (Ec_bool _ | Ec_constr _) | Se_fword _ ->
        invalid_arg "psplit_length"
    )
  | Concat p_l ->
    List.fold_left (fun l pt -> Int.add l (psplit_length pt)) Int.zero p_l

let ty_of_st st = Pct_stream st

let st_of_ty loc t (ctx, constrs) =
  let st = fresh_st () in
  st, (ctx, { loc = loc; desc = Tc_equal (ty_of_st st, t); } :: constrs)

let on_ty loc t ce acc =
  let st, acc = st_of_ty loc t acc in
  ty_of_st (Pst_on (st, ce)), acc

let adaptable_tys loc (ctx, constrs) =
  let st = fresh_st () in
  let st' = fresh_st () in
  let constr = { loc = loc; desc = Tc_adapt (st, st'); } in
  ty_of_st st, ty_of_st st', (ctx, constr :: constrs)

let sampled_ty loc ty cce ec acc =
  on_ty loc ty (Clock_types.Ce_equal (cce, ec)) acc

let rec unalias_st st =
  match st with
  | PreTySt.Pst_var { VarTySt.v_link = Some st; } -> unalias_st st
  | _ -> st

let rec unalias_ty ty =
  match ty with
  | PreTy.Pct_var { VarTy.v_link = Some ty; } -> unalias_ty ty
  | _ -> ty

(** {2 High-level utilities} *)

module A =
struct
  type new_annot =
    | Exp of VarTy.t
    | ClockExp of VarTySt.t
    | Node of Clock_types.clock_sig
    | App of (int * VarTySt.t) list

  let print_new_annot fmt na =
    match na with
    | Exp ty -> VarTy.print fmt ty
    | ClockExp st -> VarTySt.print fmt st
    | Node csig ->
      Clock_types.print_sig fmt csig
    | App inst ->
      let print_binding fmt (i, ty) =
        Format.fprintf fmt "%d -> %a" i VarTySt.print ty
      in
      Format.fprintf fmt "@[%a@]"
        (Utils.print_list_r print_binding ",") inst
end

module ANN_INFO = Acids_utils.MakeAnnot(Acids_preclock)(A)
module M = Acids.Make(ANN_INFO)

let annotate_exp info ty =
  ANN_INFO.annotate info (A.Exp ty)

let annotate_clock_exp info st =
  ANN_INFO.annotate info (A.ClockExp st)

let annotate_node info csig =
  ANN_INFO.annotate info (A.Node csig)

let annotate_app info app =
  ANN_INFO.annotate info (A.App app)

let annotate_dummy info =
  let dummy_sch = PreTy.Pct_var { VarTy.v_id = -1; VarTy.v_link = None; } in
  ANN_INFO.annotate info (A.Exp dummy_sch)

module MORPH =
struct
  module IN_INFO = M.I
  module OUT_INFO = Acids_clocked.Info

  open ANN_INFO
  open A

  let update_clock_exp_info { new_annot = na; old_annot = info; } =
    match na with
    | Node _ | App _ | Exp _ -> invalid_arg "update_clock_exp_info"
    | ClockExp pst ->
      (
        object
          method ci_data = info#ci_data
          method ci_interv = info#ci_interv
          method ci_static = info#ci_static
          method ci_clock = Clock_types.st_of_pre_st pst
        end
      )

  let update_static_exp_info { new_annot = na; old_annot = info; } =
    match na with
    | Node _ | App _ | Exp _ -> invalid_arg "update_static_exp_info"
    | ClockExp pst ->
      (
        object
          method pwi_data = info#pwi_data
          method pwi_interv = info#pwi_interv
          method pwi_static = info#pwi_static
          method pwi_clock = Clock_types.st_of_pre_st pst
          end
      )

  let update_exp_info { new_annot = na; old_annot = info; } =
    match na with
    | Node _ | App _ | ClockExp _ -> invalid_arg "update_exp_info"
    | Exp pty ->
      object
        method ei_data = info#ei_data
        method ei_interv = info#ei_interv
        method ei_static = info#ei_static
        method ei_clock = Clock_types.ty_of_pre_ty pty
      end

  let update_app_info { new_annot = na; old_annot = (); } =
    match na with
    | Exp _ | Node _ | ClockExp _ -> invalid_arg "update_app_info"
    | App inst ->
      let trad (i, pst) = i, Clock_types.st_of_pre_st pst in
      {
        Acids_clocked.Info.ai_clock_inst = List.map trad inst;
      }

  let update_block_info _ = ()

  let update_pat_info { new_annot = na; old_annot = info; } =
    match na with
    | Node _ | App _ | ClockExp _ -> invalid_arg "update_pat_info"
    | Exp pty ->
      let ty = ty_of_pre_ty pty in
      object
        method pi_data = info#pi_data
        method pi_interv = info#pi_interv
        method pi_static = info#pi_static
        method pi_clock = ty
      end

  let update_eq_info _ = ()

  let update_domain_info _ = ()

  let update_node_info  { new_annot = na; old_annot = info; } =
    match na with
    | Exp _ | App _ | ClockExp _ -> invalid_arg "update_node_info"
    | Node csig ->
      object
        method ni_ctx = info#ni_ctx
        method ni_data = info#ni_data
        method ni_interv = info#ni_interv
        method ni_static = info#ni_static
        method ni_clock = csig
      end
end
module EXTRACT = Acids_utils.MakeMap(M)(Acids_clocked)(MORPH)

(** {2 Clocking itself} *)

let rec clock_var v (ctx, constrs) =
  try Ident.Env.find v ctx, (ctx, constrs)
  with Not_found ->
    let ty = fresh_ty () in
    ty, (Ident.Env.add v ty ctx, constrs)

and clock_clock_exp env ce acc =
  let loc = ce.ce_loc in
  let ced, st, acc =
    match ce.ce_desc with
    | Ce_var v ->
      let ty, acc = clock_var v acc in
      let st, acc = st_of_ty loc ty acc in
      M.Ce_var v, st, acc

    | Ce_pword pw ->
      let st = fresh_st () in
      let pw, acc =
        let expect = expect_static_exp (ty_of_st st) in
        Ast_misc.mapfold_upword expect expect pw acc
      in
      M.Ce_pword pw, st, acc

    | Ce_equal (ce, se) ->
      let (ce, st), acc = clock_clock_exp env ce acc in
      let se, acc = expect_static_exp (ty_of_st st) se acc in
      M.Ce_equal (ce, se), st, acc

    | Ce_iter ce ->
      let (mce, st), acc = clock_clock_exp env ce acc in
      M.Ce_iter mce, Pst_on (st, trad_clock_exp ce), acc
  in
  (
    {
      M.ce_desc = ced;
      M.ce_loc = loc;
      M.ce_info = annotate_clock_exp ce.ce_info st;
    },
    st
  ),
  acc

and expect_clock_exp env expected_st ce (ctx, constrs) =
  let (ce, actual_st), (ctx, constrs) = clock_clock_exp env ce (ctx, constrs) in
  let cstrs =
    unify ce.M.ce_loc (ty_of_st expected_st) (ty_of_st actual_st) constrs
  in
  ce, (ctx, cstrs)

and clock_static_exp se =
  let st = fresh_st () in
  {
    M.se_desc = se.se_desc;
    M.se_loc = se.se_loc;
    M.se_info = annotate_clock_exp se.se_info st;
  },
  st

and expect_static_exp expected_ty se (ctx, constrs) =
  let se, actual_st = clock_static_exp se in
  se, (ctx, unify se.M.se_loc expected_ty (ty_of_st actual_st) constrs)

and clock_exp env e acc =
  let loc = e.e_loc in
  let ed, ty, acc =
  match e.e_desc with
  | E_var v ->
    let ty, acc = clock_var v acc in
    M.E_var v, ty, acc

  | E_const c ->
    M.E_const c, fresh_ty (), acc

  | E_fst e ->
    let ty_l = fresh_ty () in
    let ty_r = fresh_ty () in
    let e, acc = expect_exp env (prod_ty [ty_l; ty_r]) e acc in
    M.E_fst e, ty_l, acc

  | E_snd e ->
    let ty_l = fresh_ty () in
    let ty_r = fresh_ty () in
    let e, acc = expect_exp env (prod_ty [ty_l; ty_r]) e acc in
    M.E_snd e, ty_r, acc

  | E_tuple e_l ->
    let ety_l, acc = Utils.mapfold (clock_exp env) e_l acc in
    let e_l, ty_l = List.split ety_l in
    M.E_tuple e_l, prod_ty ty_l, acc

  | E_fby (e1, e2) ->
    let (e1, ty), acc = clock_exp env e1 acc in
    let e2, acc = expect_exp env ty e2 acc in
    M.E_fby (e1, e2), ty, acc

  | E_ifthenelse (e1, e2, e3) ->
    let (e1, ty), acc = clock_exp env e1 acc in
    let e2, acc = expect_exp env ty e2 acc in
    let e3, acc = expect_exp env ty e3 acc in
    M.E_ifthenelse (e1, e2, e3), ty, acc

  | E_app (app, e) ->
    let csig = find_node_signature env app.a_op in
    let ty_in, ty_out, preconstrs, inst =
      Clock_types.instantiate_clock_sig loc fresh_st fresh_ty csig
    in
    let app =
      {
        M.a_op = app.a_op;
        M.a_loc = app.a_loc;
        M.a_info = annotate_app app.a_info inst;
      }
    in
    let e, (ctx, cstrs) = expect_exp env ty_in e acc in
    let cstrs = preconstrs @ cstrs in
    M.E_app (app, e), ty_out, (ctx, cstrs)

  | E_where (e, block) ->
    let block, acc = clock_block env block acc in
    let (e, ty), acc = clock_exp env e acc in
    M.E_where (e, block), ty, acc

  | E_when (e, ce) ->
    let cce = trad_clock_exp ce in
    let (e, ty), acc = clock_exp env e acc in
    let st, acc = st_of_ty loc ty acc in
    let ce, acc = expect_clock_exp env st ce acc in
    M.E_when (e, ce), ty_of_st (Pst_on (st, cce)), acc

  | E_split (ce, e, ec_l) ->
    let cce = trad_clock_exp ce in
    let (e, ty), acc = clock_exp env e acc in
    let st, acc = st_of_ty loc ty acc in
    let ce, acc = expect_clock_exp env st ce acc in
    let ty_l, acc = Utils.mapfold (sampled_ty loc ty cce) ec_l acc in
    M.E_split (ce, e, ec_l), prod_ty ty_l, acc

  | E_bmerge (ce, e1, e2) ->
    let cce = trad_clock_exp ce in
    let (ce, st), acc = clock_clock_exp env ce acc in
    let ty = ty_of_st st in
    let e1, acc =
      expect_sampled_exp env ty cce (Ast_misc.Ec_bool true) e1 acc
    in
    let e2, acc =
      expect_sampled_exp env ty cce (Ast_misc.Ec_bool false) e2 acc
    in
    M.E_bmerge (ce, e1, e2), ty_of_st st, acc

  | E_merge (ce, c_l) ->
    let cce = trad_clock_exp ce in
    let (ce, st), acc = clock_clock_exp env ce acc in
    let ty = ty_of_st st in
    let c_l, acc =
      let clock_clause c acc =
        let e, acc =
          expect_sampled_exp env ty cce c.c_sel c.c_body acc
        in
        {
          M.c_sel = c.c_sel;
          M.c_body = e;
          M.c_loc = c.c_loc;
        },
        acc
      in
      Utils.mapfold clock_clause c_l acc
    in
    M.E_merge (ce, c_l), ty_of_st st, acc

  | E_valof ce ->
    let (ce, st), acc = clock_clock_exp env ce acc in
    M.E_valof ce, ty_of_st st, acc

  | E_clock_annot (e, cka) ->
    let (cka, st), acc = clock_clock_annot env loc cka acc in
    let ty = ty_of_st st in
    let e, acc = expect_exp env ty e acc in
    M.E_clock_annot (e, cka), ty, acc

  | E_type_annot (e, tya) ->
    let (e, ty), acc = clock_exp env e acc in
    M.E_type_annot (e, tya), ty, acc

  | E_dom (e, dom) ->
    let (dom, e, ty), acc = clock_dom env dom e acc in
    M.E_dom (e, dom), ty, acc

  | E_buffer e ->
    let ty, ty', acc = adaptable_tys loc acc in
    let e, acc = expect_exp env ty e acc in
    M.E_buffer e, ty', acc

  in
  (
    {
      M.e_desc = ed;
      M.e_loc = e.e_loc;
      M.e_info = annotate_exp e.e_info ty;
    },
    ty
  ),
  acc

and expect_exp env expected_ty e (ctx, constrs) =
  let (e, actual_ty), (ctx, constrs) = clock_exp env e (ctx, constrs) in
  e, (ctx, unify e.M.e_loc expected_ty actual_ty constrs)

and expect_sampled_exp env base_ty cce ec e constrs =
  let expected_ty, constrs = sampled_ty e.e_loc base_ty cce ec constrs in
  expect_exp env expected_ty e constrs

and clock_clock_annot env loc cka acc =
  match cka with
  | Ca_var v ->
    (M.Ca_var v, find_ck_var env v), acc
  | Ca_on (cka, ce) ->
    let cce = trad_clock_exp ce in
    let (cka, st), acc = clock_clock_annot env loc cka acc in
    let ce, acc = expect_clock_exp env st ce acc in
    (M.Ca_on (cka, ce), Pst_on (st, cce)), acc

and clock_pattern env p acc =
  let loc = p.p_loc in
  let pd, ty, acc =
    match p.p_desc with
    | P_var (v, ita) ->
      let ty, acc = clock_var v acc in
      M.P_var (v, ita), ty, acc

    | P_tuple p_l ->
      let pty_l, acc = Utils.mapfold (clock_pattern env) p_l acc in
      let p_l, ty_l = List.split pty_l in
      M.P_tuple p_l, prod_ty ty_l, acc

    | P_clock_annot (p, cka) ->
      let (cka, st), acc = clock_clock_annot env loc cka acc in
      let ty = ty_of_st st in
      let p, acc = expect_pattern env ty p acc in
      M.P_clock_annot (p, cka), ty, acc

    | P_type_annot (p, tya) ->
      let (p, ty), acc = clock_pattern env p acc in
      M.P_type_annot (p, tya), ty, acc

    | P_split pw ->
      let pw, ty, acc = clock_psplit env loc pw acc in
      M.P_split pw, ty, acc
  in
  (
    {
      M.p_desc = pd;
      M.p_loc = p.p_loc;
      M.p_info = annotate_exp p.p_info ty;
    },
    ty
  ),
  acc

and expect_pattern env expected_ty p (ctx, constrs) =
  let (p, actual_ty), (ctx, constrs) = clock_pattern env p (ctx, constrs) in
  p, (ctx, unify p.M.p_loc expected_ty actual_ty constrs)

and clock_psplit env loc pw acc =
  let open Ast_misc in

  let pw_ce = int_pword_of_pword pw in
  let ty = fresh_ty () in

  let rec clock_ptree (current, acc) pt =
    match pt with
    | Leaf p ->
      let ty, acc = sampled_ty loc ty pw_ce (Ec_int current) acc in
      let p, acc = expect_pattern env ty p acc in
      (Int.succ current, acc), Leaf p
    | Power (p, se) ->
      let (current, acc), p = clock_ptree (current, acc) p in
      let se, _ = clock_static_exp se in (* TODO *)
      (current, acc), Power (p, se)
    | Concat pt_l ->
      let (current, acc), p_l =
        Utils.mapfold_left clock_ptree (current, acc) pt_l
      in
      (current, acc), Concat p_l
  in

  let (current, acc), u = clock_ptree (Int.zero, acc) pw.u in
  let (_, acc), v = clock_ptree (current, acc) pw.v in
  { u = u; v = v; }, ty, acc

and clock_eq env eq acc =
  let (lhs, ty), acc = clock_pattern env eq.eq_lhs acc in
  let rhs, acc = expect_exp env ty eq.eq_rhs acc in
  {
    M.eq_lhs = lhs;
    M.eq_rhs = rhs;
    M.eq_loc = eq.eq_loc;
    M.eq_info = annotate_dummy eq.eq_info;
  },
  acc

and clock_block env block acc =
  let body, acc = Utils.mapfold (clock_eq env) block.b_body acc in
  {
    M.b_body = body;
    M.b_info = annotate_dummy block.b_info;
    M.b_loc = block.b_loc;
  },
  acc

and clock_dom env dom e (ctx, constrs) =
  assert false

let clock_node_def env nd =
  let env = reset_env env in
  let (input, ty_in), acc = clock_pattern env nd.n_input (Ident.Env.empty, []) in
  let (body, ty_out), (_, cstrs) = clock_exp env nd.n_body acc in
  let csig = Clock_types.generalize_clock_sig ty_in ty_out cstrs in
  add_local_node env nd.n_name csig,
  {
    M.n_name = nd.n_name;
    M.n_input = input;
    M.n_body = body;
    M.n_pragma = nd.n_pragma;
    M.n_static = nd.n_static;
    M.n_loc = nd.n_loc;
    M.n_info = annotate_node nd.n_info csig;
  }

let clock_node_decl env ndecl =
  add_local_node env ndecl.decl_name ndecl.decl_clock,
  {
    M.decl_name = ndecl.decl_name;
    M.decl_data = ndecl.decl_data;
    M.decl_static = ndecl.decl_static;
    M.decl_interv = ndecl.decl_interv;
    M.decl_clock = ndecl.decl_clock;
    M.decl_loc = ndecl.decl_loc;
  }

let clock_type_decl td =
  {
    M.ty_name = td.ty_name;
    M.ty_body = td.ty_body;
    M.ty_loc = td.ty_loc;
  }

let clock_phrase env phr =
  match phr with
  | Phr_node_def nd ->
    let env, nd = clock_node_def env nd in
    env, M.Phr_node_def nd
  | Phr_node_decl nd ->
    let env, nd = clock_node_decl env nd in
    env, M.Phr_node_decl nd
  | Phr_type_def td ->
    env, M.Phr_type_def (clock_type_decl td)

let clock_file file =
  let env = initial_env file.f_info#interfaces in
  let _, body = Utils.mapfold_left clock_phrase env file.f_body in
  {
    M.f_name = file.f_name;
    M.f_imports = file.f_imports;
    M.f_info = file.f_info;
    M.f_body = body;
  }

(** {2 Putting it all together} *)

let clock_file ctx file =
  let file = clock_file file in
  let file = EXTRACT.extract_file file in
  ctx, file

let clock :
    (< interfaces : Interface.env; static_nodes : Acids_static.node_def list > Acids_preclock.file ->
     < interfaces : Interface.env; static_nodes : Acids_static.node_def list > Acids_clocked.file)
    Pass_manager.pass
    =
  let open Pass_manager in
  P_transform
    (Frontend_utils.make_transform
       ~print_out:Acids_clocked.print_file
       "clocking"
       clock_file)
