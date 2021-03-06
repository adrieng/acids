(* Copyright (C) Adrien Guatto <adrien.guatto@laposte.net> 2013-2014
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
open Acids_spec
open PreTySt
open PreTy

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

(** {2 Environments} *)

type env =
  {
    ctx : Pass_manager.ctx;
    intf_env : Interface.t Names.ModEnv.t;
    pragmas : Pragma.pragma Utils.Env.t;
    local_nodes : Clock_types.clock_sig Names.ShortEnv.t;
    local_pwords : Ast_misc.econstr_pword Names.ShortEnv.t;
    mutable ck_vars : VarTySt.t Utils.Int_map.t;
  }

let initial_env ctx intf_env =
  {
    ctx = ctx;
    intf_env = Names.mod_env_of_short_env intf_env;
    pragmas = Utils.Env.empty;
    local_nodes = Names.ShortEnv.empty;
    local_pwords = Names.ShortEnv.empty;
    ck_vars = Utils.Int_map.empty;
  }

let get_interfaces env = env.intf_env

let get_ctx env = env.ctx

let get_pragma_env env = env.pragmas

let reset_env env pragmas =
  {
    env with
      pragmas = Pragma.env_of_pragma_list pragmas;
      ck_vars = Utils.Int_map.empty;
  }

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
    let intf = ModEnv.find (Module modn) env.intf_env in
    Interface.clock_signature_of_node_item (Interface.find_node intf ln.shortn)

let find_pword env ln =
  let open Names in
  match ln.modn with
  | LocalModule -> ShortEnv.find ln.shortn env.local_pwords
  | Module modn ->
    let intf = ModEnv.find (Module modn) env.intf_env in
    let pi = Interface.find_pword intf ln.shortn in
    pi.Interface.pi_value

let add_pword env pn pw =
  let get se = se.se_desc in
  let get_int se = Ast_misc.int_of_econstr (get se) in
  let p = Tree_word.map_upword get get_int pw in
  { env with local_pwords = Names.ShortEnv.add pn p env.local_pwords; }

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

(* This function implement very simple heuristics to minimize the number of
   useless equations *)
let unify loc t1 t2 constrs =
  let unify_st loc st1 st2 constrs =
    let open VarTySt in
    let st1 = unalias_st st1 in
    let st2 = unalias_st st2 in
    match st1, st2 with
    | Pst_var { v_id = v1; }, Pst_var ({ v_id = v2; } as r) ->
      if v1 = v2 then () else r.v_link <- Some st1;
      constrs
    | _ ->
      let desc = Tc_equal (PreTy.Pct_stream st1, PreTy.Pct_stream st2) in
      { loc = loc; desc = desc; } :: constrs
  in

  let open VarTy in
  let t1 = unalias_ty t1 in
  let t2 = unalias_ty t2 in
  match t1, t2 with
  | Pct_var { v_id = v1; }, Pct_var ({ v_id = v2; } as r) ->
    if v1 = v2 then () else r.v_link <- Some t1;
    constrs

  | Pct_stream st1, Pct_stream st2 ->
    unify_st loc st1 st2 constrs

  | _ ->
    { loc = loc; desc = Tc_equal (t1, t2); } :: constrs

let prod_ty t_l = Pct_prod t_l

let trans_const_exp_int se = Ast_misc.get_int se.se_desc

module T = Acids_utils.TRANSLATE_CLOCK_EXP(Acids_spec)

let trans_clock_exp env ce =
  let find_pword ln = find_pword env ln in
  let find_bounds info = info#ci_bounds in
  let find_specs info = info#ci_specs in
  let cce = T.trans_clock_exp find_pword find_bounds find_specs ce in
  Clock_types.pre_ce_of_ce cce

let rec int_ptree_of_ptree current pt =
  let open Tree_word in
  let open Ast_misc in
  match pt with
  | Leaf _ -> Int.succ current, Leaf (Ec_int current)
  | Power (pt, se) ->
    let current, pt = int_ptree_of_ptree current pt in
    current, Power (pt, trans_const_exp_int se)
  | Concat pt_l ->
    let current, pt_l = Utils.mapfold_left int_ptree_of_ptree current pt_l in
    current, Concat pt_l

let int_pword_of_pword pw =
  let open Tree_word in
  let current, u = int_ptree_of_ptree Int.zero pw.u in
  let _, v = int_ptree_of_ptree current pw.v in
  Clock_types.PreCe.Pce_pword { u = u; v = v; }

let rec psplit_length pt =
  let open Tree_word in
  match pt with
  | Leaf _ -> Int.of_int 1
  | Power (pt, se) ->
    Int.mul (Ast_misc.get_int se.se_desc) (psplit_length pt)
  | Concat p_l ->
    List.fold_left (fun l pt -> Int.add l (psplit_length pt)) Int.zero p_l

let ty_of_st st = Pct_stream st

let st_of_ty loc t (ctx, constrs) =
  let st = fresh_st () in
  st, (ctx, { loc = loc; desc = Tc_equal (ty_of_st st, t); } :: constrs)

let on_ty loc t ce acc =
  let st, acc = st_of_ty loc t acc in
  ty_of_st (Pst_on (st, ce)), acc

let adaptable_sts loc (ctx, constrs) =
  let st = fresh_st () in
  let st' = fresh_st () in
  let constr = { loc = loc; desc = Tc_adapt (st, st'); } in
  st, st', (ctx, constr :: constrs)

let sampled_ty loc ty cce ec acc =
  on_ty loc ty (Clock_types.PreCe.Pce_equal (cce, ec)) acc

(** {2 High-level utilities} *)

module A =
struct
  type new_annot =
    | Exp of VarTy.t
    | ClockExp of VarTySt.t
    | Domain of VarTySt.t * (VarTy.t * VarTy.t) Ident.Env.t
    | Node of Clock_types.clock_sig
    | App of (int * VarTySt.t) list
    | Buffer of Loc.t * VarTySt.t * VarTySt.t (* in st * out st *)

  let print_new_annot fmt na =
    match na with
    | Exp ty -> VarTy.print fmt ty
    | ClockExp st -> VarTySt.print fmt st
    | Domain (st, down) ->
      let print_down fmt (ext, int) =
        Format.fprintf fmt "%a -> %a"
          VarTy.print ext
          VarTy.print int
      in
      Format.fprintf fmt "@[base @[%a@],@ env @[%a@]@]"
        VarTySt.print st
        (Ident.Env.print print_down ";") down
    | Node csig ->
      Clock_types.print_sig fmt csig
    | App st_inst ->
      let print_st_binding fmt (i, st) =
        Format.fprintf fmt "%d -> %a" i VarTySt.print st
      in
      Format.fprintf fmt "@[%a@]"
        (Utils.print_list_r print_st_binding ",") st_inst
    | Buffer (_, in_st, out_st) ->
      Format.fprintf fmt "@[%a <: %a@]"
        VarTySt.print in_st
        VarTySt.print out_st
end

module ANN_INFO = Acids_utils.MakeAnnot(Acids_spec)(A)
module M = Acids.Make(ANN_INFO)

let annotate_exp info ty =
  ANN_INFO.annotate info (A.Exp ty)

let annotate_clock_exp info st =
  ANN_INFO.annotate info (A.ClockExp st)

let annotate_domain info st down =
  ANN_INFO.annotate info (A.Domain (st, down))

let annotate_node info csig =
  ANN_INFO.annotate info (A.Node csig)

let annotate_app info inst_st =
  ANN_INFO.annotate info (A.App inst_st)

let annotate_buffer info loc in_st out_st =
  ANN_INFO.annotate info (A.Buffer (loc, in_st, out_st))

let annotate_dummy info =
  let dummy_sch = PreTy.Pct_var { VarTy.v_id = -1; VarTy.v_link = None; } in
  ANN_INFO.annotate info (A.Exp dummy_sch)

module MORPH =
struct
  module IN_INFO = M.I
  module OUT_INFO = Acids_clocked.Info

  open ANN_INFO
  open A

  let st_of_pre_st = st_of_pre_st make_st_var

  let ty_of_pre_ty = ty_of_pre_ty make_st_var

  let map_const_exp_desc _ ec = ec

  let update_clock_exp_info { new_annot = na; old_annot = info; } =
    match na with
    | Node _ | App _ | Exp _ | Buffer _ | Domain _ ->
      invalid_arg "update_clock_exp_info"
    | ClockExp pst ->
      (
        object
          method ci_data = info#ci_data
          method ci_bounds = info#ci_bounds
          method ci_specs = info#ci_specs
          method ci_clock = st_of_pre_st pst
        end
      )

  let update_const_exp_info { new_annot = na; old_annot = info; } =
    match na with
    | Node _ | App _ | Exp _ | Buffer _ | Domain _ ->
      invalid_arg "update_const_exp_info"
    | ClockExp pst ->
      (
        object
          method pwi_data = info#pwi_data
          method pwi_clock = st_of_pre_st pst
          end
      )

  let update_exp_info { new_annot = na; old_annot = info; } =
    match na with
    | Node _ | App _ | ClockExp _ | Buffer _ | Domain _ ->
      invalid_arg "update_exp_info"
    | Exp pty ->
      object
        method ei_data = info#ei_data
        method ei_clock = ty_of_pre_ty pty
      end

  let update_app_info { new_annot = na; old_annot = (); } =
    match na with
    | Exp _ | Node _ | ClockExp _ | Buffer _ | Domain _ ->
      invalid_arg "update_app_info"
    | App inst_st ->
      let trans_st (i, pst) = i, st_of_pre_st pst in
      object
        method ai_stream_inst = List.map trans_st inst_st
      end

  let update_block_info _ = ()

  let update_pat_info { new_annot = na; old_annot = info; } =
    match na with
    | Node _ | App _ | ClockExp _ | Buffer _ | Domain _ ->
      invalid_arg "update_pat_info"
    | Exp pty ->
      let ty = ty_of_pre_ty pty in
      object
        method pi_data = info#pi_data
        method pi_clock = ty
      end

  let update_eq_info _ = ()

  let update_domain_info { new_annot = na; old_annot = (); } =
    match na with
    | Node _ | App _ | Exp _ | Buffer _ | ClockExp _ ->
      invalid_arg "update_domain_info"
    | Domain (pst, down) ->
      object
        method di_activation_clock = st_of_pre_st pst
        method di_downsampled =
          Ident.Env.map
            (fun (ext, int) ->
              let open Acids_clocked in
              {
                external_clock = ty_of_pre_ty ext;
                internal_clock = ty_of_pre_ty int;
              }
            )
            down
      end

  let update_buffer_info { new_annot = na; old_annot = (); } =
    match na with
    | Node _ | App _ | Exp _ | ClockExp _ | Domain _ ->
      invalid_arg "update_buffer_info"
    | Buffer (loc, in_st, out_st) ->
      let in_st = st_of_pre_st in_st in
      let out_st = st_of_pre_st out_st in
      let info =
        object
          method bui_is_delay = Clock_types.non_strict_adaptable in_st out_st
          method bui_real_size = Clock_types.buffer_size in_st out_st
          method bui_size =
            Clock_types.buffer_size ~consider_bypass:true in_st out_st
        end
      in
      if !Compiler_options.print_buffer_info
      then
        Format.printf "(* @[%abuffer of size %a, delay: %b@] *)@."
          Loc.print loc
          Int.print info#bui_size
          info#bui_is_delay
      ;
      info


  let update_node_info  { new_annot = na; old_annot = info; } =
    match na with
    | Exp _ | App _ | ClockExp _ | Buffer _ | Domain _ ->
      invalid_arg "update_node_info"
    | Node csig ->
      object
        method ni_ctx = info#ni_ctx
        method ni_data = info#ni_data
        method ni_const = info#ni_const
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
    | Ce_condvar v ->
      let ty, acc = clock_var v acc in
      let st, acc = st_of_ty loc ty acc in
      M.Ce_condvar v, st, acc

    | Ce_pword (Pd_lit pw) ->
      let st = fresh_st () in
      let pw, acc =
        let expect = expect_const_exp (ty_of_st st) in
        Tree_word.mapfold_upword expect expect pw acc
      in
      M.Ce_pword (M.Pd_lit pw), st, acc

    | Ce_pword (Pd_global ln) ->
      M.Ce_pword (M.Pd_global ln), fresh_st (), acc

    | Ce_equal (ce, se) ->
      let (ce, st), acc = clock_clock_exp env ce acc in
      let se, acc = expect_const_exp (ty_of_st st) se acc in
      M.Ce_equal (ce, se), st, acc
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

and clock_const_exp se =
  let st = fresh_st () in
  {
    M.se_desc = se.se_desc;
    M.se_loc = se.se_loc;
    M.se_info = annotate_clock_exp se.se_info st;
  },
  st

and expect_const_exp expected_ty se (ctx, constrs) =
  let se, actual_st = clock_const_exp se in
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
    (* WARN: e1 and e2 should have a stream clock type, for the
       fby will be lowered to merge/buffer later *)
    let ty = ty_of_st (fresh_st ()) in
    let e1, acc = expect_exp env ty e1 acc in
    let e2, acc = expect_exp env ty e2 acc in
    M.E_fby (e1, e2), ty, acc

  | E_ifthenelse (e1, e2, e3) ->
    (* WARN: e1, e2 and e3 should have a stream clock type, for the
       if will be lowered to merge later *)
    let ty = ty_of_st (fresh_st ()) in
    let e1, acc = expect_exp env ty e1 acc in
    let e2, acc = expect_exp env ty e2 acc in
    let e3, acc = expect_exp env ty e3 acc in
    M.E_ifthenelse (e1, e2, e3), ty, acc

  | E_app (app, e) ->
    let csig = find_node_signature env app.a_op in
    let ty_in, ty_out, preconstrs, inst_st =
      Clock_types.instantiate_clock_sig loc csig
    in
    let app =
      {
        M.a_op = app.a_op;
        M.a_loc = app.a_loc;
        M.a_info = annotate_app app.a_info inst_st;
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
    let cce = trans_clock_exp env ce in
    let (e, ty), acc = clock_exp env e acc in
    let st, acc = st_of_ty loc ty acc in
    let ce, acc = expect_clock_exp env st ce acc in
    M.E_when (e, ce), ty_of_st (Pst_on (st, cce)), acc

  | E_split (ce, e, ec_l) ->
    let cce = trans_clock_exp env ce in
    let (e, ty), acc = clock_exp env e acc in
    let st, acc = st_of_ty loc ty acc in
    let ce, acc = expect_clock_exp env st ce acc in
    let ty_l, acc = Utils.mapfold (sampled_ty loc ty cce) ec_l acc in
    M.E_split (ce, e, ec_l), prod_ty ty_l, acc

  | E_bmerge (ce, e1, e2) ->
    let cce = trans_clock_exp env ce in
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
    let cce = trans_clock_exp env ce in
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

  | E_spec_annot (e, spec) ->
    let (e, ty), acc = clock_exp env e acc in
    let spec, acc = expect_spec ty spec acc in
    M.E_spec_annot (e, spec), ty, acc

  | E_dom (e, dom) ->
    let (dom, e, ty), acc = clock_dom env loc dom e acc in
    M.E_dom (e, dom), ty, acc

  | E_buffer (e, bu) ->
    let st, st', acc = adaptable_sts loc acc in
    let e, acc = expect_exp env (ty_of_st st) e acc in
    let bu = clock_buffer env loc st st' bu in
    M.E_buffer (e, bu), ty_of_st st', acc

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
    let cce = trans_clock_exp env ce in
    let (cka, st), acc = clock_clock_annot env loc cka acc in
    let ce, acc = expect_clock_exp env st ce acc in
    (M.Ca_on (cka, ce), Pst_on (st, cce)), acc

and clock_pattern env p acc =
  let loc = p.p_loc in
  let pd, ty, acc =
    match p.p_desc with
    | P_var v ->
      let ty, acc = clock_var v acc in
      M.P_var v, ty, acc

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

    | P_spec_annot (p, spec) ->
      let (p, ty), acc = clock_pattern env p acc in
      let spec, acc = expect_spec ty spec acc in
      M.P_spec_annot (p, spec), ty, acc

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

and expect_pattern env expected_ty p acc =
  let (p, actual_ty), (ctx, constrs) = clock_pattern env p acc in
  p, (ctx, unify p.M.p_loc expected_ty actual_ty constrs)

and clock_spec spec acc =
  let ty = fresh_ty () in
  let sd, acc =
    match spec.s_desc with
    | Unspec -> M.Unspec, acc
    | Word w ->
      let w, acc =
        Tree_word.mapfold_upword
          (expect_const_exp ty)
          (expect_const_exp ty)
          w
          acc
      in
      M.Word w, acc
    | Interval (l, u) ->
      let l, acc = expect_const_exp ty l acc in
      let u, acc = expect_const_exp ty u acc in
      M.Interval (l, u), acc
  in
  {
    M.s_desc = sd;
    M.s_loc = spec.s_loc;
  },
  ty,
  acc

and expect_spec expected_ty spec acc =
  let spec, actual_ty, (ctx, constrs) = clock_spec spec acc in
  spec, (ctx, unify spec.M.s_loc expected_ty actual_ty constrs)

and clock_psplit env loc pw acc =
  let open Ast_misc in
  let open Tree_word in

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
      let se, _ = clock_const_exp se in (* TODO *)
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
  let desc, acc =
    match eq.eq_desc with
    | Eq_plain (lhs, rhs) ->
      let (lhs, ty), acc = clock_pattern env lhs acc in
      let rhs, acc = expect_exp env ty rhs acc in
      M.Eq_plain (lhs, rhs), acc
    | Eq_condvar (lhs, specs, rhs) ->
      let ty, acc = clock_var lhs acc in
      let specs, acc = Utils.mapfold (expect_spec ty) specs acc in
      let rhs, acc = expect_exp env ty rhs acc in
      M.Eq_condvar (lhs, specs, rhs), acc
  in
  {
    M.eq_desc = desc;
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

and clock_dom env loc dom e acc =
  (* Clocking domains:
     1. Clock e in a fresh environment (ctx and constraints)
     2. Solve clocking constraints
     3. Generate a fresh stream type bst
     4. If the domain is annotated with a base clock,
     add an equality constraint between bst and the former
     5. For each x : st free in e, add a constraint relating st[alpha/bst]
     and its type in the original environment.
     6. If e has type ty, the resulting type has ty[alpha/bst].
  *)

  (* 1. Clock e in isolation *)
  let (e, ty), (local_ctx, local_constrs) =
    clock_exp env e (Ident.Env.empty, [])
  in

  (* 2. Solve constraints *)
  Clocking_resolution.solve_constraints
    (get_interfaces env)
    (get_ctx env)
    (get_pragma_env env)
    loc
    local_constrs;

  (* 3. Fresh base clock *)
  let bst = fresh_st () in

  (* 4. Unification between base clock and annot *)
  let cka, (ctx, cstrs) =
    match dom.d_base_clock with
    | None -> None, acc
    | Some cka ->
      let (cka, st), (ctx, cstrs) = clock_clock_annot env loc cka acc in
      let c = { loc = loc; desc = Tc_equal (ty_of_st bst, ty_of_st st); } in
      Some cka, (ctx, c :: cstrs)
  in

  (* 5. For each free variable of e, we add a constraint relating it to the
     output env *)
  let fv_e =
    let module F = Acids_utils.FREEVARS(M) in
    F.fv_exp Ident.Set.empty e
  in
  let add_constraint v (ctx, cstrs, down) =
    let out_ty, (ctx, cstrs) = clock_var v (ctx, cstrs) in
    let in_ty = Ident.Env.find v local_ctx in
    let c = { loc = loc; desc = Tc_equal (out_ty, reroot_ty bst in_ty); } in
    (ctx, c :: cstrs, Ident.Env.add v (out_ty, in_ty) down)
  in
  let (ctx, cstrs, down) =
    Ident.Set.fold add_constraint fv_e (ctx, cstrs, Ident.Env.empty)
  in

  let ty = reroot_ty bst ty in

  (
    {
      M.d_base_clock = cka;
      M.d_par = dom.d_par;
      M.d_info = annotate_domain dom.d_info bst down;
    },
    e,
    ty),
  (ctx, cstrs)

and clock_buffer _ loc in_st out_st bu =
  {
    M.bu_info = annotate_buffer bu.bu_info loc in_st out_st;
  }

let clock_node_def env nd =
  Clock_types.reset_st ();
  Clock_types.reset_ty ();
  let env = reset_env env nd.n_pragma in
  Ident.set_current_ctx nd.n_info#ni_ctx;
  let (input, ty_in), acc =
    clock_pattern env nd.n_input (Ident.Env.empty, [])
  in
  let (body, ty_out), (_, cstrs) = clock_exp env nd.n_body acc in
  Clocking_resolution.solve_constraints
    (get_interfaces env)
    (get_ctx env)
    (get_pragma_env env)
    nd.n_loc
    cstrs;
  let csig = Clock_types.generalize_clock_sig ty_in ty_out [] in
  add_local_node env nd.n_name csig,
  {
    M.n_name = nd.n_name;
    M.n_input = input;
    M.n_body = body;
    M.n_pragma = nd.n_pragma;
    M.n_const = nd.n_const;
    M.n_loc = nd.n_loc;
    M.n_info = annotate_node nd.n_info csig;
  }

let clock_node_decl env ndecl =
  add_local_node env ndecl.decl_name ndecl.decl_clock,
  {
    M.decl_name = ndecl.decl_name;
    M.decl_data = ndecl.decl_data;
    M.decl_const = ndecl.decl_const;
    M.decl_clock = ndecl.decl_clock;
    M.decl_loc = ndecl.decl_loc;
  }

let clock_const_def env sd =
  let c =
    match sd.sd_body.e_desc with
    | E_const c -> c
    | _ -> assert false (* const-simpl problem *)
  in
  {
    M.sd_name = sd.sd_name;
    M.sd_body =
      {
        M.e_desc = M.E_const c;
        M.e_info = annotate_exp sd.sd_body.e_info (fresh_ty ());
        M.e_loc = sd.sd_body.e_loc;
      };
    M.sd_loc = sd.sd_loc;
  },
  env

let clock_pword_def env pd =
  let st = fresh_st () in
  let pw, _ =
    let expect = expect_const_exp (ty_of_st st) in
    Tree_word.mapfold_upword expect expect pd.pd_body (Ident.Env.empty, [])
  in
  {
    M.pd_name = pd.pd_name;
    M.pd_body = pw;
    M.pd_loc = pd.pd_loc;
  },
  add_pword env pd.pd_name pd.pd_body

let clock_phrase env phr =
  match phr with
  | Phr_node_def nd ->
    let env, nd = clock_node_def env nd in
    env, M.Phr_node_def nd
  | Phr_node_decl nd ->
    let env, nd = clock_node_decl env nd in
    env, M.Phr_node_decl nd
  | Phr_type_def td ->
    env, M.Phr_type_def td
  | Phr_const_def sd ->
    let sd, env = clock_const_def env sd in
    env, M.Phr_const_def sd
  | Phr_pword_def pd ->
    let pd, env = clock_pword_def env pd in
    env, M.Phr_pword_def pd

let clock_file ctx file =
  let env = initial_env ctx file.f_info#interfaces in
  let _, body = Utils.mapfold_left clock_phrase env file.f_body in
  {
    M.f_name = file.f_name;
    M.f_imports = file.f_imports;
    M.f_info = file.f_info;
    M.f_body = body;
  }

(** {2 Putting it all together} *)

let clock_file ctx file =
  let file = clock_file ctx file in
  let file = EXTRACT.extract_file file in
  ctx, file

let pass :
    (< interfaces : Interface.env; const_nodes : Acids_const.node_def list >
      Acids_spec.file ->
     < interfaces : Interface.env; const_nodes : Acids_const.node_def list >
       Acids_clocked.file)
    Pass_manager.pass
    =
  let open Pass_manager in
  P_transform
    (Frontend_utils.make_transform
       ~print_out:Acids_clocked.print_file
       "clocking"
       clock_file)
