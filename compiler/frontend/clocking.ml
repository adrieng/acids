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

(** {2 Type schemes} *)

type ty_constr_desc =
  | Tc_adapt of VarTySt.t * VarTySt.t
  | Tc_equal of VarTy.t * VarTy.t

type ty_constr =
  {
    loc : Loc.t;
    desc : ty_constr_desc;
  }

type ty_sch =
  {
    occ : VarTy.t Ident.Env.t;
    ty : VarTy.t;
  }

let print_ty_constr_desc fmt tycd =
  match tycd with
  | Tc_adapt (st1, st2) ->
    Format.fprintf fmt "@[%a <:@ %a@]"
      VarTySt.print st1
      VarTySt.print st2
  | Tc_equal (t1, t2) ->
    Format.fprintf fmt "@[%a =@ %a@]"
      VarTy.print t1
      VarTy.print t2

let print_ty_constr fmt tyc =
  print_ty_constr_desc fmt tyc.desc

let print_ty_sch fmt tys =
  let print_occ_item fmt (i, ty) =
    Format.fprintf fmt "%a -> %a" Ident.print i VarTy.print ty
  in
  Format.fprintf fmt "@[%a =>@ %a@]"
    (Ident.Env.print print_occ_item ";") tys.occ
    VarTy.print tys.ty

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

let fresh_ty_sch () =
  {
    occ = Ident.Env.empty;
    ty = fresh_ty ();
  }

(** {2 Environments} *)

type env =
  {
    intf_env : Interface.env;
    mutable ck_vars : ty_sch Utils.Int_map.t;
  }

let initial_env intf_env =
  {
    intf_env = intf_env;
    ck_vars = Utils.Int_map.empty;
  }

let reset_env env = { env with ck_vars = Utils.Int_map.empty; }

let find_ck_var env v =
  try Utils.Int_map.find v env.ck_vars
  with Not_found ->
    let ty = fresh_ty_sch () in
    env.ck_vars <- Utils.Int_map.add v ty env.ck_vars;
    ty

(** {2 Utility functions} *)

let singleton_ty x =
  let ty = fresh_ty () in
  {
    occ = Ident.Env.add x ty Ident.Env.empty;
    ty = ty;
  }

let unify_free_vars loc s1 s2 constrs =
  let unify_occ id ty (new_occ, new_constr) =
    try
      let ty' = Ident.Env.find id s1.occ in
      new_occ, { loc = loc; desc = Tc_equal (ty, ty') } :: new_constr
    with Not_found ->
      Ident.Env.add id ty new_occ, new_constr
  in
  let new_occ, new_constrs =
    Ident.Env.fold unify_occ s2.occ (s1.occ, constrs)
  in
  {
    occ = new_occ;
    ty = ty;
  },
  { loc = loc; desc = Tc_equal (s1.ty, s2.ty) } :: new_constrs

let merge_sch loc ty s1 s2 constrs =
  let unify_occ id ty (new_occ, new_constr) =
    try
      let ty' = Ident.Env.find id s1.occ in
      new_occ, { loc = loc; desc = Tc_equal (ty, ty') } :: new_constr
    with Not_found ->
      Ident.Env.add id ty new_occ, new_constr
  in
  let new_occ, new_constrs =
    Ident.Env.fold unify_occ s2.occ (s1.occ, constrs)
  in
  {
    occ = new_occ;
    ty = ty;
  },
  { loc = loc; desc = Tc_equal (s1.ty, s2.ty) } :: new_constrs

(* [unify_sch s1 s2] unify the occurences found in occ1 and occ2 *)
let unify_sch loc s1 s2 constrs =
  let sch, constrs = merge_sch loc s1.ty s1 s2 constrs in
  sch, { loc = loc; desc = Tc_equal (s1.ty, s2.ty); } :: constrs

let tuple_ty loc s_l constrs =
  let ty = PreTy.Pct_prod (List.map (fun sch -> sch.ty) s_l) in
  let merge (res_s, constrs) s = merge_sch loc ty res_s s constrs in
  let s, s_l = Utils.get_1 s_l in
  List.fold_left merge (s, constrs) s_l

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

let on_ty loc s ce constrs =
  let st = fresh_st () in
  { s with ty = Pct_stream (Pst_on (st, ce)); },
  { loc = loc; desc = Tc_equal (Pct_stream st, s.ty); } :: constrs

let ty_of_st st = { ty = Pct_stream st; occ = Ident.Env.empty; }

let adaptable_tys loc constrs =
  let st = fresh_st () in
  let st' = fresh_st () in
  let constr = { loc = loc; desc = Tc_adapt (st, st'); } in
  ty_of_st st, ty_of_st st', constr :: constrs

let sampled_ty loc ty cce ec constrs =
  on_ty loc ty (Clock_types.Ce_equal (cce, ec)) constrs

(** {2 High-level utilities} *)

module A =
struct
  type new_annot =
    | Exp of ty_sch
    | Node of ty_sch * ty_sch

  let print_new_annot fmt na =
    match na with
    | Exp ty -> print_ty_sch fmt ty
    | Node (ty_in, ty_out) ->
      Format.fprintf fmt "@[%a -> %a@]"
        print_ty_sch ty_in
        print_ty_sch ty_out
end

module ANN_INFO = Acids_utils.MakeAnnot(Acids_preclock)(A)
module M = Acids.Make(ANN_INFO)

let annotate_exp info ty =
  ANN_INFO.annotate info (A.Exp ty)

let annotate_node info inp_ty out_ty =
  ANN_INFO.annotate info (A.Node (inp_ty, out_ty))

let annotate_dummy info =
  let dummy_sch =
    {
      occ = Ident.Env.empty;
      ty = PreTy.Pct_var { VarTy.v_id = -1; VarTy.v_link = None; };
    }
  in
  ANN_INFO.annotate info (A.Exp dummy_sch)

(** {2 Clocking itself} *)

let clock_var v = singleton_ty v

let rec clock_clock_exp env ce constrs =
  let loc = ce.ce_loc in
  let ced, ty, constrs =
    match ce.ce_desc with
    | Ce_var v ->
      M.Ce_var v, clock_var v, constrs
    | Ce_pword pw ->
      let v = fresh_ty_sch () in
      let pw, constrs =
        let expect = expect_static_exp v in
        Ast_misc.mapfold_upword expect expect pw constrs
      in
      M.Ce_pword pw, v, constrs
    | Ce_equal (ce, se) ->
      let (ce, ty), constrs = clock_clock_exp env ce constrs in
      let se, constrs = expect_static_exp ty se constrs in
      M.Ce_equal (ce, se), ty, constrs
    | Ce_iter ce ->
      let (mce, ty), constrs = clock_clock_exp env ce constrs in
      let ty, constrs = on_ty loc ty (trad_clock_exp ce) constrs in
      M.Ce_iter mce, ty, constrs
  in
  ({
    M.ce_desc = ced;
    M.ce_loc = loc;
    M.ce_info = annotate_exp ce.ce_info ty;
  }, ty),
  constrs

and expect_clock_exp env expected_ty ce constrs =
  let (ce', actual_ty), constrs = clock_clock_exp env ce constrs in
  let ty, constrs = unify_sch ce.ce_loc expected_ty actual_ty constrs in
  { ce' with M.ce_info = annotate_exp ce.ce_info ty; }, constrs

and clock_static_exp se =
  let ty = fresh_ty_sch () in
  {
    M.se_desc = se.se_desc;
    M.se_loc = se.se_loc;
    M.se_info = annotate_exp se.se_info ty;
  },
  ty

and expect_static_exp expected_ty se constrs =
  let se', actual_ty = clock_static_exp se in
  let ty, constrs = unify_sch se.se_loc expected_ty actual_ty constrs in
  { se' with M.se_info = annotate_exp se.se_info ty; }, constrs

and clock_exp env e constrs =
  let loc = e.e_loc in
  let ed, ty, constrs =
  match e.e_desc with
  | E_var v ->
    M.E_var v, clock_var v, constrs

  | E_const c ->
    M.E_const c, fresh_ty_sch (), constrs

  | E_fst e ->
    let ty_l = fresh_ty_sch () in
    let ty_r = fresh_ty_sch () in
    let ty, constrs = tuple_ty loc [ty_l; ty_r] constrs in
    let e, constrs = expect_exp env ty e constrs in
    M.E_fst e, ty_l, constrs

  | E_snd e ->
    let ty_l = fresh_ty_sch () in
    let ty_r = fresh_ty_sch () in
    let ty, constrs = tuple_ty loc [ty_l; ty_r] constrs in
    let e, constrs = expect_exp env ty e constrs in
    M.E_snd e, ty_r, constrs

  | E_tuple e_l ->
    let ety_l, constrs = Utils.mapfold (clock_exp env) e_l constrs in
    let e_l, ty_l = List.split ety_l in
    let ty, constrs = tuple_ty e.e_loc ty_l constrs in
    M.E_tuple e_l, ty, constrs

  | E_fby (e1, e2) ->
    let (e1, ty), constrs = clock_exp env e1 constrs in
    let e2, constrs = expect_exp env ty e2 constrs in
    M.E_fby (e1, e2), ty, constrs

  | E_ifthenelse (e1, e2, e3) ->
    let (e1, ty), constrs = clock_exp env e1 constrs in
    let e2, constrs = expect_exp env ty e2 constrs in
    let e3, constrs = expect_exp env ty e3 constrs in
    M.E_ifthenelse (e1, e2, e3), ty, constrs

  | E_app _ ->
    assert false (* TODO *)

  | E_where (e, block) ->
    assert false

  | E_when (e, ce) ->
    let cce = trad_clock_exp ce in
    let (e, ty), constrs = clock_exp env e constrs in
    let ce, constrs = expect_clock_exp env ty ce constrs in
    let ty, constrs = on_ty loc ty cce constrs in
    M.E_when (e, ce), ty, constrs

  | E_split (ce, e, ec_l) ->
    let cce = trad_clock_exp ce in
    let (e, ty), constrs = clock_exp env e constrs in
    let ce, constrs = expect_clock_exp env ty ce constrs in
    let ty_l, constrs = Utils.mapfold (sampled_ty loc ty cce) ec_l constrs in
    let ty, constrs = tuple_ty loc ty_l constrs in
    M.E_split (ce, e, ec_l), ty, constrs

  | E_bmerge (ce, e1, e2) ->
    let cce = trad_clock_exp ce in
    let (ce, ty), constrs = clock_clock_exp env ce constrs in
    let e1, constrs =
      expect_sampled_exp env ty cce (Ast_misc.Ec_bool true) e1 constrs
    in
    let e2, constrs =
      expect_sampled_exp env ty cce (Ast_misc.Ec_bool false) e2 constrs
    in
    M.E_bmerge (ce, e1, e2), ty, constrs

  | E_merge (ce, c_l) ->
    let cce = trad_clock_exp ce in
    let (ce, ty), constrs = clock_clock_exp env ce constrs in
    let c_l, constrs =
      let clock_clause c constrs =
        let e, constrs =
          expect_sampled_exp env ty cce c.c_sel c.c_body constrs
        in
        {
          M.c_sel = c.c_sel;
          M.c_body = e;
          M.c_loc = c.c_loc;
        },
        constrs
      in
      Utils.mapfold clock_clause c_l constrs
    in
    M.E_merge (ce, c_l), ty, constrs

  | E_valof ce ->
    let (ce, ty), constrs = clock_clock_exp env ce constrs in
    M.E_valof ce, ty, constrs

  | E_clock_annot (e, cka) ->
    let (cka, ty), constrs = clock_clock_annot env loc cka constrs in
    let e, constrs = expect_exp env ty e constrs in
    M.E_clock_annot (e, cka), ty, constrs

  | E_type_annot (e, tya) ->
    let (e, ty), constrs = clock_exp env e constrs in
    M.E_type_annot (e, tya), ty, constrs

  | E_dom (e, dom) ->
    let (e, ty), constrs = clock_exp env e constrs in
    let (dom, ty), constrs = clock_dom env dom ty constrs in
    M.E_dom (e, dom), ty, constrs

  | E_buffer e ->
    let ty, ty', constrs = adaptable_tys loc constrs in
    let e, constrs = expect_exp env ty e constrs in
    M.E_buffer e, ty', constrs

  in
  ({
    M.e_desc = ed;
    M.e_loc = e.e_loc;
    M.e_info = annotate_exp e.e_info ty;
   },
   ty),
  constrs

and expect_exp env expected_ty e constrs =
  let (e', actual_ty), constrs = clock_exp env e constrs in
  let ty, constrs = unify_sch e.e_loc expected_ty actual_ty constrs in
  { e' with M.e_info = annotate_exp e.e_info ty; }, constrs

and expect_sampled_exp env base_ty cce ec e constrs =
    let expected_ty, constrs = sampled_ty e.e_loc base_ty cce ec constrs in
    expect_exp env expected_ty e constrs

and clock_clock_annot env loc cka constrs =
  match cka with
  | Ca_var v ->
    (M.Ca_var v, find_ck_var env v), constrs
  | Ca_on (cka, ce) ->
    let cce = trad_clock_exp ce in
    let (cka, ty), constrs = clock_clock_annot env loc cka constrs in
    let ce, constrs = expect_clock_exp env ty ce constrs in
    let res_ty, constrs = on_ty loc ty cce constrs in
    (M.Ca_on (cka, ce), res_ty), constrs

and clock_dom env dom ty constrs =
  assert false

(** {2 Putting it all together} *)

let clock :
    (< interfaces : Interface.env; static_nodes : Acids_static.node_def list > Acids_preclock.file ->
     < interfaces : Interface.env; static_nodes : Acids_static.node_def list > Acids_clocked.file)
    Pass_manager.pass
    =
  assert false
