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

open Acids_scoped
open Data_types

(** {1 Data typing}

    Nothing special, really. *)

(** {2 Errors} *)

type error =
  | Unification_conflict of Loc.t * VarTy.t * VarTy.t
  | Unification_occur of Loc.t * VarTy.t

exception Typing_error of error

let print_error fmt err =
  match err with
  | Unification_conflict (l, ty1, ty2) ->
    Format.fprintf fmt "%aCould not unify %a with %a"
      Loc.print l
      VarTy.print ty1
      VarTy.print ty2
  | Unification_occur (l, ty) ->
    Format.fprintf fmt "%aType %a is cyclic"
      Loc.print l
      VarTy.print ty

let unification_conflict loc ty1 ty2 =
  raise (Typing_error (Unification_conflict (loc, ty1, ty2)))

let unification_occur loc ty =
  raise (Typing_error (Unification_occur (loc, ty)))

(** {2 Unification} *)

let occur_check loc id ty =
  let open PreTy in
  let open VarTy in
  let rec walk ty =
    match ty with
    | Pty_var { v_link = Some ty; } -> walk ty
    | Pty_var { v_link = None; v_id = id'; } ->
      if id = id' then unification_occur loc ty
    | Pty_scal _ -> ()
    | Pty_cond ty -> walk ty
    | Pty_prod ty_l -> List.iter walk ty_l
  in
  walk ty

let unify loc ty1 ty2 =
  let open PreTy in
  let open VarTy in

  let rec u ty1 ty2 =
    match ty1, ty2 with
    (** traverse links *)
    | Pty_var { v_link = Some ty1; }, ty2
    | ty1, Pty_var { v_link = Some ty2; } -> u ty1 ty2

    | Pty_var { v_link = None; v_id = id1; },
      Pty_var { v_link = None; v_id = id2; } when id1 = id2 ->
      ()

    (** in-place unification *)
    | Pty_var ({ v_link = None; v_id = id; } as r), ty
    | ty, Pty_var ({ v_link = None; v_id = id; } as r) ->
      occur_check loc id ty;
      r.v_link <- Some ty

    | Pty_scal Tys_bool, Pty_scal Tys_bool
    | Pty_scal Tys_int, Pty_scal Tys_int
    | Pty_scal Tys_float, Pty_scal Tys_float ->
      ()

    | Pty_prod ty_l1, Pty_prod ty_l2 ->
      (try List.iter2 u ty_l1 ty_l2
       with Invalid_argument _ -> unification_conflict loc ty1 ty2)

    | _ ->
      unification_conflict loc ty1 ty2
  in
  u ty1 ty2

let try_unify_no_conflict loc ty1 ty2 =
  try unify loc ty1 ty2; true
  with Typing_error (Unification_conflict _) -> false

(** {2 Low-level utilities} *)

let reset_ty, fresh_ty =
  let open PreTy in
  let open VarTy in
  let r = ref 0 in
  (fun () -> r := 0),
  (fun () -> incr r; Pty_var { v_link = None; v_id = !r; })

(** {2 Typing environments} *)

type typing_env =
  {
    (** maps module names to interfaces *)
    intf_env : Interface.env;
    (** maps constructors from the current module to type names *)
    current_constr : Names.shortname Names.ShortEnv.t;
    (** maps nodes from the current module to type signatures *)
    current_nodes : Data_types.data_sig Names.ShortEnv.t;
    (** maps current idents to (pre)types *)
    idents : Data_types.VarTy.t Ident.Env.t;
    (** maps existential (annotation) variables to types *)
    exists : Data_types.VarTy.t Utils.Int_map.t;
  }

let initial_typing_env info =
  {
    intf_env = info#interfaces;
    current_constr = Names.ShortEnv.empty;
    current_nodes = Names.ShortEnv.empty;
    idents = Ident.Env.empty;
    exists = Utils.Int_map.empty;
  }

let print_env fmt env =
  Format.fprintf fmt "Ident env:@\n";
  Ident.Env.iter
    (fun k ty ->
      Format.fprintf fmt " %a -> %a@\n"
        Ident.print k
        VarTy.print ty) env.idents

let find_env local global env ln =
  let open Names in
  match ln.modn with
  | LocalModule -> Names.ShortEnv.find ln.shortn (local env)
  | Module modn -> global ln.shortn (Names.ShortEnv.find modn env.intf_env)

let find_constr env ln =
  let global shortn intf =
    Names.ShortEnv.find shortn intf.Interface.i_constrs
  in
  let tyn = find_env (fun env -> env.current_constr) global env ln in
  Names.make_longname ln.Names.modn tyn

let add_type_constrs env tyn constr_l =
  let add constr_env constr = Names.ShortEnv.add constr tyn constr_env in
  {
    env with
      current_constr = List.fold_left add env.current_constr constr_l;
  }

let find_node =
  let global shortn intf =
    let open Interface in
    data_signature_of_node_item (Names.ShortEnv.find shortn intf.i_nodes)
  in
  find_env (fun env -> env.current_nodes) global

let add_node env nn dsig =
  { env with current_nodes = Names.ShortEnv.add nn dsig env.current_nodes; }

let find_ident env id = Ident.Env.find id env.idents

let reset_env env =
  {
    env with
      idents = Ident.Env.empty;
      exists = Utils.Int_map.empty;
  }

let add_fresh_type_for_var env id =
  { env with idents = Ident.Env.add id (fresh_ty ()) env.idents; }

let rec add_fresh_types_for_pat env p =
  match p.p_desc with
  | P_var id | P_condvar (id, _) -> add_fresh_type_for_var env id
  | P_tuple p_l -> List.fold_left add_fresh_types_for_pat env p_l
  | P_clock_annot (p, _) | P_type_annot (p, _) | P_spec_annot (p, _) ->
    add_fresh_types_for_pat env p
  | P_split w ->
    Ast_misc.fold_upword
      (Utils.flip add_fresh_types_for_pat)
      (fun _ env -> env)
      w
      env

let rec pre_ty_of_ty_annotation env ty =
  match ty with
  | Ty_var i ->
    (
      try env, Utils.Int_map.find i env.exists
      with Not_found ->
        let ty = fresh_ty () in
        { env with exists = Utils.Int_map.add i ty env.exists; }, ty
    )
  | Ty_scal tys -> env, PreTy.Pty_scal tys
  | Ty_cond ty ->
    let env, pty = pre_ty_of_ty_annotation env ty in
    env, PreTy.Pty_cond pty
  | Ty_prod ty_l ->
    let env, pty_l = Utils.mapfold_left pre_ty_of_ty_annotation env ty_l in
    env, PreTy.Pty_prod pty_l

(** {2 High-level utilities} *)

let int_ty = PreTy.Pty_scal Tys_int
let bool_ty = PreTy.Pty_scal Tys_bool
let float_ty = PreTy.Pty_scal Tys_float
let user_ty ln = PreTy.Pty_scal (Tys_user ln)
let tuple_ty ty_l = PreTy.Pty_prod ty_l
let cond_ty ty = PreTy.Pty_cond ty

module A =
struct
  type new_annot =
    | Exp of Data_types.VarTy.t
    | Node of Data_types.VarTy.t * Data_types.VarTy.t

  let print_new_annot fmt na =
    match na with
    | Exp ty -> Data_types.VarTy.print fmt ty
    | Node (ty1, ty2) ->
      Format.fprintf fmt "%a -> %a"
        Data_types.VarTy.print ty1
        Data_types.VarTy.print ty2
end

module ANN_INFO = Acids_utils.MakeAnnot(Acids_scoped)(A)
module M = Acids.Make(ANN_INFO)

let annotate_exp info ty =
  ANN_INFO.annotate info (A.Exp ty)

let annotate_node info inp_ty out_ty =
  ANN_INFO.annotate info (A.Node (inp_ty, out_ty))

let annotate_dummy info =
  ANN_INFO.annotate info (A.Exp bool_ty)

module MORPH =
struct
  module IN_INFO = M.I
  module OUT_INFO = Acids_typed.Info

  open ANN_INFO
  open A

  let update_clock_exp_info { new_annot = na; old_annot = (); } =
    match na with
    | Node _ -> invalid_arg "update_clock_exp_info"
    | Exp pty ->
      let ty = Data_types.ty_of_pre_ty pty in
      (
        match ty with
        | Ty_scal tys ->
          object method ci_data = tys end
        | _ -> invalid_arg "update_clock_exp_info"
      )

  let update_static_exp_info { new_annot = na; old_annot = (); } =
    match na with
    | Node _ -> invalid_arg "update_static_exp_info"
    | Exp pty ->
      let ty = Data_types.ty_of_pre_ty pty in
      (
        match ty with
        | Ty_scal tys ->
          object method pwi_data = tys end
        | _ -> invalid_arg "update_static_exp_info"
      )

  let update_exp_info { new_annot = na; old_annot = (); } =
    match na with
    | Node _ -> invalid_arg "update_clock_exp_info"
    | Exp pty ->
      let ty = Data_types.ty_of_pre_ty pty in
      object method ei_data = ty end

  let update_app_info _ = ()

  let update_block_info _ = ()

  let update_pat_info { new_annot = na; old_annot = (); } =
    match na with
    | Node _ -> invalid_arg "update_clock_exp_info"
    | Exp pty ->
      let ty = Data_types.ty_of_pre_ty pty in
      object method pi_data = ty end

  let update_eq_info _ = ()

  let update_domain_info _ = ()

  let update_node_info { new_annot = na; old_annot = ctx; } =
    match na with
    | Exp _ -> invalid_arg "update_node_info"
    | Node (inp, out) ->
      object
        method ni_ctx = ctx
        method ni_data = Data_types.generalize_sig inp out
      end
end

module EXTRACT = Acids_utils.MakeMap(M)(Acids_typed)(MORPH)

(** {2 Typing AST nodes} *)

let rec type_econstr env ec =
  let open Ast_misc in
  match ec with
  | Ec_bool _ -> bool_ty
  | Ec_int _ -> int_ty
  | Ec_constr cn -> user_ty (find_constr env cn)

and type_const env c =
  let open Ast_misc in
  match c with
  | Cconstr ec -> type_econstr env ec
  | Cfloat _ -> float_ty

and type_clock_exp env ce =
  let ced, ty =
    match ce.ce_desc with
    | Ce_condvar id ->
      let ty = cond_ty (fresh_ty ()) in
      unify ce.ce_loc ty (find_ident env id);
      M.Ce_condvar id, ty

    | Ce_pword w ->
      let w, ty = type_static_word env w in
      M.Ce_pword w, ty

    | Ce_equal (ce, se) ->
      let ce, ty = type_clock_exp env ce in
      let se = expect_static_exp env ty se in
      M.Ce_equal (ce, se), bool_ty
  in
  {
    M.ce_desc = ced;
    M.ce_loc = ce.ce_loc;
    M.ce_info = annotate_exp ce.ce_info ty;
  },
  ty

and expect_clock_exp env expected_ty ce =
  let ce, effective_ty = type_clock_exp env ce in
  unify ce.M.ce_loc expected_ty effective_ty;
  ce

and type_static_exp env se =
  let open Acids_scoped.Info in
  let ty =
    match se.se_desc with
    | Se_var v -> find_ident env v
    | Se_econstr ec -> type_econstr env ec
  in
  {
    M.se_desc = se.se_desc;
    M.se_loc = se.se_loc;
    M.se_info = annotate_exp se.se_info ty;
  },
  ty

and expect_static_exp env expected_ty se =
  let se, effective_ty = type_static_exp env se in
  unify se.M.se_loc expected_ty effective_ty;
  se

and type_exp env e =
  let ed, ty =
    match e.e_desc with
    | E_var id ->
      M.E_var id, find_ident env id

    | E_const c ->
      M.E_const c, type_const env c

    | E_fst e ->
      let ty_l = fresh_ty () in
      let ty_r = fresh_ty () in
      let ty_tuple = tuple_ty [ty_l; ty_r] in
      let e = expect_exp env ty_tuple e in
      M.E_fst e, ty_l

    | E_snd e ->
      let ty_l = fresh_ty () in
      let ty_r = fresh_ty () in
      let ty_tuple = tuple_ty [ty_l; ty_r] in
      let e = expect_exp env ty_tuple e in
      M.E_fst e, ty_r

    | E_tuple e_l ->
      let e_l, ty_l = List.split (List.map (type_exp env) e_l) in
      M.E_tuple e_l, tuple_ty ty_l

    | E_fby (e1, e2) ->
      let e1, ty = type_exp env e1 in
      let e2 = expect_exp env ty e2 in
      M.E_fby (e1, e2), ty

    | E_ifthenelse (e1, e2, e3) ->
      let e1 = expect_exp env bool_ty e1 in
      let e2, ty = type_exp env e2 in
      let e3 = expect_exp env ty e3 in
      M.E_ifthenelse (e1, e2, e3), ty

    | E_app (app, e) ->
      let app, ty_inp, ty_out = type_app env app in
      let e = expect_exp env ty_inp e in
      M.E_app (app, e), ty_out

    | E_where (e, block) ->
      let block, env = type_block env block in
      let e, ty = type_exp env e in
      M.E_where (e, block), ty

    | E_when (e, ce) ->
      let e, ty = type_exp env e in
      let ce = expect_clock_exp env (cond_ty bool_ty) ce in
      M.E_when (e, ce), ty

    | E_split (ce, e', ec_l) ->
      let ce_ty = fresh_ty () in
      let ce = expect_clock_exp env (cond_ty ce_ty) ce in
      List.iter
        (fun ec ->
          let ty = type_econstr env ec in
          unify e.e_loc ce_ty ty)
        ec_l;
      let e', ty = type_exp env e' in
      M.E_split (ce, e', ec_l), ty

    | E_bmerge (ce, e1, e2) ->
      let ce = expect_clock_exp env (cond_ty bool_ty) ce in
      let e1, ty = type_exp env e1 in
      let e2 = expect_exp env ty e2 in
      M.E_bmerge (ce, e1, e2), ty

    | E_merge (ce, c_l) ->
      let ce_ty = fresh_ty () in
      let ce = expect_clock_exp env (cond_ty ce_ty) ce in
      let body_ty = fresh_ty () in
      let type_merge_clause cl =
        let sel_ty = type_econstr env cl.c_sel in
        unify cl.c_loc ce_ty sel_ty;
        {
          M.c_sel = cl.c_sel;
          M.c_body = expect_exp env body_ty cl.c_body;
          M.c_loc = cl.c_loc;
        }
      in
      M.E_merge (ce, List.map type_merge_clause c_l), body_ty

    | E_valof ce ->
      let ty = fresh_ty () in
      let ce = expect_clock_exp env (cond_ty ty) ce in
      M.E_valof ce, ty

    | E_clock_annot (e, ca) ->
      let e, ty = type_exp env e in
      let ca = type_clock_annot env ca in
      M.E_clock_annot (e, ca), ty

    | E_type_annot (e, ta) ->
      let env, ty = pre_ty_of_ty_annotation env ta in
      let e = expect_exp env ty e in
      M.E_type_annot (e, ta), ty

    | E_spec_annot (e, spec) ->
      let spec, ty = type_spec env spec in
      let e = expect_exp env ty e in
      M.E_spec_annot (e, spec), ty

    | E_dom (e, dom) ->
      let e, ty = type_exp env e in
      let dom = type_domain env dom in
      M.E_dom (e, dom), ty

    | E_buffer e ->
      let e, ty = type_exp env e in
      M.E_buffer e, ty

  in
  {
    M.e_desc = ed;
    M.e_loc = e.e_loc;
    M.e_info = annotate_exp e.e_info ty;
  },
  ty

and expect_exp env expected_ty e =
  let e, effective_ty = type_exp env e in
  unify e.M.e_loc expected_ty effective_ty;
  e

and type_app env app =
  let ty_sig = find_node env app.a_op in
  let inp_ty, out_ty = Data_types.instantiate_sig fresh_ty ty_sig in
  {
    M.a_op = app.a_op;
    M.a_info = annotate_dummy app.a_info;
    M.a_loc = app.a_loc;
  },
  inp_ty,
  out_ty

and type_pattern p env =
  let pd, ty, env =
    match p.p_desc with
    | P_var id ->
      M.P_var id, find_ident env id, env

    | P_condvar (id, specs) ->
      let ty = fresh_ty () in
      let specs = List.map (expect_spec env ty) specs in
      let ty = cond_ty ty in
      let ty' = find_ident env id in
      unify p.p_loc ty ty';
      M.P_condvar (id, specs), ty, env

    | P_tuple p_l ->
      let pty_l, env = Utils.mapfold type_pattern p_l env in
      let p_l, ty_l = List.split pty_l in
      M.P_tuple p_l, tuple_ty ty_l, env

    | P_clock_annot (p, ca) ->
      let (p, ty), env = type_pattern p env in
      M.P_clock_annot (p, type_clock_annot env ca), ty, env

    | P_type_annot (p, ta) ->
      let env, ty = pre_ty_of_ty_annotation env ta in
      let p, env = expect_pat ty p env in
      M.P_type_annot (p, ta), ty, env

    | P_spec_annot (p, spec) ->
      let spec, ty = type_spec env spec in
      let p, env = expect_pat ty p env in
      M.P_spec_annot (p, spec), ty, env

    | P_split w ->
      let ty = fresh_ty () in
      let expect_pat = expect_pat ty in
      let expect_static_exp_int e env = expect_static_exp env int_ty e, env in
      let w, env =
        Ast_misc.mapfold_upword expect_pat expect_static_exp_int w env
      in
      M.P_split w, ty, env
  in
  (
    {
      M.p_desc = pd;
      M.p_loc = p.p_loc;
      M.p_info = annotate_exp p.p_info ty;
    },
    ty),
  env

and expect_pat expected_ty p env =
  let (p, effective_ty), env = type_pattern p env in
  unify p.M.p_loc expected_ty effective_ty;
  p, env

and type_eq env eq =
  let (lhs, ty), env = type_pattern eq.eq_lhs env in
  let rhs = expect_exp env ty eq.eq_rhs in
  env,
  {
    M.eq_lhs = lhs;
    M.eq_rhs = rhs;
    M.eq_loc = eq.eq_loc;
    M.eq_info = annotate_dummy eq.eq_info;
  }

and type_block env block =
  let enrich env eq = add_fresh_types_for_pat env eq.eq_lhs in
  let env = List.fold_left enrich env block.b_body in
  let env, body = Utils.mapfold_left type_eq env block.b_body in
  {
    M.b_body = body;
    M.b_loc = block.b_loc;
    M.b_info = annotate_dummy block.b_info;
  },
  env

and type_clock_annot env ca =
  match ca with
  | Ca_var i -> M.Ca_var i
  | Ca_on (ca, ce) ->
    let ca = type_clock_annot env ca in
    let ty = fresh_ty () in
    let ce = expect_clock_exp env (cond_ty ty) ce in
    M.Ca_on (ca, ce)

and type_domain env dom =
  {
    M.d_base_clock = Utils.map_opt (type_clock_annot env) dom.d_base_clock;
    M.d_par = dom.d_par;
    M.d_info = annotate_dummy dom.d_info;
  }

and type_spec env spec =
  let sd, ty =
    match spec.s_desc with
    | Unspec -> M.Unspec, fresh_ty ()
    | Word w ->
      let w, ty = type_static_word env w in
      M.Word w, ty
    | Interval (l, u) ->
      let l = expect_static_exp env int_ty l in
      let u = expect_static_exp env int_ty u in
      M.Interval (l, u), int_ty
  in
  {
    M.s_desc = sd;
    M.s_loc = spec.s_loc;
  },
  ty

and expect_spec env expected_ty spec =
  let spec, actual_ty = type_spec env spec in
  unify spec.M.s_loc expected_ty actual_ty;
  spec

and type_static_word env w =
  let ty = fresh_ty () in
  let expect = expect_static_exp env ty in
  let expect_int = expect_static_exp env int_ty in
  Ast_misc.map_upword expect expect_int w, ty

let type_node_def env nd =
  reset_ty ();
  let env = add_fresh_types_for_pat env nd.n_input in
  let (p, inp_ty), env = type_pattern nd.n_input env in
  let e, out_ty = type_exp env nd.n_body in
  let ty_sig = Data_types.generalize_sig inp_ty out_ty in
  {
    M.n_name = nd.n_name;
    M.n_input = p;
    M.n_body = e;
    M.n_pragma = nd.n_pragma;
    M.n_static = nd.n_static;
    M.n_loc = nd.n_loc;
    M.n_info = annotate_node nd.n_info inp_ty out_ty;
  },
  add_node env nd.n_name ty_sig

let type_node_decl env nd =
  {
    M.decl_name = nd.decl_name;
    M.decl_data = nd.decl_data;
    M.decl_static = nd.decl_static;
    M.decl_interv = nd.decl_interv;
    M.decl_clock = nd.decl_clock;
    M.decl_loc = nd.decl_loc;
  },
  add_node env nd.decl_name nd.decl_data

let type_type_def env td =
  {
    M.ty_name = td.ty_name;
    M.ty_body = td.ty_body;
    M.ty_loc = td.ty_loc;
  },
  add_type_constrs env td.ty_name td.ty_body

let type_phrase env phr =
  match phr with
  | Phr_node_def nd ->
    let nd, env = type_node_def env nd in
    env, M.Phr_node_def nd
  | Phr_node_decl nd ->
    let nd, env = type_node_decl env nd in
    env, M.Phr_node_decl nd
  | Phr_type_def td ->
    let td, env = type_type_def env td in
    env, M.Phr_type_def td

let type_file file =
  let _, body =
    Utils.mapfold_left type_phrase (initial_typing_env file.f_info) file.f_body
  in
  {
    M.f_name = file.f_name;
    M.f_imports = file.f_imports;
    M.f_info = file.f_info;
    M.f_body = body;
  }

(** {2 Moving from pretypes to types} *)

let type_file
    ctx
    (file : < interfaces : Interface.env > Acids_scoped.file) =
  let intermediate_file = type_file file in
  let final_file = EXTRACT.extract_file intermediate_file in
  ctx, final_file

(** {2 Putting it all together} *)

let type_ =
  let open Pass_manager in
  P_transform
    (Frontend_utils.make_transform
       ~print_out:Acids_typed.print_file
       "data_typing"
       type_file)
