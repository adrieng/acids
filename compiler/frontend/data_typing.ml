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

module MakeAst = Acids.Make

open Acids_scoped
open Data_types

(** {1 Data typing}

    Nothing special, really. *)

(** {2 Errors} *)

type error =
  | Unification_conflict of Loc.t * VarTy.t * VarTy.t
  | Unification_occur of Loc.t * int * VarTy.t

exception Typing_error of error

let print_error fmt err =
  match err with
  | Unification_conflict (l, ty1, ty2) ->
    Format.fprintf fmt "%aCould not unify %a with %a"
      Loc.print l
      VarTy.print ty1
      VarTy.print ty2
  | Unification_occur (l, id, ty) ->
    Format.fprintf fmt "%aType variable %d occurs in %a"
      Loc.print l
      id
      VarTy.print ty

let unification_conflict loc ty1 ty2 =
  raise (Typing_error (Unification_conflict (loc, ty1, ty2)))

let unification_occur loc id ty =
  raise (Typing_error (Unification_occur (loc, id, ty)))

(** {2 Unification} *)

let occur_check loc id ty =
  let open PreTy in
  let open VarTy in
  let rec walk ty =
    match ty with
    | Pty_var { v_link = Some ty; } -> walk ty
    | Pty_var { v_link = None; v_id = id'; } ->
      if id = id' then unification_occur loc id ty
    | Pty_scal _ -> ()
    | Pty_prod ty_l -> List.iter walk ty_l
  in
  match ty with
  | Pty_var { v_link = None; } -> ()
  | _ -> walk ty

let unify loc ty1 ty2 =
  let open PreTy in
  let open VarTy in

  let rec u ty1 ty2 =
    match ty1, ty2 with
    (** traverse links *)
    | Pty_var { v_link = Some ty1; }, ty2
    | ty1, Pty_var { v_link = Some ty2; } -> u ty1 ty2

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
      List.iter2 u ty_l1 ty_l2

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
    intf_env : Interface.t Names.ShortEnv.t;
    (** maps constructors from the current module to type names *)
    current_constr : Names.shortname Names.ShortEnv.t;
    (** maps nodes from the current module to type signatures *)
    current_nodes : Data_types.data_sig Names.ShortEnv.t;
    (** maps current idents to (pre)types *)
    idents : Data_types.VarTy.t Ident.Env.t;
  }

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

let find_node =
  let global shortn intf =
    let open Interface in
    data_signature_of_node_item (Names.ShortEnv.find shortn intf.i_nodes)
  in
  find_env (fun env -> env.current_nodes) global

let find_ident env id = Ident.Env.find id env.idents

let add_fresh_type_for_var env id =
  { env with idents = Ident.Env.add id (fresh_ty ()) env.idents; }

let rec add_fresh_types_for_pat env p =
  match p.p_desc with
  | P_var id -> add_fresh_type_for_var env id
  | P_tuple p_l -> List.fold_left add_fresh_types_for_pat env p_l
  | P_clock_annot (p, _) -> add_fresh_types_for_pat env p
  | P_split w ->
    Ast_misc.fold_upword
      (Utils.flip add_fresh_types_for_pat)
      (fun _ env -> env)
      w
      env

(** {2 High-level utilities} *)

let int_ty = PreTy.Pty_scal Tys_int
let bool_ty = PreTy.Pty_scal Tys_bool
let float_ty = PreTy.Pty_scal Tys_float
let user_ty ln = PreTy.Pty_scal (Tys_user ln)
let tuple_ty ty_l = PreTy.Pty_prod ty_l

(** {2 Typing AST nodes} *)

module Info =
struct
  type var = Ident.t
  let print_var = Ident.print

  type clock_exp_info = Data_types.VarTy.t
  let print_clock_exp_info = Data_types.VarTy.print

  type exp_info = Data_types.VarTy.t
  let print_exp_info = Data_types.VarTy.print

  type app_info = Data_types.VarTy.t list
  let print_app_info = Utils.print_list_r Data_types.VarTy.print ","

  type block_info = unit
  let print_block_info _ () = ()

  type pat_info = Data_types.VarTy.t
  let print_pat_info = Data_types.VarTy.print

  type eq_info = Data_types.VarTy.t
  let print_eq_info = Data_types.VarTy.print

  type node_info = Data_types.VarTy.t * Data_types.VarTy.t
  let print_node_info fmt (inp, out) =
    Format.fprintf fmt "%a -> %a"
      Data_types.VarTy.print inp
      Data_types.VarTy.print out
end

module M = MakeAst(Info)

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
  | Cword _ -> int_ty

and type_clock_exp env ce =
  let ced, ty =
    match ce.ce_desc with
    | Ce_var id ->
      M.Ce_var id, find_ident env id

    | Ce_pword w ->
      let ty = fresh_ty () in
      let expect = expect_exp env ty in
      let w = Ast_misc.map_upword expect expect w in
      M.Ce_pword w, ty

    | Ce_equal (ce, e) ->
      let ce, ty = type_clock_exp env ce in
      let e = expect_exp env ty e in
      M.Ce_equal (ce, e), bool_ty

    | Ce_iter ce ->
      let ce = expect_clock_exp env int_ty ce in
      M.Ce_iter ce, int_ty
  in
  {
    M.ce_desc = ced;
    M.ce_loc = ce.ce_loc;
    M.ce_info = ty;
  },
  ty

and expect_clock_exp env expected_ty ce =
  let ce, effective_ty = type_clock_exp env ce in
  unify ce.M.ce_loc expected_ty effective_ty;
  ce

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

    | E_app _ ->
      assert false

    | E_where (e, block) ->
      let block, env = type_block env block in
      let e, ty = type_exp env e in
      M.E_where (e, block), ty

    | E_when (e, ce) ->
      let e, ty = type_exp env e in
      let ce = expect_clock_exp env bool_ty ce in
      M.E_when (e, ce), ty

    | E_split _ ->
      assert false

    | E_bmerge (ce, e1, e2) ->
      let ce = expect_clock_exp env bool_ty ce in
      let e1, ty = type_exp env e1 in
      let e2 = expect_exp env ty e2 in
      M.E_bmerge (ce, e1, e2), ty

    | E_merge (ce, c_l) ->
      let ce, ce_ty = type_clock_exp env ce in
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
      let ce, ty = type_clock_exp env ce in
      M.E_valof ce, ty

    | E_clockannot (e, ca) ->
      let e, ty = type_exp env e in
      let ca = type_clock_annot env ca in
      M.E_clockannot (e, ca), ty

    | E_dom (e, dom) ->
      let e, ty = type_exp env e in
      let dom = type_domain env dom in
      M.E_dom (e, dom), ty
  in
  {
    M.e_desc = ed;
    M.e_loc = e.e_loc;
    M.e_info = ty;
  },
  ty

and expect_exp env expected_ty e =
  let e, effective_ty = type_exp env e in
  unify e.M.e_loc expected_ty effective_ty;
  e

and type_pattern env p =
  let pd, ty =
    match p.p_desc with
    | P_var id ->
      M.P_var id, find_ident env id

    | P_tuple p_l ->
      let p_l, ty_l = List.split (List.map (type_pattern env) p_l) in
      M.P_tuple p_l, tuple_ty ty_l

    | P_clock_annot (p, ca) ->
      let p, ty = type_pattern env p in
      M.P_clock_annot (p, type_clock_annot env ca), ty

    | P_split w ->
      let expect_exp_int = expect_exp env int_ty in
      let ty = fresh_ty () in
      let expect_pat = expect_pat env ty in
      let w =
        Ast_misc.map_upword expect_pat expect_exp_int w
      in
      M.P_split w, ty
  in
  {
    M.p_desc = pd;
    M.p_loc = p.p_loc;
    M.p_info = ty;
  }, ty

and expect_pat env expected_ty p =
  let p, effective_ty = type_pattern env p in
  unify p.M.p_loc expected_ty effective_ty;
  p

and type_eq env eq =
  let lhs, ty = type_pattern env eq.eq_lhs in
  let rhs = expect_exp env ty eq.eq_rhs in
  {
    M.eq_lhs = lhs;
    M.eq_rhs = rhs;
    M.eq_loc = eq.eq_loc;
    M.eq_info = ty;
  }

and type_block env block =
  let enrich env eq = add_fresh_types_for_pat env eq.eq_lhs in

  let env = List.fold_left enrich env block.b_body in
  let body = List.map (type_eq env) block.b_body in
  {
    M.b_body = body;
    M.b_loc = block.b_loc;
    M.b_info = ();
  },
  env

and type_clock_annot env ca =
  match ca with
  | Ca_var i -> M.Ca_var i
  | Ca_on (ca, ce) ->
    let ca = type_clock_annot env ca in
    let ce, _ = type_clock_exp env ce in
    M.Ca_on (ca, ce)

and type_domain env dom =
  {
    M.d_base_clock = Utils.map_opt (type_clock_annot env) dom.d_base_clock;
    M.d_par = dom.d_par;
  }

(** {2 Moving from pretypes to types} *)

let type_file
    ctx
    (file : < interfaces : Interface.t Names.ShortEnv.t > Acids_scoped.file)
    = ctx, file

(** {2 Putting it all together} *)

let type_ =
  let open Pass_manager in
  P_transform
    (Frontend_utils.make_transform
       ~print_out:Acids_scoped.print_file
       "typing"
       type_file)
