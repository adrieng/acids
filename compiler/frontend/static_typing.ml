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

(** {1 Static typing} *)

open Acids_interval
open Static_types

(** Static typing is a very simple (two-element) type system used to distinguish
    which nodes have to be inlined. It drives static evaluation later on. *)

(** {2 Errors} *)

type error =
  | Unification_error of Static_types.error

exception Typing_error of error

let unification_error err =
  raise (Typing_error (Unification_error err))

(** {2 Unification} *)

let unify loc ty1 ty2 =
  try Static_types.unify loc ty1 ty2
  with Static_types.Unification_error err -> unification_error err

(** {2 Low-level utilities} *)

let reset_ty, fresh_ty =
  let open PreTy in
  let open VarTy in
  let r = ref 0 in
  (fun () -> r := 0),
  (fun () -> incr r; Psy_var { v_link = None; v_id = !r; })

(** {2 Typing environments} *)

type typing_env =
  {
    (** maps module names to interfaces *)
    intf_env : Interface.t Names.ShortEnv.t;
    (** maps constructors from the current module to type names *)
    current_constr : Names.shortname Names.ShortEnv.t;
    (** maps nodes from the current module to type signatures *)
    current_nodes : ty_sig Names.ShortEnv.t;
    (** maps current idents to (pre)types *)
    idents : VarTy.t Ident.Env.t;
    (** subtyping constraint system *)
    mutable constr : Static_types.constr list;
  }

let initial_typing_env info =
  {
    intf_env = info#interfaces;
    current_constr = Names.ShortEnv.empty;
    current_nodes = Names.ShortEnv.empty;
    idents = Ident.Env.empty;
    constr = [];
  }

let reset_env env = { env with idents = Ident.Env.empty; }

let find_ident env id = Ident.Env.find id env.idents

let add_fresh_type_for_var env id =
  { env with idents = Ident.Env.add id (fresh_ty ()) env.idents; }

let add_constraint env c = env.constr <- c :: env.constr

(** {2 High-level utilities} *)

let static_ty = PreTy.Psy_scal S_static
let dynamic_ty = PreTy.Psy_scal S_dynamic
let tuple_ty ty_l = PreTy.Psy_prod ty_l

module A =
struct
  type new_annot =
  | Exp of VarTy.t
  | Node of VarTy.t * VarTy.t

  let print_new_annot fmt na =
    match na with
    | Exp ty -> VarTy.print fmt ty
    | Node (ty1, ty2) ->
      Format.fprintf fmt "%a -> %a"
        VarTy.print ty1
        VarTy.print ty2
end

module ANN_INFO = Acids_utils.MakeAnnot(Acids_interval)(A)
module M = Acids.Make(ANN_INFO)

let annotate_exp e ty = ANN_INFO.annotate e.e_info (A.Exp ty)
let annotate_clock_exp ce ty = ANN_INFO.annotate ce.ce_info (A.Exp ty)
let annotate_node node inp_ty out_ty =
  ANN_INFO.annotate node.n_info (A.Node (inp_ty, out_ty))
let annotate_dummy dom =
  ANN_INFO.annotate dom.d_info (A.Exp static_ty)

module MORPH =
struct
  module IN_INFO = M.I
  module OUT_INFO = Acids_typed.Info

  open ANN_INFO
  open A

  let update_clock_exp_info { new_annot = na; old_annot = info; } =
    match na with
    | Node _ -> invalid_arg "update_clock_exp_info"
    | Exp pty ->
      let ty = ty_of_pre_ty pty in
      (
        match ty with
        | Sy_scal tys ->
          object
            method ci_data = info#ci_data
            method ci_interv = info#ci_interv
            method ci_static = ty
          end
        | _ -> invalid_arg "update_clock_exp_info"
      )

  let update_exp_info { new_annot = na; old_annot = info; } =
    match na with
    | Node _ -> invalid_arg "update_clock_exp_info"
    | Exp pty ->
      let ty = ty_of_pre_ty pty in
      object
        method ei_data = info#ei_data
        method ei_interv = info#ei_interv
        method ei_static = ty
      end

  let update_app_info _ = ()

  let update_block_info _ = ()

  let update_pat_info { new_annot = na; old_annot = info; } =
    match na with
    | Node _ -> invalid_arg "update_clock_exp_info"
    | Exp pty ->
      let ty = ty_of_pre_ty pty in
      object
        method pi_data = info#pi_data
        method pi_interv = info#pi_interv
        method pi_static = ty
      end

  let update_eq_info _ = ()

  let update_domain_info _ = ()

  let update_node_info  { new_annot = na; old_annot = info; } =
    match na with
    | Exp _ -> invalid_arg "update_node_info"
    | Node (inp, out) ->
      object
        method ni_data = info#ni_data
        method ni_interv = info#ni_interv
        method ni_static =
          {
            input = ty_of_pre_ty inp;
            output = ty_of_pre_ty out;
          }
      end
end

let exp_type e = e.M.e_info.ANN_INFO.new_annot

(** {2 Typing AST nodes} *)

let rec type_clock_exp env ce =
  let loc = ce.ce_loc in
  let ced, ty =
    match ce.ce_desc with
    | Ce_var id ->
      M.Ce_var id, find_ident env id

    | Ce_pword w ->
      let expect = expect_exp loc env static_ty in
      let w = Ast_misc.map_upword expect expect w in
      let ty =
        if Ast_misc.is_constant_pword w
        then static_ty
        else dynamic_ty
      in
      M.Ce_pword w, ty

    | Ce_equal (ce, e) ->
      let ce, ty = type_clock_exp env ce in
      let e = expect_exp loc env static_ty e in
      M.Ce_equal (ce, e), ty

    | Ce_iter ce ->
      let ce, ty = type_clock_exp env ce in
      M.Ce_iter ce, ty
  in
  {
    M.ce_desc = ced;
    M.ce_loc = ce.ce_loc;
    M.ce_info = annotate_clock_exp ce ty;
  },
  ty

and type_exp env e =
  let loc = e.e_loc in
  let ed, ty =
    match e.e_desc with
    | E_var v ->
      M.E_var v, find_ident env v

    | E_const c ->
      M.E_const c, fresh_ty ()

    | E_fst e ->
      let ty_l = fresh_ty () in
      let ty_r = fresh_ty () in
      let e = expect_exp loc env (tuple_ty [ty_l; ty_r]) e in
      M.E_fst e, ty_l

    | E_snd e ->
      let ty_l = fresh_ty () in
      let ty_r = fresh_ty () in
      let e = expect_exp loc env (tuple_ty [ty_l; ty_r]) e in
      M.E_snd e, ty_r

    | E_tuple e_l ->
      let ety_l = List.map (type_exp env) e_l in
      let e_l, ty_l = List.split ety_l in
      M.E_tuple e_l, tuple_ty ty_l

    | E_fby (e1, e2) ->
      let e1, _ = type_exp env e1 in
      let e2, _ = type_exp env e2 in
      M.E_fby (e1, e2), dynamic_ty

    | E_ifthenelse (e1, e2, e3) ->
      let e1, ty = type_exp env e1 in
      let e2 = expect_exp loc env ty e2 in
      let e3 = expect_exp loc env ty e3 in
      M.E_ifthenelse (e1, e2, e3), ty

    | E_app _ -> assert false (* TODO *)

    | E_where _ -> assert false (* TODO *)

    | E_when (e, ce) ->
      let e, ty = type_exp env e in
      let ce, _ = type_clock_exp env ce in
      M.E_when (e, ce), ty

    | E_split (ce, e, ec_l) ->
      let ce, _ = type_clock_exp env ce in
      let e, ty = type_exp env e in
      M.E_split (ce, e, ec_l), ty

    | E_bmerge (ce, e1, e2) ->
      let ce, ty = type_clock_exp env ce in
      let e1 = expect_exp loc env ty e1 in
      let e2 = expect_exp loc env ty e2 in
      M.E_bmerge (ce, e1, e2), ty

    | E_merge (ce, c_l) ->
      let ce, ty = type_clock_exp env ce in
      let c_l =
        List.map
          (fun ec ->
            let e = expect_exp loc env ty ec.c_body in
            {
              M.c_sel = ec.c_sel;
              M.c_body = e;
              M.c_loc = ec.c_loc;
            })
          c_l
      in
      M.E_merge (ce, c_l), ty

    | E_valof ce ->
      let ce, ty = type_clock_exp env ce in
      M.E_valof ce, ty

    | E_clock_annot (e, cka) ->
      let e, ty = type_exp env e in
      let cka = type_clock_annot env cka in
      M.E_clock_annot (e, cka), ty

    | E_type_annot (e, ta) ->
      let e, ty = type_exp env e in
      M.E_type_annot (e, ta), ty

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
    M.e_info = annotate_exp e ty;
  },
  ty

and expect_exp loc env expected_ty e =
  let e, actual_ty = type_exp env e in
  add_constraint env (Static_types.make_constraint loc actual_ty expected_ty);
  e

and type_merge_clause env c =
  let body, ty = type_exp env c.c_body in
  {
    M.c_sel = c.c_sel;
    M.c_body = body;
    M.c_loc = c.c_loc;
  },
  ty

and type_clock_annot env cka =
  match cka with
  | Ca_var i -> M.Ca_var i
  | Ca_on (cka, ce) ->
    let cka = type_clock_annot env cka in
    let ce, _ = type_clock_exp env ce in
    M.Ca_on (cka, ce)

and type_domain env dom =
  {
    M.d_base_clock = Utils.map_opt (type_clock_annot env) dom.d_base_clock;
    M.d_par = dom.d_par;
    M.d_info = annotate_dummy dom;
  }

(** {2 Moving from pretypes to types} *)

let type_file
    ctx
    (file
       : < interfaces : Interface.t Names.ShortEnv.t > Acids_interval.file) =
  ((assert false)
      :
      Pass_manager.ctx
   * < interfaces : Interface.t Names.ShortEnv.t > Acids_preclock.file)
  (* let intermediate_file = type_file file in *)
  (* let final_file = EXTRACT.extract_file intermediate_file in *)
  (* ctx, final_file *)

(** {2 Putting it all together} *)

let type_ =
  let open Pass_manager in
  P_transform
    (Frontend_utils.make_transform
       ~print_out:Acids_preclock.print_file
       "static_typing"
       type_file)
