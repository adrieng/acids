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

(** {2 Errors} *)

type error =
  | Non_exhaustive_pattern of Loc.t * Ast_misc.econstr
  | Unification_error of Loc.t * VarTy.t * VarTy.t
  | Unification_occur of Loc.t * VarTy.t

exception Typing_error of error

let print_error fmt err =
  match err with
  | Non_exhaustive_pattern (l, ec) ->
    Format.fprintf fmt "%aThis pattern-matching is not exhaustive@\n"
      Loc.print l;
    Format.fprintf fmt "Here is an example of a value that is not matched:@\n%a"
      Ast_misc.print_econstr ec
  | Unification_error (l, ty1, ty2) ->
    Format.fprintf fmt "%aCould not unify %a with %a"
      Loc.print l
      VarTy.print ty1
      VarTy.print ty2
  | Unification_occur (l, ty) ->
    Format.fprintf fmt "%aType %a is cyclic"
      Loc.print l
      VarTy.print ty

let non_exhaustive_pattern loc ec =
  raise (Typing_error (Non_exhaustive_pattern (loc, ec)))

let unification_error loc ty1 ty2 =
  raise (Typing_error (Unification_error (loc, ty1, ty2)))

let unification_occur loc ty =
  raise (Typing_error (Unification_occur (loc, ty)))

(** {2 Constraints and unification} *)

let occur_check loc id ty =
  let open PreTy in
  let open VarTy in
  let rec walk ty =
    match ty with
    | Pit_var { v_link = Some ty; } -> walk ty
    | Pit_var { v_link = None; v_id = id'; } ->
      if id = id' then unification_occur loc ty
    | Pit_scal _ -> ()
    | Pit_prod ty_l -> List.iter walk ty_l
  in
  match ty with
  | Pit_var { v_link = None; } -> ()
  | _ -> walk ty

let unify loc ty1 ty2 =
  let open PreTy in
  let open VarTy in

  let rec u ty1 ty2 =
    match ty1, ty2 with
    (** traverse links *)
    | Pit_var { v_link = Some ty1; }, ty2
    | ty1, Pit_var { v_link = Some ty2; } -> u ty1 ty2

    (** in-place unification *)
    | Pit_var ({ v_link = None; v_id = id; } as r), ty
    | ty, Pit_var ({ v_link = None; v_id = id; } as r) ->
      occur_check loc id ty;
      r.v_link <- Some ty

    | Pit_scal Is_top, Pit_scal Is_top
    | Pit_scal Is_bot, Pit_scal Is_bot ->
      ()
    | Pit_scal (Is_inter it1), Pit_scal (Is_inter it2) ->
      if Interval.compare it1 it2 = 0
      then ()
      else unification_error loc ty1 ty2

    | Pit_prod ty_l1, Pit_prod ty_l2 ->
      List.iter2 u ty_l1 ty_l2

    | _ ->
      unification_error loc ty1 ty2
  in
  u ty1 ty2

let reset_ty, fresh_ty =
  let open PreTy in
  let open VarTy in
  let r = ref 0 in
  (fun () -> r := 0),
  (fun () -> incr r; Pit_var { v_link = None; v_id = !r; })

(* {2 Typing environments} *)

type typing_env =
  {
    intf_env : Interface.t Names.ShortEnv.t;
    current_types : Names.shortname list Names.ShortEnv.t;
    current_nodes : interval_sig Names.ShortEnv.t;
    idents : VarTy.t Ident.Env.t;
  }

let initial_typing_env info =
  {
    intf_env = info#interfaces;
    current_types = Names.ShortEnv.empty;
    current_nodes = Names.ShortEnv.empty;
    idents = Ident.Env.empty;
  }

let find_ident env id = Ident.Env.find id env.idents

(** {2 High-level utilities} *)

let top_ty = PreTy.Pit_scal Is_top
let bot_ty = PreTy.Pit_scal Is_bot
let bounded_ty max = PreTy.Pit_scal (Is_inter (Interval.make 0n max))

let rec union loc ty1 ty2 =
  match ty1, ty2 with
  | PreTy.Pit_var _, _ | _, PreTy.Pit_var _ ->
    unify loc ty1 ty2;
    ty1

  | PreTy.Pit_scal _, PreTy.Pit_prod _
  | PreTy.Pit_prod _, PreTy.Pit_scal _ ->
    unification_error loc ty1 ty2

  | PreTy.Pit_prod pty_l1, PreTy.Pit_prod pty_l2 ->
    let pty_l = List.map2 (union loc) pty_l1 pty_l2 in
    PreTy.Pit_prod pty_l

  | PreTy.Pit_scal Is_bot, ty | ty, PreTy.Pit_scal Is_bot ->
    ty

  | PreTy.Pit_scal Is_top, _ | _, PreTy.Pit_scal Is_top ->
    PreTy.Pit_scal Is_top

  | PreTy.Pit_scal (Is_inter i1), PreTy.Pit_scal (Is_inter i2) ->
    PreTy.Pit_scal (Is_inter (Interval.join i1 i2))

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

module ANN_INFO = Acids_utils.MakeAnnot(Acids_typed)(A)
module M = Acids.Make(ANN_INFO)

let annotate_exp info ty =
  ANN_INFO.annotate info (A.Exp ty)

let annotate_node info inp_ty out_ty =
  ANN_INFO.annotate info (A.Node (inp_ty, out_ty))

let annotate_dummy info =
  ANN_INFO.annotate info (A.Exp top_ty)

module MORPH =
struct
  module IN_INFO = M.I
  module OUT_INFO = Acids_interval.Info

  open ANN_INFO
  open A

  let update_clock_exp_info { new_annot = na; old_annot = d; } =
    match na with
    | Node _ -> invalid_arg "update_clock_exp_info"
    | Exp pty ->
      let ty = ty_of_pre_ty pty in
      object
        method ci_data = d#ci_data
        method ci_interv = ty
      end

  let update_exp_info { new_annot = na; old_annot = d; } =
    match na with
    | Node _ -> invalid_arg "update_clock_exp_info"
    | Exp pty ->
      let ty = ty_of_pre_ty pty in
      object
        method ei_data = d#ei_data
        method ei_interv = ty
      end

  let update_app_info _ = ()

  let update_block_info _ = ()

  let update_pat_info { new_annot = na; old_annot = d; } =
    match na with
    | Node _ -> invalid_arg "update_clock_exp_info"
    | Exp pty ->
      let ty = ty_of_pre_ty pty in
      object
        method pi_data = d#pi_data
        method pi_interv = ty
      end

  let update_eq_info _ = ()

  let update_domain_info _ = ()

  let update_node_info  { new_annot = na; old_annot = d; } =
    match na with
    | Exp _ -> invalid_arg "update_node_info"
    | Node (inp, out) ->
      object
        method ni_data = d#ni_data
        method ni_interv = Interval_types.generalize_sig inp out
      end
end

module EXTRACT = Acids_utils.MakeMap(M)(Acids_interval)(MORPH)

(** {2 Typing AST nodes} *)

let rec type_clock_exp env ce =
  let open Ast_misc in
  let ced, ty =
    match ce.ce_desc with
    | Ce_var v ->
      M.Ce_var v, find_ident env v

    | Ce_pword w ->
      let w, ty_l =
        let type_exp e ty_l =
          let e, ty = type_exp env e in
          e, ty :: ty_l
        in
        mapfold_upword type_exp type_exp w []
      in
      M.Ce_pword w, List.fold_left (union ce.ce_loc) bot_ty ty_l

    | Ce_equal (ce, e) ->
      let ce, ce_ty = type_clock_exp env ce in
      let e, e_ty = type_exp env e in
      M.Ce_equal (ce, e), bot_ty

    | Ce_iter ce ->
      let ce, ty = type_clock_exp env ce in
      M.Ce_iter ce, assert false
  in
  {
    M.ce_desc = ced;
    M.ce_loc = ce.ce_loc;
    M.ce_info = annotate_exp ce.ce_info ty;
  },
  ty

and type_exp env e =
  assert false

let type_file
    ctx
    (file : < interfaces : Interface.t Names.ShortEnv.t > Acids_typed.file) =
  (assert false
     :
     Pass_manager.ctx
     * < interfaces : Interface.t Names.ShortEnv.t > Acids_interval.file)

(** {2 Putting it all together} *)

let type_ =
  let open Pass_manager in
  P_transform
    (Frontend_utils.make_transform
       ~print_out:Acids_interval.print_file
       "intervals"
       type_file)


