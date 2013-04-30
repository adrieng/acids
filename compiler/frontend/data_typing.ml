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

(** {2 High-level utilities} *)

let int_ty = PreTy.Pty_scal Tys_int
let bool_ty = PreTy.Pty_scal Tys_bool

let reset_ty, fresh_ty =
  let open PreTy in
  let open VarTy in
  let r = ref 0 in
  (fun () -> r := 0),
  (fun () -> incr r; Pty_var { v_link = None; v_id = !r; })

(** {2 Typing AST nodes} *)

let rec type_clock_exp env ce =
  let ty =
    match ce.ce_desc with
    | Ce_var v -> Ident.Env.find v env
    | Ce_pword w ->
      let ty = fresh_ty () in
      let expect = expect_exp env ty in
      Ast_misc.iter_upword expect expect w;
      if not (try_unify_no_conflict ce.ce_loc ty int_ty)
      then unify ce.ce_loc ty bool_ty;
      ty
    | Ce_equal (ce, e) ->
      let ty = type_clock_exp env ce in
      expect_exp env ty e;
      ty
    | Ce_iter ce ->
      expect_clock_exp env ce int_ty
  in
  assert false

and expect_clock_exp env ce ty = assert false

and type_exp env e = assert false

and expect_exp env e ty = assert false

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
