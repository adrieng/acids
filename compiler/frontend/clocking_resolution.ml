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
open PreTySt
open PreTy

(** {2 Errors} *)

type error =
  | Occur_check_st of Loc.t * int * VarTySt.t
  | Occur_check_ty of Loc.t * int * VarTy.t

exception Resolution_error of error

let print_error fmt err =
  match err with
  | Occur_check_st (l, i, st) ->
    Format.fprintf fmt "%aStream type variable %d occurs in %a"
      Loc.print l
      i
      VarTySt.print st
  | Occur_check_ty (l, i, ty) ->
    Format.fprintf fmt "%aClock type variable %d occurs in %a"
      Loc.print l
      i
      VarTy.print ty

let occur_check_st l id st =
  raise (Resolution_error (Occur_check_st (l, id, st)))

let occur_check_ty l id ty =
  raise (Resolution_error (Occur_check_ty (l, id, ty)))

(** {2 Utilities} *)

let print_system fmt sys =
  Format.fprintf fmt "{ @[<v>%a@] }"
    (Utils.print_list_r print_ty_constr ";") sys

let p f x =
  if !Compiler_options.print_clock_info
  then Format.printf "%a@." f x

let p_sys s sys =
  p
    (fun fmt sys -> Format.fprintf fmt "%s: %a@." s print_system sys)
    sys

let occur_check_st loc id st =
  let open VarTySt in
  let rec check st =
    match unalias_st st with
    | Pst_var { v_id = id'; } ->
      if id = id' then occur_check_st loc id st
    | Pst_on (st, _) -> check st
  in
  match unalias_st st with
  | Pst_var _ -> ()
  | Pst_on (st, _) -> check st

let occur_check_ty loc id ty =
  let open VarTy in
  let rec check ty =
    match unalias_ty ty with
    | Pct_var { v_id = id'; } ->
      if id = id' then occur_check_ty loc id ty
    | Pct_stream _ -> ()
    | Pct_prod ty_l -> List.iter check ty_l
  in
  match unalias_ty ty with
  | Pct_var _ | Pct_stream _ -> ()
  | Pct_prod ty_l -> List.iter check ty_l

(** {2 Constraint solving} *)

let simplify_equality_constraints sys =
  let unify_st loc sys st1 st2 =
    let open VarTySt in
    let st1 = unalias_st st1 in
    let st2 = unalias_st st2 in
    match st1, st2 with
    | Pst_var v1, Pst_var v2 ->
      if v1.v_id <> v2.v_id then v2.v_link <- Some st1;
      sys

    | Pst_var v, st | st, Pst_var v ->
      occur_check_st loc v.v_id st;
      v.v_link <- Some st;
      sys

    | Pst_on _, Pst_on _ ->
      { loc = loc; desc = Tc_equal_st (st1, st2); } :: sys
  in

  let rec unify_ty loc sys ty1 ty2 =
    let open VarTy in
    let ty1 = unalias_ty ty1 in
    let ty2 = unalias_ty ty2 in
    match ty1, ty2 with
    | Pct_var v1, Pct_var v2 ->
      if v1.v_id <> v2.v_id then v2.v_link <- Some ty1;
      sys

    | Pct_var v, ty | ty, Pct_var v ->
      occur_check_ty loc v.v_id ty;
      v.v_link <- Some ty;
      sys

    | Pct_stream st1, Pct_stream st2 ->
      unify_st loc sys st1 st2

    | Pct_prod ty_l1, Pct_prod ty_l2 ->
      List.fold_left2 (unify_ty loc) sys ty_l1 ty_l2

    | Pct_prod ty_l, Pct_stream st | Pct_stream st, Pct_prod ty_l ->
      synchronize loc sys st ty_l

  and synchronize loc sys st ty_l =
    let unif sys ty = unify_ty loc sys (Pct_stream st) ty in
    List.fold_left unif sys ty_l
  in

  let simplify_constraints sys c =
    match c.desc with
    | Tc_adapt _ -> c :: sys
    | Tc_equal (ty1, ty2) -> unify_ty c.loc sys ty1 ty2
    | Tc_equal_st (st1, st2) -> unify_st c.loc sys st1 st2
  in
  List.fold_left simplify_constraints [] sys

(** {2 Top-level function} *)

let solve_constraints sys =
  p_sys "Initial system" sys;
  let sys = simplify_equality_constraints sys in
  p_sys "System with simplified equality constraints" sys;
  ()
