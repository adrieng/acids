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

type ty_scal =
  | Is_top
  | Is_inter of Interval.t

type ty =
  | It_scal of ty_scal
  | It_prod of ty list

type ty_sig = { input : ty; output : ty; }

let print_ty_scal fmt is =
  match is with
  | Is_top -> Format.fprintf fmt "T"
  | Is_inter it -> Interval.print fmt it

let rec print_ty fmt ity =
  match ity with
  | It_scal is -> print_ty_scal fmt is
  | It_prod ity_l ->
    Format.fprintf fmt "(@[%a@])"
      (Utils.print_list_r print_ty " *") ity_l

let print_sig fmt cs =
  Format.fprintf fmt "@[%a -> %a@]"
    print_ty cs.input
    print_ty cs.output

let printing_prefix = "in"

let print_interval_ann =
  Ast_misc.print_annot
    Compiler_options.print_interval_info
    printing_prefix
    Interval.print

let print_ty_scal_ann =
  Ast_misc.print_annot
    Compiler_options.print_interval_info
    printing_prefix
    print_ty_scal

let print_ty_ann =
  Ast_misc.print_annot
    Compiler_options.print_interval_info
    printing_prefix
    print_ty

let print_sig_ann =
  Ast_misc.print_annot
    Compiler_options.print_interval_info
    printing_prefix
    print_sig

let join_scal ts1 ts2 =
  match ts1, ts2 with
  | Is_top, _ | _, Is_top -> Is_top
  | Is_inter i1, Is_inter i2 -> Is_inter (Interval.join i1 i2)

exception Ill_typed

let rec join ty1 ty2 =
  match ty1, ty2 with
  | It_scal ts1, It_scal ts2 -> It_scal (join_scal ts1 ts2)
  | It_prod ty_l1, It_prod ty_l2 -> It_prod (List.map2 join ty_l1 ty_l2)
  | It_scal _, It_prod _ | It_prod _, It_scal _ -> raise Ill_typed

exception Not_subset

let subset_scal ts1 ts2 =
  match ts1, ts2 with
  | _, Is_top -> ()
  | Is_inter i1, Is_inter i2 ->
    if not (Interval.le i1 i2) then raise Not_subset
  | Is_top, Is_inter _ -> raise Not_subset

let rec subset ty1 ty2 =
  match ty1, ty2 with
  | It_scal ts1, It_scal ts2 -> subset_scal ts1 ts2
  | It_prod ty_l1, It_prod ty_l2 ->
    List.iter2 subset ty_l1 ty_l2

  | It_prod ty_l, It_scal _ ->
    let ty1 = Utils.fold_left_1 join ty_l in
    subset ty1 ty2

  | It_scal _, It_prod ty_l ->
    let ty2 = Utils.fold_left_1 join ty_l in
    subset ty1 ty2

let subset ty1 ty2 = try subset ty1 ty2; true with Not_subset -> false
