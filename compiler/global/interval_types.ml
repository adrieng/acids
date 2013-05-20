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
