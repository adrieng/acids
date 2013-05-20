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

type interval_ty_scal =
  | Is_top
  | Is_inter of Interval.t

type interval_ty =
  | It_scal of interval_ty_scal
  | It_prod of interval_ty list

type interval_sig =
  {
    interval_sig_input : interval_ty;
    interval_sig_output : interval_ty;
  }

let print_interval_ty_scal fmt is =
  match is with
  | Is_top -> Format.fprintf fmt "T"
  | Is_inter it -> Interval.print fmt it

let rec print_interval_ty fmt ity =
  match ity with
  | It_scal is -> print_interval_ty_scal fmt is
  | It_prod ity_l ->
    Format.fprintf fmt "(@[%a@])"
      (Utils.print_list_r print_interval_ty " *") ity_l

let print_sig fmt cs =
  Format.fprintf fmt "@[%a -> %a@]"
    print_interval_ty cs.interval_sig_input
    print_interval_ty cs.interval_sig_output
