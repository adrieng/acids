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

type static_ty_scal =
  | S_static
  | S_dynamic

type static_ty =
  | Sy_scal of static_ty_scal
  | Sy_prod of static_ty list

type static_sig =
  {
    st_sig_input : static_ty;
    st_sig_output : static_ty;
  }

let print_static_ty_scal fmt ss =
  match ss with
  | S_static -> Format.fprintf fmt "s"
  | S_dynamic -> Format.fprintf fmt "d"

let rec print_static_ty fmt sty =
  match sty with
  | Sy_scal ss -> print_static_ty_scal fmt ss
  | Sy_prod sty_l ->
    Format.fprintf fmt "(@[%a@])"
      (Utils.print_list_r print_static_ty " *") sty_l

module PreTy =
struct
  type 'a pre_ty =
  | Psy_var of 'a
  | Psy_scal of static_ty_scal
  | Psy_prod of 'a pre_ty list

  let rec print print_var fmt sty =
    match sty with
    | Psy_var v -> print_var fmt v
    | Psy_scal ss -> print_static_ty_scal fmt ss
    | Psy_prod sty_l ->
      Format.fprintf fmt "(@[%a@])"
        (Utils.print_list_r (print print_var) " *") sty_l
end
module VarTy = Ast_misc.MakeVar(PreTy)

let rec ty_of_pre_ty pty =
  let open PreTy in
  let open VarTy in
  match pty with
  | Psy_var { v_link = Some pty } -> ty_of_pre_ty pty
  | Psy_var { v_link = None; } ->
    (* type variables default to dynamic since its more modular *)
    Sy_scal S_dynamic
  | Psy_scal ss -> Sy_scal ss
  | Psy_prod psy_l -> Sy_prod (List.map ty_of_pre_ty psy_l)

let is_static = (=) S_static

let is_static_signature ssig =
  List.exists is_static ssig.st_sig_input
  || List.exists is_static ssig.st_sig_output
