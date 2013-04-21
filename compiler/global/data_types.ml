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

type data_ty_scal =
  | Tys_bool
  | Tys_int
  | Tys_float

type data_ty =
  | Ty_var of int
  | Ty_scal of data_ty_scal
  | Ty_prod of data_ty list

type data_sig =
    {
      data_sig_input : data_ty;
      data_sig_output : data_ty;
    }

let print_data_ty_scal fmt tys =
  match tys with
  | Tys_bool -> Format.fprintf fmt "bool"
  | Tys_int -> Format.fprintf fmt "int"
  | Tys_float -> Format.fprintf fmt "float"

let rec print_ty fmt ty =
  match ty with
  | Ty_var id -> Format.fprintf fmt "'x%d" id
  | Ty_scal tys -> print_data_ty_scal fmt tys
  | Ty_prod ty_l ->
    Format.fprintf fmt "(@[%a@])"
      (Utils.print_list_r print_ty " *") ty_l

let print_data_sig fmt tys =
  Format.fprintf fmt "@[%a -> %a@]"
    print_ty tys.data_sig_input
    print_ty tys.data_sig_output

module PreTy =
  struct
    type 'a pre_ty =
      | Pty_var of 'a
      | Pty_scal of data_ty_scal
      | Pty_prod of 'a pre_ty list

    let rec print print_var fmt pty =
      match pty with
      | Pty_var v -> print_var fmt v
      | Pty_scal tys -> print_data_ty_scal fmt tys
      | Pty_prod pty_l ->
        Format.fprintf fmt "(@[%a@])"
          (Utils.print_list_r (print print_var) " *") pty_l
  end
module VarTy = Ast_misc.MakeVar(PreTy)

let rec ty_of_pre_ty pty =
  let open PreTy in
  match pty with
  | Pty_var v -> VarTy.ty_of_ty_var ty_of_pre_ty (fun i -> Ty_var i) v
  | Pty_scal tys -> Ty_scal tys
  | Pty_prod ty_l -> Ty_prod (List.map ty_of_pre_ty ty_l)