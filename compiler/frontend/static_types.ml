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
  | S_static
  | S_dynamic

type ty =
  | Sy_scal of ty_scal
  | Sy_prod of ty list

type ty_sig = { input : ty; output : ty; }

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

let print_sig fmt csig =
  Format.fprintf fmt "@[%a -> %a@]"
    print_static_ty csig.input
    print_static_ty csig.output

let join ts1 ts2 =
  match ts1, ts2 with
  | S_static, _ | _, S_static -> S_static
  | S_dynamic, _ -> S_dynamic

module PreTy =
struct
  type 'a pre_ty =
    | Psy_var of 'a
    | Psy_scal of ty_scal ref
    | Psy_prod of 'a pre_ty list

  let rec print print_var fmt pty =
    match pty with
    | Psy_var v -> print_var fmt v
    | Psy_scal ss -> print_static_ty_scal fmt (! ss)
    | Psy_prod pty_l ->
      Format.fprintf fmt "(@[%a@])"
        (Utils.print_list_r (print print_var) " *") pty_l
end
module VarTy = Ast_misc.MakeVar(PreTy)

let rec ty_of_pre_ty pty =
  let open PreTy in
  match pty with
  | Psy_var v ->
    (* type variables default to dynamic since its more modular *)
    VarTy.ty_of_ty_var ty_of_pre_ty (fun _ -> Sy_scal S_dynamic) v
  | Psy_scal ss -> Sy_scal (! ss)
  | Psy_prod pty_l -> Sy_prod (List.map ty_of_pre_ty pty_l)

let rec is_static st =
  match st with
  | Sy_scal S_static -> true
  | Sy_scal S_dynamic -> true
  | Sy_prod st_l -> List.exists is_static st_l

let is_static_signature ssig = is_static ssig.input || is_static ssig.output
