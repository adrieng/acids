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

type clock_exp =
  | Ce_var of Ident.t
  | Ce_pword of (Int.t, Int.t) Ast_misc.upword
  | Ce_equal of clock_exp * Int.t
  | Ce_iter of clock_exp

type stream_type =
  | St_var of int
  | St_on of stream_type * clock_exp

type clock_type =
  | Ct_var of int
  | Ct_stream of stream_type
  | Ct_prod of clock_type list

type clock_sig =
    {
      ct_sig_input : clock_type;
      ct_sig_output : clock_type;
    }

let rec print_clock_exp fmt ce =
  match ce with
  | Ce_var id -> Ident.print fmt id
  | Ce_pword pw ->
    Ast_misc.print_upword Int.print Int.print fmt pw
  | Ce_equal (ce, i) ->
    Format.fprintf fmt "%a = %a"
      print_clock_exp ce
      Int.print i
  | Ce_iter ce ->
    Format.fprintf fmt "iter %a" print_clock_exp ce

let rec print_stream_type fmt st =
  match st with
  | St_var i -> Format.fprintf fmt "'a%d" i
  | St_on (st, ce) ->
    Format.fprintf fmt "@[%a@ on %a@]"
      print_stream_type st
      print_clock_exp ce

let rec print_clock_type fmt ct =
  match ct with
  | Ct_var i -> Format.fprintf fmt "'b%d" i
  | Ct_stream st -> print_stream_type fmt st
  | Ct_prod st_l ->
    Format.fprintf fmt "(@[%a@])"
      (Utils.print_list_r print_clock_type " *") st_l

let print_sig fmt cs =
  Format.fprintf fmt "%a -> %a"
    print_clock_type cs.ct_sig_input
    print_clock_type cs.ct_sig_output

let printing_prefix = "::"

module PreTySt =
struct
  type 'a pre_ty =
    | Pst_var of 'a
    | Pst_on of 'a pre_ty * clock_exp

  let rec print print_var fmt pty =
    match pty with
    | Pst_var v -> print_var fmt v
    | Pst_on (pty, ce) ->
      Format.fprintf fmt "@[%a@ on %a@]"
        (print print_var) pty
        print_clock_exp ce
end
module VarTySt = Ast_misc.MakeVar(PreTySt)

let rec st_of_pre_st pst =
  let open PreTySt in
  match pst with
  | Pst_var v -> VarTySt.ty_of_ty_var st_of_pre_st (fun i -> St_var i) v
  | Pst_on (st, ce) -> St_on (st_of_pre_st st, ce)

module PreTy =
struct
  type 'a pre_ty =
    | Pct_var of 'a
    | Pct_stream of VarTySt.ty_var PreTySt.pre_ty
    | Pct_prod of 'a pre_ty list

  let rec print print_var fmt pty =
    match pty with
    | Pct_var v -> print_var fmt v
    | Pct_stream pst -> PreTySt.print VarTySt.print_var fmt pst
    | Pct_prod pty_l ->
      Format.fprintf fmt "(@[%a@])"
        (Utils.print_list_r (print print_var) " *") pty_l

end
module VarTy = Ast_misc.MakeVar(PreTy)

let rec ty_of_pre_ty pty =
  let open PreTy in
  match pty with
  | Pct_var v -> VarTy.ty_of_ty_var ty_of_pre_ty (fun i -> Ct_var i) v
  | Pct_stream pst -> Ct_stream (st_of_pre_st pst)
  | Pct_prod pty_l -> Ct_prod (List.map ty_of_pre_ty pty_l)
