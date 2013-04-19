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

type 'a var_dec =
    {
      v_ident : Ident.t;
      v_info : 'a;
      v_loc : Loc.t;
    }


type const =
  | Cbool of bool
  | Cint of Int.t
  | Cfloat of float
  | Cword of int list (* [0-9] ints *)

type ('a, 'b) power_tree =
  | Leaf of 'a
  | Concat of ('a, 'b) power_tree list
  | Power of ('a, 'b) power_tree * 'b

(** Generic module for unification variables *)
module MakeVar =
  functor
    (S :
       sig
         type 'a pre_ty
         val print :
           (Format.formatter -> 'a -> unit) ->
           Format.formatter ->
           'a pre_ty ->
           unit
       end) ->
struct
  type ty_var =
      {
        v_id : int;
        mutable v_link : ty_var S.pre_ty option;
      }

  include S

  let rec print_var fmt v =
    Format.fprintf fmt "%a%d"
      (Utils.print_opt (S.print print_var)) v.v_link
      v.v_id

  let ty_of_ty_var ty_of_pre_ty ty_of_var_id tyv =
    match tyv.v_link with
    | Some pty -> ty_of_pre_ty pty
    | None -> ty_of_var_id tyv.v_id
end

let print_const fmt c =
  match c with
  | Cbool b -> Format.fprintf fmt "%b" b
  | Cint i -> Format.fprintf fmt "%nd" i
  | Cfloat f -> Format.fprintf fmt "%f" f
  | Cword w ->
    let print_int fmt i = Format.fprintf fmt "%d" i in
    Format.fprintf fmt "@%a@" (Utils.print_list print_int) w

let rec print_power_tree print_a print_b fmt tr =
  match tr with
  | Leaf a -> print_a fmt a
  | Concat tr_l ->
    Utils.print_list_r (print_power_tree print_a print_b) "" fmt tr_l
  | Power (tr, pw) ->
    Format.fprintf fmt "%a^%a"
      (print_power_tree print_a print_b) tr
      print_b pw
