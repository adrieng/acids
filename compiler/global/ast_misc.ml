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

include Tree_word

type 'a var_dec =
    {
      v_ident : Ident.t;
      v_info : 'a;
      v_loc : Loc.t;
    }

type constr = Names.longname

let print_constr fmt c = Names.print_longname fmt c

(** Extended constructors *)
type econstr =
  | Ec_bool of bool
  | Ec_int of Int.t
  | Ec_constr of constr

let print_econstr fmt ec =
  match ec with
  | Ec_bool b -> Format.fprintf fmt "%b" b
  | Ec_int i -> Int.print fmt i
  | Ec_constr cstr -> print_constr fmt cstr

let get_int ec =
  match ec with
  | Ec_int i -> i
  | Ec_bool _ | Ec_constr _ -> invalid_arg "get_int: not an int"

let get_econstr ec =
  match ec with
  | Ec_constr ec -> ec
  | Ec_bool _ | Ec_int _ -> invalid_arg "get_econstr: not a constructor"

type const =
  | Cconstr of econstr
  | Cfloat of float

let print_const fmt c =
  match c with
  | Cconstr c -> print_econstr fmt c
  | Cfloat f -> Format.fprintf fmt "%f" f

type spec =
  | Unspec
  | Word of (Int.t, Int.t) Tree_word.t
  | Interval of Interval.t

let print_spec fmt spec =
  match spec with
  | Unspec -> Format.fprintf fmt "unspec"
  | Word w -> Tree_word.print_upword_int Int.print fmt w
  | Interval it -> Interval.print fmt it

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
        mutable v_link : t option;
      }
  and t = ty_var S.pre_ty

  let rec print_var fmt v =
    match v.v_link with
    | None -> Format.fprintf fmt "v%d" v.v_id
    | Some ty ->
      Format.fprintf fmt "%a{v%d}"
        (S.print print_var) ty
        v.v_id

  let print fmt t = S.print print_var fmt t

  let ty_of_ty_var ty_of_pre_ty ty_of_var_id tyv =
    match tyv.v_link with
    | Some pty -> ty_of_pre_ty pty
    | None -> ty_of_var_id tyv.v_id
end

(** Printing annotations *)

let print_annot r prefix p fmt x =
  if !Compiler_options.print_full_info || !r
  then Format.fprintf fmt " %s %a" prefix p x
  else ()

(** Printing annotated specs *)

let printing_prefix = "in"

let print_interval_annot =
  print_annot
    Compiler_options.print_spec_info
    printing_prefix
    Interval.print

let print_spec_annot =
  print_annot
    Compiler_options.print_spec_info
    printing_prefix
    print_spec
