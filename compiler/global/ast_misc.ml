(* Copyright (C) Adrien Guatto <adrien.guatto@laposte.net> 2013-2014
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

type rank = Int.t

type constr = Names.longname

let print_constr fmt c = Names.print_longname fmt c

(** Extended constructors *)
type econstr =
  | Ec_bool of bool
  | Ec_int of Int.t
  | Ec_constr of constr * rank

let print_econstr fmt ec =
  match ec with
  | Ec_bool b -> Format.fprintf fmt "%b" b
  | Ec_int i -> Int.print fmt i
  | Ec_constr (cstr, _) -> print_constr fmt cstr

let econstr_compare ec1 ec2 =
  let tag_to_int ec =
    match ec with
    | Ec_bool _ -> 0
    | Ec_int _ -> 1
    | Ec_constr _ -> 2
  in
  match ec1, ec2 with
  | Ec_bool b1, Ec_bool b2 ->
    Utils.bool_compare b1 b2
  | Ec_int i1, Ec_int i2 ->
    Utils.int_compare i1 i2
  | Ec_constr (ln1, _), Ec_constr (ln2, _) ->
    Names.longname_compare ln1 ln2
  | (Ec_bool _ | Ec_int _ | Ec_constr _), _ ->
    Utils.int_compare (tag_to_int ec1) (tag_to_int ec2)

let get_int ec =
  match ec with
  | Ec_int i -> i
  | Ec_bool _ | Ec_constr _ -> invalid_arg "get_int: not an int"

let get_bool ec =
  match ec with
  | Ec_bool b -> b
  | Ec_int _ | Ec_constr _ -> invalid_arg "get_bool: not a bool"

let get_constr ec =
  match ec with
  | Ec_constr (ec, _) -> ec
  | Ec_bool _ | Ec_int _ -> invalid_arg "get_econstr: not a constructor"

let int_of_econstr ec =
  match ec with
  | Ec_bool b -> Int.of_bool b
  | Ec_int i -> i
  | Ec_constr (_, rank) -> rank

type const_pword = (econstr, Int.t) Tree_word.t

let print_const_pword fmt pw =
  Tree_word.print_upword_int print_econstr fmt pw

type const =
  | Cconstr of econstr
  | Cfloat of float

let print_const fmt c =
  match c with
  | Cconstr c -> print_econstr fmt c
  | Cfloat f -> Format.fprintf fmt "%f" f

let get_econstr c =
  match c with
  | Cconstr ec -> ec
  | Cfloat _ -> invalid_arg "get_econstr: not a const"

let get_float c =
  match c with
  | Cfloat f -> f
  | Cconstr _ -> invalid_arg "get_float: not a float"

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
         val var_pref : string
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
    | None ->
      Format.fprintf fmt "'%s%a" S.var_pref Utils.print_int_non_zero v.v_id
    | Some ty ->
      S.print print_var fmt ty

  let print fmt t = S.print print_var fmt t

  let ty_of_ty_var ty_of_pre_ty ty_of_var_id tyv =
    match tyv.v_link with
    | Some pty -> ty_of_pre_ty pty
    | None -> ty_of_var_id tyv.v_id
end

let memoize_make_var make_var =
  let r = ref 0 in
  let ht = Hashtbl.create 10 in
  fun i ->
    let v_id =
      try Hashtbl.find ht i
      with Not_found ->
        let v_id = !r in
        incr r;
        Hashtbl.add ht i v_id;
        v_id
    in
    make_var v_id

(** Printing annotations *)

let print_annot r prefix p fmt x =
  if !Compiler_options.print_all_info || !r
  then Format.fprintf fmt "@ %s %a" prefix p x
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

(** Bounds of an integer word *)

let bounds_of_int_pword p =
  let l = ref (Int.of_int (- 1)) in
  let u = ref (Int.of_int (- 1)) in
  let check i =
    assert (!l >= Int.zero || !u < Int.zero);
    assert (i >= Int.zero);
    if !l < Int.zero
    then (l := i; u := i)
    else (l := Int.min !l i; u := Int.max !u i)
  in
  Tree_word.iter_upword check (fun _ -> ()) p;
  !l, !u
