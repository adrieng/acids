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

type const =
  | Cconstr of econstr
  | Cfloat of float
  | Cword of Int.t list (* [0-9] ints *)

let print_const fmt c =
  match c with
  | Cconstr c -> print_econstr fmt c
  | Cfloat f -> Format.fprintf fmt "%f" f
  | Cword w ->
    Format.fprintf fmt "'%a'" (Utils.print_list Int.print) w

type ('a, 'b) power_tree =
  | Leaf of 'a
  | Concat of ('a, 'b) power_tree list
  | Power of ('a, 'b) power_tree * 'b

let rec print_power_tree print_a print_b fmt tr =
  match tr with
  | Leaf a -> print_a fmt a
  | Concat tr_l ->
    Utils.print_list_r (print_power_tree print_a print_b) "" fmt tr_l
  | Power (tr, pw) ->
    Format.fprintf fmt "%a^%a"
      (print_power_tree print_a print_b) tr
      print_b pw

type ('a, 'b) upword = { u : ('a, 'b) power_tree; v : ('a, 'b) power_tree; }

let print_upword print_a print_b fmt { u = u; v = v; } =
  Format.fprintf fmt "%a(%a)"
    (print_power_tree print_a print_b) u
    (print_power_tree print_a print_b) v

let rec mapfold_power_tree f g pt acc =
  match pt with
  | Leaf x ->
    let x, acc = f x acc in
    Leaf x, acc
  | Concat pt_l ->
    let pt_l, acc = Utils.mapfold (mapfold_power_tree f g) pt_l acc in
    Concat pt_l, acc
  | Power (pt, pw) ->
    let pw, acc = g pw acc in
    let pt, acc = mapfold_power_tree f g pt acc in
    Power (pt, pw), acc

let rec fold_power_tree f g pt acc =
  match pt with
  | Leaf x -> f x acc
  | Concat pt_l -> List.fold_right (fold_power_tree f g) pt_l acc
  | Power (pt, pw) -> fold_power_tree f g pt (g pw acc)

let rec iter_power_tree f g pt =
  match pt with
  | Leaf x -> f x
  | Concat pt_l -> List.iter (iter_power_tree f g) pt_l
  | Power (pt, pw) -> g pw; iter_power_tree f g pt

let rec map_power_tree f g pt =
  match pt with
  | Leaf x -> Leaf (f x)
  | Concat pt_l -> Concat (List.map (map_power_tree f g) pt_l)
  | Power (pt, pw) -> Power (map_power_tree f g pt, g pw)

let mapfold_upword f g { u = u; v = v; } acc =
  let u, acc = mapfold_power_tree f g u acc in
  let v, acc = mapfold_power_tree f g v acc in
  { u = u; v = v; }, acc

let iter_upword f g { u = u; v = v; } =
  iter_power_tree f g u;
  iter_power_tree f g v

let fold_upword f g { u = u; v = v; } acc =
  fold_power_tree f g v (fold_power_tree f g u acc)

let map_upword f g { u = u; v = v; } =
  { u = map_power_tree f g u; v = map_power_tree f g v; }

let is_constant_pword { u = u; v = v; } =
  match u, v with
  | Concat [], (Leaf _ | Power (Leaf _, _)) -> true
  | _ -> false

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
