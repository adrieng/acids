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

let rec print_power_tree_int print_a fmt tr =
  match tr with
  | Leaf a -> print_a fmt a
  | Concat tr_l ->
    Utils.print_list_r (print_power_tree_int print_a) "" fmt tr_l
  | Power (tr, pw) ->
    if pw = Int.one
    then print_power_tree_int print_a fmt tr
    else
      Format.fprintf fmt "%a^%a"
        (print_power_tree_int print_a) tr
        Int.print pw

type ('a, 'b) t = { u : ('a, 'b) power_tree; v : ('a, 'b) power_tree; }

let print_upword print_a print_b fmt { u = u; v = v; } =
  Format.fprintf fmt "%a(%a)"
    (print_power_tree print_a print_b) u
    (print_power_tree print_a print_b) v

let print_upword_int print_a fmt { u = u; v = v; } =
  Format.fprintf fmt "%a(%a)"
    (print_power_tree_int print_a) u
    (print_power_tree_int print_a) v

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

let flatten_power_tree_no_power pt =
  fold_power_tree (fun x l -> x :: l) (fun _ l -> l) pt []

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

let flatten_upword_no_power { u = u; v = v; } =
  flatten_power_tree_no_power u @ flatten_power_tree_no_power v
