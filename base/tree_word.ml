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

type ('a, 'b) power_tree =
  | Leaf of 'a
  | Concat of ('a, 'b) power_tree list
  | Power of ('a, 'b) power_tree * 'b

let rec print_power_tree print_a print_b fmt tr =
  match tr with
  | Leaf a -> print_a fmt a
  | Concat tr_l ->
    Utils.print_list_r (print_power_tree print_a print_b) "" fmt tr_l
  | Power (Concat _ as tr, pw) ->
    Format.fprintf fmt "[%a]^%a"
      (print_power_tree print_a print_b) tr
      print_b pw
  | Power (tr, pw) ->
    Format.fprintf fmt "%a^%a"
      (print_power_tree print_a print_b) tr
      print_b pw

let rec print_power_tree_int print_a fmt tr =
  match tr with
  | Leaf a -> print_a fmt a
  | Concat tr_l ->
    Utils.print_list_r (print_power_tree_int print_a) "" fmt tr_l
  | Power (tr, pw) when pw = Int.one ->
    print_power_tree_int print_a fmt tr
  | Power (Concat _ as tr, pw) ->
    Format.fprintf fmt "[%a]^%a"
      (print_power_tree_int print_a) tr
      Int.print pw
  | Power (tr, pw) ->
    Format.fprintf fmt "%a^%a"
      (print_power_tree_int print_a) tr
      Int.print pw

type ('a, 'b) t = { u : ('a, 'b) power_tree; v : ('a, 'b) power_tree; }

let print_upword print_a print_b fmt { u = u; v = v; } =
  Format.fprintf fmt "@[%a(@[%a@])@]"
    (print_power_tree print_a print_b) u
    (print_power_tree print_a print_b) v

let print_upword_int print_a fmt { u = u; v = v; } =
  Format.fprintf fmt "@[%a(@[%a@])@]"
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

let flatten_power_tree_no_power pt =
  fold_power_tree (fun x l -> x :: l) (fun _ l -> l) pt []

let flatten_upword_no_power { u = u; v = v; } =
  flatten_power_tree_no_power u @ flatten_power_tree_no_power v

let flatten_word_int pt =
  let rec walk acc k pt =
    match pt with
    | Leaf x -> k (x :: acc)
    | Power (pt, n) ->
      if n = Int.zero
      then k acc
      else walk acc (fun acc -> walk acc k (Power (pt, Int.pred n))) pt
    | Concat [] ->
      k acc
    | Concat (pt :: pt_l) ->
      walk acc (fun acc -> walk acc k (Concat pt_l)) pt
  in
  walk [] (fun acc -> List.rev acc) pt

let pair_list_of_word_int acc pt =
  let rec walk n acc pt =
    match pt with
    | Leaf x -> (x, n) :: acc
    | Power (pt, m) -> walk Int.(n * m) acc pt
    | Concat pt_l -> List.fold_left (walk n) acc pt_l
  in
  walk Int.one acc pt

let pair_list_of_pword_int pw =
  let acc_u = pair_list_of_word_int [] pw.u in
  let acc = pair_list_of_word_int acc_u pw.v in
  Int.of_int (List.length acc_u), List.rev acc

let rec size_tree pt =
  match pt with
  | Leaf _ -> 1
  | Power (pt, _) -> 1 + size_tree pt
  | Concat pt_l -> List.fold_left (+) 0 (List.map size_tree pt_l)

let size_upword { u = u; v = v } = size_tree u, size_tree v

let get_first_leaf_period { v = v; } =
  let rec walk pt =
    match pt with
    | Leaf x -> x
    | Power (pt, _) -> walk pt
    | Concat [] -> invalid_arg "empty pword"
    | Concat (pt :: _) -> walk pt
  in
  walk v
