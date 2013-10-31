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

open Nir

(** Construction functions *)

let make_eq desc ck =
  {
    eq_desc = desc;
    eq_base_clock = ck;
    eq_loc = Loc.dummy;
  }

(** Iterators *)

(* Map *)

let rec map_eq_desc f proc =
  match proc with
  | Var (x, y) ->
    Var (f x, f y)
  | Const (x, cst) ->
    Const (f x, cst)
  | Call (x_l, app, y_l) ->
    Call (List.map f x_l, app, List.map f y_l)
  | Merge (x, ce, c_l) ->
    Merge (f x, ce, List.map (fun (ec, c) -> ec, f c) c_l)
  | Split (x_l, ce, y, ec_l) ->
    Split (List.map f x_l, ce, f y, ec_l)
  | Valof (x, ce) ->
    Valof (f x, ce)
  | Buffer (x, bu, y) ->
    Buffer (f x, bu, f y)
  | Delay (x, y) ->
    Delay (f x, f y)
  | Block block ->
    Block (map_block f block)

and map_eq f eq = { eq with eq_desc = map_eq_desc f eq.eq_desc; }

and map_block f block =
  { block with b_body = List.map (map_eq f) block.b_body; }

(* Fold *)

let rec fold_eq_desc f proc acc =
  match proc with
  | Var (x, y) ->
    let acc = f y acc in
    let acc = f x acc in
    acc
  | Const (x, _) ->
    f x acc
  | Call (x_l, _, y_l) ->
    let acc = List.fold_right f y_l acc in
    let acc = List.fold_right f x_l acc in
    acc
  | Merge (x, _, c_l) ->
    let f_clause (_, c) acc = f c acc in
    let acc = List.fold_right f_clause c_l acc in
    f x acc
  | Split (x_l, _, y, _) ->
    let acc = f y acc in
    List.fold_right f x_l acc
  | Valof (x, _) ->
    f x acc
  | Buffer (x, _, y) | Delay (x, y) ->
    f x (f y acc)
  | Block block ->
    fold_block f block acc

and fold_eq f eq acc = fold_eq_desc f eq.eq_desc acc

and fold_block f block acc = List.fold_right (fold_eq f) block.b_body acc

(** Compute variale occurences *)

let vars_eq eq = fold_eq (fun v acc -> v :: acc) eq []

let vars_block block = fold_block (fun v acc -> v :: acc) block []

(** Compute block count *)

let rec block_count_eq count eq =
  match eq.eq_desc with
  | Var _ | Const _ | Call _ | Merge _ | Split _ | Valof _ | Buffer _ | Delay _
      ->
    count
  | Block block ->
    block_count_block count block

and block_count_block count block =
  List.fold_left block_count_eq (succ count) block.b_body
