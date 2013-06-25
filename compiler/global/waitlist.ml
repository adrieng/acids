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

open Utils

type id = int

type 'a t =
  {
    mutable var_to_class : int Union_find.point Int_map.t;
    mutable class_constr : 'a bin_tree Utils.Int_map.t;
  }

let create () =
  {
    var_to_class = Int_map.empty;
    class_constr = Int_map.empty;
  }

let print print_constr fmt waitlist =
  Format.fprintf fmt "@[var->class mapping: @[%a@]@\n"
    (Int_map.print print_int (fun fmt p -> print_int fmt (Union_find.find p)))
    waitlist.var_to_class;
  Format.fprintf fmt "class->constr mapping: @[%a@]@]"
    (Int_map.print print_int (print_bin_tree print_constr)) waitlist.class_constr

let find_class waitlist id =
  try Utils.Int_map.find id waitlist.var_to_class
  with Not_found ->
    let cl = Union_find.fresh id in
    waitlist.var_to_class <- Utils.Int_map.add id cl waitlist.var_to_class;
    cl

let find_items waitlist class_id =
  try Some (Utils.Int_map.find class_id waitlist.class_constr)
  with Not_found -> None

let add_item waitlist id c =
  let class_id = Union_find.find (find_class waitlist id) in
  let new_class =
    match find_items waitlist class_id with
    | Some cl -> Node (Leaf c, cl)
    | None -> Leaf c
  in
  waitlist.class_constr <- Int_map.add class_id new_class waitlist.class_constr

let remove waitlist id =
  waitlist.class_constr <- Int_map.remove id waitlist.class_constr

let merge_items waitlist id1 id2 =
  (* remap the class of id2 to the class of id1 *)
  let cl1 = find_class waitlist id1 in
  let cl2 = find_class waitlist id2 in
  let class_id1 = Union_find.find cl1 in
  let class_id2 = Union_find.find cl2 in
  if class_id1 <> class_id2 then Union_find.union cl1 cl2;
  match
    match find_items waitlist class_id1, find_items waitlist class_id2 with
    | None, None -> None
    | Some cl, None ->
      remove waitlist class_id1;
      Some cl
    | None, Some cl ->
      remove waitlist class_id2;
      Some cl
    | Some cl1, Some cl2 ->
      remove waitlist class_id1;
      remove waitlist class_id2;
      Some (Node (cl1, cl2))
  with
  | None -> ()
  | Some cl ->
    waitlist.class_constr <- Int_map.add (Union_find.find cl1) cl waitlist.class_constr

let take_items waitlist id =
  let class_id = Union_find.find (find_class waitlist id) in
  match find_items waitlist class_id with
  | None -> []
  | Some cl ->
    waitlist.class_constr <- Int_map.remove class_id waitlist.class_constr;
    fold_bin_tree_df (fun acc x -> x :: acc) [] cl

let take_all waitlist =
  let take_and_remove i cl acc =
    remove waitlist i;
    fold_bin_tree_df (fun acc x -> x :: acc) acc cl
  in
  let res = Utils.Int_map.fold take_and_remove waitlist.class_constr [] in
  waitlist.var_to_class <- Utils.Int_map.empty;
  res
