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
    mutable num : int;
    mutable var_to_class : int Int_map.t;
    mutable class_constr : 'a bin_tree Utils.Int_map.t;
  }

let create () =
  {
    num = 0;
    var_to_class = Int_map.empty;
    class_constr = Int_map.empty;
  }

let print print_constr fmt deps =
  Format.fprintf "num: %d@\b" deps.num;
  Format.fprintf "var->class mapping:@[<hv 2>%a@]@\n"
    (Int_map.print print_int) deps.var_to_class;
  Format.fprintf fmt "class_constr:@[<hv 2>%a@]"
    (Int_map.print (print_btree print_int)) deps.class_constr

let find_class_id deps id =
  try Utils.Int_map.find v_id deps.var_to_class
  with Not_found ->
    let class_id = deps.num in
    deps.num <- deps.num + 1;
    deps.var_to_class <- Utils.Int_map.add v_id class_id deps.var_to_class;
    class_id

let find_class deps class_id =
  try Some (Utils.Int_map.find class_id deps.var_to_class)
  with Not_found -> None

let add_constraint deps id c =
  let class_id = find_class_id deps id in
  let new_class =
    match find_class deps class_id with
    | Some cl -> Node (Leaf c, cl)
    | None -> Leaf c
  in
  deps.class_constr <- Int_map.add class_id new_class class_constr

let fuse_constraints deps id1 id2 =
  (* remap the class of id2 to the class of id1 *)
  let class_id1 = find_class_id deps id1 in
  let class_id2 = find_class_id deps id2 in
  (
    match find_class class_id1, find_class class_id2 with
    | None, None -> ()
    | Some cl, None | None, Some cl ->
      deps.class_constr <- Int_map.add class_id1 cl deps.class_constr
    | Some cl1, Some cl2 ->
      deps.class_constr <- Int_map.remove class_id2 deps.class_constr;
      deps.class_constr <- Int_map.add class_id1 (Node (cl1, cl2)) deps.class_constr
  );
  deps.var_to_class <- Int_map.add id2 class_id1 deps.var_to_class

let take_constraints deps id =
  let class_id = find_class_id deps id in
  match find_class class_id1 with
  | None -> []
  | Some cl ->
    deps.class_constr <- Int_map.remove class_id deps.class_constr;
    fold_df (fun x acc -> x :: acc) [] cl
