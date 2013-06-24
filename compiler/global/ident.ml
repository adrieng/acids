(* Copyright (C) Adrien Guatto <adrien.guatto@laposte.net> 2012
 *
 * This file is part of nsched.
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

type kind = Source | Internal

type t =
  {
    num : int;
    name : string;
    name_num : int;
    kind : kind;
  }

type ctx =
  {
    mutable global_cpt : int;
    available_name_nums : (string, int ref) Hashtbl.t;
  }

let make_ctx () =
  {
    global_cpt = 0;
    available_name_nums = Hashtbl.create 1000;
  }

let _current_ctx = ref (make_ctx ())

let get_current_ctx () = !_current_ctx

let set_current_ctx ctx = _current_ctx := ctx

let reset_ctx () = set_current_ctx (make_ctx ())

let make_ident kind name =
  let available_name_num =
    try Hashtbl.find !_current_ctx.available_name_nums name
    with Not_found ->
      let r = ref 0 in
      Hashtbl.add !_current_ctx.available_name_nums name r;
      r
  in
  let id =
    {
      num = !_current_ctx.global_cpt;
      name = name;
      name_num = !available_name_num;
      kind = kind;
    }
  in
  !_current_ctx.global_cpt <- !_current_ctx.global_cpt + 1;
  incr available_name_num;
  id

let compare b1 b2 = b2.num - b1.num

let make_source = make_ident Source
let make_internal = make_ident Internal

let make_concat b s = make_internal (b.name ^ s)

let hash id = Hashtbl.hash id.num

let equal id1 id2 = 0 = compare id1 id2

type t_ = t
module Ident_ordered =
struct
  type t = t_
  let compare = compare
end

let to_string id =
  let print_short = id.kind = Source && id.name_num = 0 in
  if print_short then id.name else id.name ^ "_" ^ (string_of_int id.name_num)

let print fmt id = Format.fprintf fmt "%s" (to_string id)

module Set =
struct
  module M = Set.Make(Ident_ordered)

  include M

  let print fmt s =
    let l = M.fold (fun x l -> x :: l) s [] in
    Utils.print_list_r print "," fmt l
end

module Env =
struct
  module M = Map.Make(Ident_ordered)

  include M

  let of_assoc_list l =
    List.fold_left (fun env (id, x) -> M.add id x env) M.empty l

  let union env1 env2 = M.fold (fun k v env2 -> M.add k v env2) env1 env2

  let mapfold f env acc =
    let add k v (env, acc) =
      let (k, v), acc = f (k, v) acc in
      M.add k v env, acc
    in
    M.fold add env (M.empty, acc)

  let mapfold_elems f env acc =
    let add k v (env, acc) =
      let v, acc = f v acc in
      M.add k v env, acc
    in
    M.fold add env (M.empty, acc)

  let cardinal env = M.fold (fun _ _ n -> n + 1) env 0

  open Format

  let print print sep fmt env =
    let size = cardinal env in
    fprintf fmt "@[";
    ignore (M.fold
              (fun k v n ->
                if n < size
                then fprintf fmt "%a%s@ " print (k, v) sep
                else print fmt (k, v);
                n + 1)
              env
              1);
    fprintf fmt "@]"
end
