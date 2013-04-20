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

type modname = string

type shortname = string

type modul =
  | LocalModule
  | Module of modname

type longname =
  {
    modn : modul;
    shortn : shortname;
  }

let make_longname modn shortn = { modn = modn; shortn = shortn; }

let print_modname fmt m = Format.fprintf fmt "%s" m

let print_shortname fmt s = Format.fprintf fmt "%s" s

let print_longname fmt ln =
  match ln.modn with
  | LocalModule -> print_shortname fmt ln.shortn
  | Module modn ->
    Format.fprintf fmt "%a.%a"
      print_modname modn
      print_shortname ln.shortn

let print_longname_short fmt ln = print_shortname fmt ln.shortn

let longname_compare (ln1 : longname) (ln2 : longname) =
  Pervasives.compare ln1 ln2

module LongnameOrdered =
struct
  type t = longname
  let compare = longname_compare
end

module Env =
  struct
    module M = Map.Make(LongnameOrdered)
    include M

    let union env1 env2 = M.fold (fun k v env2 -> M.add k v env2) env1 env2

    let disjoint_union env1 env2 =
      let add k v env =
        if M.mem k env then invalid_arg "disjoint_union" else M.add k v env
      in
      M.fold add env1 env2

    let mapfold_elems f env acc =
      let add k v (env, acc) =
        let v, acc = f v acc in
        M.add k v env, acc
      in
      M.fold add env (M.empty, acc)

    let of_assoc_list l =
      List.fold_left (fun env (id, x) -> M.add id x env) M.empty l
  end

module ShortEnv = Utils.String_map
