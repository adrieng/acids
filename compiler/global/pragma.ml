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

(* {2 Errors} *)

type error =
  | Unknown_pragma of Loc.t * string
  | Ill_typed of Loc.t * string * string (* loc * key * type *)

exception Pragma_error of error

let print_error fmt err =
  match err with
  | Unknown_pragma (l, s) ->
    Format.fprintf fmt "%aUnknown pragma %s"
      Loc.print l
      s
  | Ill_typed (l, k, ty) ->
    Format.fprintf fmt "%aValue for %s should have type %s"
      Loc.print l
      k
      ty

let unknown_pragma loc k = raise (Pragma_error (Unknown_pragma (loc, k)))

let ill_typed loc k ty = raise (Pragma_error (Ill_typed (loc, k, ty)))

(* {2 Type definitions} *)

type solving_level =
  | Solve_node
  | Solve_main

type pragma =
  {
    loc : Loc.t;
    kind :
      [
        `Solve of solving_level
      ];
  }

type t = pragma list

(* {2 Utilities} *)

let value_for_solve loc k v =
  match v with
  | "node" -> `Solve Solve_node
  | "main" -> `Solve Solve_main
  | _ -> ill_typed loc k "[node | main]"

let pragma_table =
  [
    "solve", value_for_solve;
  ]

let make_command (k, v) loc =
  {
    loc = loc;
    kind =
      try
        let f = List.assoc k pragma_table in
        f loc k v
      with Not_found -> unknown_pragma loc k
  }
