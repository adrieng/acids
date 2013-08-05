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

type tuple =
  | Econstr of Ast_misc.econstr
  | Tuple of tuple list

let rec print_tuple fmt tp =
  match tp with
  | Econstr ec -> Ast_misc.print_econstr fmt ec
  | Tuple tp_l ->
    Format.fprintf fmt "(@[%a@])"
      (Utils.print_list_r print_tuple ",") tp_l

type pragma =
  {
    loc : Loc.t;
    key : string;
    value : tuple;
  }

let print_pragma fmt pragma =
  Format.fprintf fmt "@@%s %a"
    pragma.key
    print_tuple pragma.value

type t = pragma list

let env_of_pragma_list pragma_l =
  let add env p = Utils.Env.add p.key p env in
  List.fold_left add Utils.Env.empty pragma_l
