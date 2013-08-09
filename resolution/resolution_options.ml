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

type value =
  | Bool of bool
  | Int of Int.t

let print_value fmt value =
  match value with
  | Bool b -> Format.fprintf fmt "%b" b
  | Int i -> Int.print fmt i

type t = string * value

let print fmt (s, value) =
  Format.fprintf fmt "@[%s =@ %a@]"
    s
    print_value value

let make s value = s, value

type env = value Utils.Env.t

let print_env fmt env =
  Utils.Env.print ~sep:"," Utils.print_string print_value fmt env

let empty = Utils.Env.empty

let is_empty env = Utils.Env.cardinal env = 0

let add env (s, opt) = Utils.Env.add s opt env

let find env s = Utils.Env.find s env

type option_name = string
type expected_type = string
type actual_type = string

exception Option_error of option_name * expected_type * actual_type

let option_error name exp_ty act_ty =
  raise (Option_error (name, exp_ty, act_ty))

let find_bool ~default env s =
  try
    match find env s with
    | Bool b -> b
    | Int _ -> option_error s "bool" "int"
  with Not_found ->
    default

let find_int ~default env s =
  try
    match find env s with
    | Bool _ -> option_error s "int" "bool"
    | Int i -> i
  with Not_found ->
    default
