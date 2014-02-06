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

type word = (Int.t, Int.t) Tree_word.t

module S =
struct
  type const = word list
  let print_const ~has_var fmt p_l =
    if has_var && List.length p_l >= 1 then Format.fprintf fmt "on ";
    Utils.print_list_r
      (Tree_word.print_upword_int Int.print)
      " on"
      fmt
      p_l

  let unit_const w_l = w_l = []

  let right_simplify _ = false

  let equivalent_const _ _ = false
end

module P = Problem.Make(S)

include S
include P

module Solution =
struct
  type t = word Utils.Env.t
  let get (m : t) x = try Some (Utils.Env.find x m) with Not_found -> None
  let fold = Utils.Env.fold
end

let translate_to_pwords problem =
  let translate_to_pword_side s =
    {
      Concrete.var = s.var;
      Concrete.const =
        List.map Resolution_utils.pword_of_tree s.const;
    }
  in

  let translate_to_pword_constr c =
    {
      Concrete.loc = c.loc;
      Concrete.lhs = translate_to_pword_side c.lhs;
      Concrete.kind = c.kind;
      Concrete.rhs = translate_to_pword_side c.rhs;
    }
  in

  {
    Concrete.body = List.map translate_to_pword_constr problem.body;
    Concrete.options = problem.options;
  }

let check_solution sys sol =
  let open Concrete in

  let simplify_side side =
    let l =
      match side.var with
      | None -> side.const
      | Some c ->
        Resolution_utils.pword_of_tree (Utils.Env.find c sol) :: side.const
    in
    Utils.fold_left_1 Pword.on l
  in

  let check_constraint constr =
    let lhs = simplify_side constr.lhs in
    let rhs = simplify_side constr.rhs in
    let check_fun =
      match constr.kind with
      | Problem.Equal -> Pword.equal
      | Problem.Adapt -> Pword.adapt ~delay:Int.zero
    in
    if not (check_fun lhs rhs)
    then Resolution_errors.internal_error sol
  in

  List.iter check_constraint sys.body

let solve sys =
  if sys.body = [] then Utils.Env.empty
  else
    let sys = translate_to_pwords sys in
    let sol = Concrete.solve sys in
    if Resolution_options.find_bool ~default:false sys.Concrete.options "check"
    then check_solution sys sol;
    sol
