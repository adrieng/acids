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

type word = (Int.t, Int.t) Tree_word.t

module S =
struct
  type const = word list
  let print_const fmt w_l =
    Utils.print_list_r
      (Tree_word.print_upword Int.print Int.print)
      " on"
      fmt
      w_l
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

let rec translate_to_word_tree pt =
  match pt with
  | Tree_word.Leaf i -> Pword.singleton i
  | Tree_word.Concat pt_l ->
    let w_l = List.map translate_to_word_tree pt_l in
    List.fold_right Pword.concat w_l Pword.empty
  | Tree_word.Power (pt, i) -> Pword.power (translate_to_word_tree pt) i

let translate_to_pword_tree { Tree_word.u = u; Tree_word.v = v; } =
  Pword.make (translate_to_word_tree u) (translate_to_word_tree v)

let translate_to_pwords problem =
  let translate_to_pword_side s =
    {
      Concrete.var = s.var;
      Concrete.const = List.map translate_to_pword_tree s.const;
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
        translate_to_pword_tree (Utils.Env.find c sol) :: side.const
    in
    Utils.fold_left_1 Pword.on l
  in

  let check_constraint constr =
    let lhs = simplify_side constr.lhs in
    let rhs = simplify_side constr.rhs in
    let check_fun =
      match constr.kind with
      | Problem.Equal -> Pword.equal
      | Problem.Adapt -> Pword.adapt
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
