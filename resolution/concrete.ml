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

open Problem

module M =
  Make
    (struct
      type const = Pword.pword list
      let print_const = Utils.print_list_r Pword.print_pword " on"
     end)

include M

let reduce_on_pp sys =
  let reduce_on_side side =
    { side with const = [Utils.fold_left_1 Pword.on side.const]; }
  in

  let reduce_on_constr constr =
    {
      constr with
        lhs = reduce_on_side constr.lhs;
        rhs = reduce_on_side constr.rhs;
    }
  in
  { body = List.map reduce_on_constr sys.body; }

let solve sys =
  let sys = reduce_on_pp sys in
  let sys = reduce_on_pp sys in
  Format.eprintf "@[Reduced pwords:@ %a@]@." print_system sys;
  let sys = lower_equality_constraints sys in
  Format.eprintf "@[Lowered equalities:@ %a@]@." print_system sys;
  exit 0
