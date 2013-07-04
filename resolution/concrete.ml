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

type cside = var * Pword.pword

type concrete_system =
  {
    constraints : (cside * cside) list;
    sampler_size_per_unknown : (Int.t * Int.t) Utils.Env.t;
    nbones_per_unknown : Int.t Utils.Env.t;
  }

let print_concrete_system fmt cs =
  let print_side fmt ((c_x, p_x), (c_y, p_y)) =
    Format.fprintf fmt "@[%s@ on %a@ <: %s@ on %a@]"
      c_x
      Pword.print_pword p_x
      c_y
      Pword.print_pword p_y
  in

  let print_size fmt (u_size, v_size) =
    Format.fprintf fmt "|p.u| = %a, |p.v| = %a"
      Int.print u_size
      Int.print v_size
  in

  Format.fprintf fmt
    "@[@[{@ %a@ }@]@ with sampler sizes @[%a@] and nbones @[%a@]@]"
    (Utils.print_list_r print_side ",") cs.constraints
    (Utils.Env.print Utils.print_string print_size) cs.sampler_size_per_unknown
    (Utils.Env.print Utils.print_string Int.print) cs.nbones_per_unknown
;;

(* [presolve sys] takes a system [sys] and returns an equivalent concrete system. *)
let presolve sys =
  let reduce_on sys =
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
  in

  let check_rigid_constraints sys =
    let check_rigid_constr c sys =
      match c.lhs.var, c.rhs.var with
      | None, None ->
        let lhs = Utils.get_single c.lhs.const in
        let rhs = Utils.get_single c.rhs.const in
        let check_fun =
          match c.kind with
          | Equal -> Pword.equal
          | Adapt -> Pword.adapt
        in
        if not (check_fun lhs rhs)
        then Resolution_errors.constant_inconsistency ();
        sys
      | _ -> c :: sys
    in
    { body = List.fold_right check_rigid_constr sys.body []; }
  in

  let sys =
    lower_equality_constraints (check_rigid_constraints (reduce_on sys))
  in
  let extract c =
    assert (c.kind = Adapt);
    (Utils.get_opt c.lhs.var, Utils.get_single c.lhs.const),
    (Utils.get_opt c.rhs.var, Utils.get_single c.rhs.const)
  in
  {
    constraints = List.map extract sys.body;
    sampler_size_per_unknown = Utils.Env.empty;
    nbones_per_unknown = Utils.Env.empty;
  }

(** [compute_sampler_sizes csys] returns an equivalent concrete systems [csys']
    where all the samplers of a given unknown have the same prefix and period
    sizes. These lengths are stored in the [csys'.sampler_size_per_unknown]
    field. *)
let compute_sampler_sizes csys =
  let walk_side env (c, p) =
    let open Int in
    let open Pword in

    let size_u, size_v = try Utils.Env.find c env with Not_found -> zero, one in

    let size_u = max size_u (size p.u) in
    let size_v = lcm size_v (size p.v) in

    Utils.Env.add c (size_u, size_v) env
  in

  let walk_constr env (s1, s2) = walk_side (walk_side env s1) s2 in

  let sampler_size_per_unknown =
    List.fold_left walk_constr Utils.Env.empty csys.constraints
  in

  let adjust_size (c, p) =
    let open Pword in

    let max_u, max_v = Utils.Env.find c sampler_size_per_unknown in

    let p = Pword.lengthen_prefix p Int.(max_u - size p.u) in
    let p = Pword.repeat_period p Int.(max_v / size p.v) in
    c, p
  in

  let adjust_constr (s1, s2) = adjust_size s1, adjust_size s2 in

  {
    csys with
      constraints = List.map adjust_constr csys.constraints;
      sampler_size_per_unknown = sampler_size_per_unknown;
  }

let solve sys =
  let csys = presolve sys in
  let csys = compute_sampler_sizes csys in
  Format.eprintf "Concrete system: %a@." print_concrete_system csys;
  Utils.Env.empty
