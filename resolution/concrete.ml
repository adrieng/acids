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

type lvar =
  | Iof of var * Int.t
  | Size of var

type lexp = (Int.t * lvar) list

type lconstr =
  | Eq of lexp * Int.t
  | Le of lexp * Int.t
  | Ge of lexp * Int.t

type concrete_system =
  {
    (** Initial system description *)

    k : Int.t; (** number of c_n period unfolding in prefix *)
    k' : Int.t; (** number of c_n period unfolding in period *)
    max_burst : Int.t; (** maximal number of ones per unit of time *)
    constraints : (cside * cside) list; (** adaptability constraints to solve *)

    (** Intermediate info *)

    sampler_size_per_unknown : (Int.t * Int.t) Utils.Env.t;
    (** size of prefix/period for each sampler per unknown *)
    nbones_per_unknown : (Int.t * Int.t) Utils.Env.t;
    (** number of ones per unknown, choosen according to k and k' *)

    (** Linear system *)

    lsys : lconstr list;
  }

let print_side fmt ((c_x, p_x), (c_y, p_y)) =
  Format.fprintf fmt "@[%s@ on %a@ <: %s@ on %a@]"
    c_x
    Pword.print_pword p_x
    c_y
    Pword.print_pword p_y

let print_lvar fmt lv =
  match lv with
  | Iof (c, j) -> Format.fprintf fmt "I_{%s}(%a)" c Int.print j
  | Size c -> Format.fprintf fmt "|%s|" c

let print_lexp fmt le =
  let print_term fmt (i, lv) =
    Format.fprintf fmt "%s %a * %a"
      (if i < Int.zero then "-" else "+")
      Int.print (Int.abs i)
      print_lvar lv
  in
  Utils.print_list_r print_term "" fmt le

let print_lconstr fmt lc =
  match lc with
  | Eq (le, i) ->
    Format.fprintf fmt "@[%a@ = %a@]"
      print_lexp le
      Int.print i
  | Le (le, i) ->
    Format.fprintf fmt "@[%a@ <= %a@]"
      print_lexp le
      Int.print i
  | Ge (le, i) ->
    Format.fprintf fmt "@[%a@ >= %a@]"
      print_lexp le
      Int.print i

let print_lsys fmt lsys =
  Format.fprintf fmt "{ @[%a@] }"
    (Utils.print_list_eol print_lconstr) lsys

let print_concrete_system fmt cs =
  let print_size fmt (u_size, v_size) =
    Format.fprintf fmt "|p.u| = %a, |p.v| = %a"
      Int.print u_size
      Int.print v_size
  in

  let print_nbones fmt (u_nbones, v_nbones) =
    Format.fprintf fmt "|c.u|_1 = %a, |c.v|_1 = %a"
      Int.print u_nbones
      Int.print v_nbones
  in

  Format.fprintf fmt
    "@[{@[@ @[%a@]@ @]}@ with sampler sizes @[%a@]@ and nbones @[%a@]@]"
    (Utils.print_list_r print_side ",") cs.constraints
    (Utils.Env.print Utils.print_string print_size) cs.sampler_size_per_unknown
    (Utils.Env.print Utils.print_string print_nbones) cs.nbones_per_unknown

let find_nbones csys c = Utils.Env.find c csys.nbones_per_unknown

let get_linear_term lc =
  match lc with
  | Eq (term, _) | Le (term, _) | Ge (term, _) -> term

(* [make_concrete_system sys] takes a system [sys] and returns an equivalent concrete system. *)
let make_concrete_system
    ?(k = Int.zero) ?(k' = Int.one) ?(max_burst = Int.of_int 1)
    sys =
  assert (k >= Int.zero);
  assert (k' >= Int.one);
  assert (max_burst >= Int.one);

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
    k = k;
    k' = k';
    max_burst = max_burst;
    constraints = List.map extract sys.body;

    sampler_size_per_unknown = Utils.Env.empty;
    nbones_per_unknown = Utils.Env.empty;

    lsys = [];
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

let choose_nbones_unknowns csys =
  let add_nbones c (sampler_u_size, sampler_v_size) nbones =
    let open Int in
    let u_nbones = sampler_u_size + csys.k * sampler_v_size in
    let v_nbones = csys.k' * sampler_v_size in
    Utils.Env.add c (u_nbones, v_nbones) nbones
  in

  {
    csys with
      nbones_per_unknown =
      Utils.Env.fold add_nbones csys.sampler_size_per_unknown Utils.Env.empty;
  }

let build_synchronizability_constraints csys =
  let add_synchronizability_constraint lsys ((c_x, p_x), (c_y, p_y)) =
    let open Pword in
    Eq ([nbones p_y.v, Size c_x; Int.neg (nbones p_x.v), Size c_y], Int.zero)
    :: lsys
  in

  let lsys =
    List.fold_left add_synchronizability_constraint csys.lsys csys.constraints
  in

  { csys with lsys = lsys; }

let build_precedence_constraints csys =
  let add_precedence_constraints lsys ((c_x, p_x), (c_y, p_y)) =
    let open Int in
    let open Pword in

    let h =
      max
        (nbones p_x.u + csys.k * nbones p_x.v)
        (nbones p_y.u + csys.k * nbones p_y.v)
      + lcm (csys.k' * nbones p_x.v) (csys.k' * nbones p_y.v)
    in

    let rec build lsys j =
      if j > h then lsys
      else
        let cstr =
          Le ([one, Iof (c_x, Pword.iof p_x j);
               neg one, Iof (c_y, Pword.iof p_y j)],
              Int.zero)
        in
        build (cstr :: lsys) (Int.succ j)
    in
    build lsys Int.one
  in

  let lsys =
    List.fold_left add_precedence_constraints csys.lsys csys.constraints
  in
  { csys with lsys = lsys; }

let build_periodicity_constraints csys =
  let open Int in

  let add_precedence_for_iof lsys lv =
    match lv with
    | Size _ -> lsys
    | Iof (c, j') ->
      let nbones_c_u, nbones_c_v = find_nbones csys c in
      if j' <= nbones_c_u + nbones_c_v then lsys
      else
        let j'_v = j' - nbones_c_u in
        let j = mod_b1 j'_v nbones_c_v + nbones_c_u in
        let l = Int.div_b1 j'_v nbones_c_v in
        assert (j' = j + l * nbones_c_v);
        Eq ([one, Iof (c, j'); neg one, Iof (c, j)],
            l * nbones_c_v) :: lsys
  in

  let add_precedence_constraints lsys lc =
    let iof_l = List.map snd (get_linear_term lc) in
    List.fold_left add_precedence_for_iof lsys iof_l
  in

  let lsys =
    List.fold_left add_precedence_constraints csys.lsys csys.lsys
  in

  { csys with lsys = lsys; }

let build_sufficient_size_constraints csys =
  let open Int in

  let add_sufficient_size c (nbones_c_u, nbones_c_v) lsys =
    let t1 = one, Iof (c, nbones_c_u + nbones_c_v) in
    let t2 = neg one, Iof (c, nbones_c_u + one) in
    let t3 = neg one, Size c in
    Le ([t1; t2; t3], neg one) :: lsys
  in

  let lsys =
    Utils.Env.fold add_sufficient_size csys.nbones_per_unknown csys.lsys
  in

  { csys with lsys = lsys; }

let build_increasing_indexes_constraints csys =
  let open Int in

  let indexes =
    let gather_iof indexes lc =
      let add indexes (_, c) =
        match c with
        | Size _ -> indexes
        | Iof (c, j) ->
          let indexes_for_c =
            try Utils.Env.find c indexes
            with Not_found -> Int.Set.empty
          in
          let indexes_for_c = Int.Set.add j indexes_for_c in
          Utils.Env.add c indexes_for_c indexes
      in
      List.fold_left add indexes (get_linear_term lc)
    in
    List.fold_left gather_iof Utils.Env.empty csys.lsys
  in

  let add_increasing_indexes_constraints c indexes_for_c lsys =
    let j = Int.Set.min_elt indexes_for_c in
    let indexes_for_c = Int.Set.remove j indexes_for_c in
    let add_constraint j' (j, lsys) =
      assert (j' >= j);
      let t1 = one, Iof (c, j') in
      let t2 = neg one, Iof (c, j) in
      let c = max zero (j' - j + one - csys.max_burst) in
      j', Ge ([t1; t2], c) :: lsys
    in
    let _, lsys = Int.Set.fold add_constraint indexes_for_c (j, lsys) in
    lsys
  in

  let lsys =
    Utils.Env.fold add_increasing_indexes_constraints indexes csys.lsys
  in

  { csys with lsys = lsys; }

let solve sys =
  let csys = make_concrete_system sys in
  let csys = compute_sampler_sizes csys in
  let csys = choose_nbones_unknowns csys in
  Format.eprintf "Concrete system: %a@." print_concrete_system csys;
  let csys = build_synchronizability_constraints csys in
  let csys = build_precedence_constraints csys in
  let csys = build_periodicity_constraints csys in
  let csys = build_sufficient_size_constraints csys in
  let csys = build_increasing_indexes_constraints csys in
  Format.eprintf "Linear system:@ %a@."
    print_lsys csys.lsys;
  Utils.Env.empty
