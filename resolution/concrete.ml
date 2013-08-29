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
      type const = Pword.pword list (* TODO some caching *)
      let print_const ~has_var fmt p_l =
        if has_var && List.length p_l >= 1 then Format.fprintf fmt "on ";
        Utils.print_list_r Pword.print_pword " on" fmt p_l
      let unit_const pw_l =
        let p = List.fold_left Pword.on Pword.unit_pword pw_l in
        Pword.is_unit_pword p
      let right_simplify pw_l =
        let p = List.fold_left Pword.on Pword.unit_pword pw_l in
        Pword.is_constant_pword p
      let equivalent_const pw_l1 pw_l2 =
        let p1 = List.fold_left Pword.on Pword.unit_pword pw_l1 in
        let p2 = List.fold_left Pword.on Pword.unit_pword pw_l2 in
        Pword.equal p1 p2
     end)

include M

type cside = var option * Pword.pword

type lvar =
  | Iof of var * Int.t
  | Size of var
  | Const of Int.t (* pseudo-variable for convenience *)

type lexp = (Int.t * lvar) list

type lconstr =
  | Eq of lexp * Int.t
  | Le of lexp * Int.t
  | Ge of lexp * Int.t

type concrete_system =
  {
    (** Initial system description *)

    global_k : Int.t; (** global number of c_n period unfolding in prefix *)
    global_k' : Int.t; (** global number of c_n period unfolding in period *)
    max_burst : Int.t; (** maximal number of ones per unit of time *)
    constraints : (cside * cside) list; (** adaptability constraints to solve *)

    (** Intermediate info *)

    sampler_size_per_unknown : (Int.t * Int.t) Utils.Env.t;
    (** size of prefix/period for each sampler per unknown *)
    balance_results : Int.t Utils.Env.t;
    (** solution of balance equations for each unknown *)
    unfolding_per_unknown : (Int.t * Int.t) Utils.Env.t;
    (** (k * k') unfolding factors, per unknown. Guaranteed to be greater than
        g_k (resp. g_k') *)
    nbones_per_unknown : (Int.t * Int.t) Utils.Env.t;
    (** number of ones per unknown, choosen according to k and k' *)

    (** Linear system *)
    synchronizability : lconstr list;
    precedence : lconstr list;
    periodicity : lconstr list;
    sufficient_size : lconstr list;
    split_prefix_period : lconstr list;
    increasing_indexes : lconstr list;
    max_burst_indexes : lconstr list;
    sufficient_indexes : lconstr list;
    objective : lexp;
  }

let print_var_option fmt co =
  match co with
  | None -> ()
  | Some c -> Format.fprintf fmt "%s@ on " c

let print_side fmt ((c_x, p_x), (c_y, p_y)) =
  Format.fprintf fmt "@[%a%a@ <: %a%a@]"
    print_var_option c_x
    Pword.print_pword p_x
    print_var_option c_y
    Pword.print_pword p_y

let print_lvar fmt lv =
  match lv with
  | Iof (c, j) -> Format.fprintf fmt "I_{%s}(%a)" c Int.print j
  | Size c -> Format.fprintf fmt "|%s|" c
  | Const i -> Int.print fmt i

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

let print_linear_system fmt lsys =
  Format.fprintf fmt "{ @[%a@] }"
    (Utils.print_list_eol print_lconstr) lsys

let print_linear_systems fmt csys =
  let p_header header fmt lsys =
    Format.fprintf fmt "@[<v 2>%s constraints:@ %a@]@\n"
      header
      print_linear_system lsys
  in
  Format.fprintf fmt "%a%a%a%a%a%a%a%a"
    (p_header "Synchronizability") csys.synchronizability
    (p_header "Precedence") csys.precedence
    (p_header "Periodicity") csys.periodicity
    (p_header "Sufficient size") csys.sufficient_size
    (p_header "Split prefix period") csys.split_prefix_period
    (p_header "Increasing indexes") csys.increasing_indexes
    (p_header "Max burst indexes") csys.max_burst_indexes
    (p_header "Sufficient indexes") csys.sufficient_indexes

let print_concrete_system fmt cs =
  let print_size fmt (u_size, v_size) =
    Format.fprintf fmt "(|p.u| = %a, |p.v| = %a)"
      Int.print u_size
      Int.print v_size
  in

  let print_nbones fmt (u_nbones, v_nbones) =
    Format.fprintf fmt "(|c.u|_1 = %a, |c.v|_1 = %a)"
      Int.print u_nbones
      Int.print v_nbones
  in

  Format.fprintf fmt
    "@[@[<hv 2>{ @[%a@] }@]@ with sampler sizes @[%a@]@ and balance @[%a@]@ and nbones @[%a@]@]"
    (Utils.print_list_r print_side ",") cs.constraints
    (Utils.Env.print Utils.print_string print_size) cs.sampler_size_per_unknown
    (Utils.Env.print Utils.print_string Int.print) cs.balance_results
    (Utils.Env.print Utils.print_string print_nbones) cs.nbones_per_unknown

(* >>> Comparison functions *)

let lvar_compare lv1 lv2 =
  let tag_to_int lv =
    match lv with
    | Iof _ -> 0
    | Size _ -> 1
    | Const _ -> 2
  in
  match lv1, lv2 with
  | Iof (v1, i1), Iof (v2, i2) ->
    Utils.compare_both
      (Utils.string_compare v1 v2)
      (fun () -> Int.compare i1 i2)

  | Size v1, Size v2 ->
    Utils.string_compare v1 v2

  | Const i1, Const i2 ->
    Int.compare i1 i2

  | (Iof _ | Size _ | Const _), _ ->
    Utils.int_compare (tag_to_int lv1) (tag_to_int lv2)

let lterm_compare (i1, lv1) (i2, lv2) =
  Utils.compare_both
    (Int.compare i1 i2)
    (fun () -> lvar_compare lv1 lv2)

let lexp_compare lexp1 lexp2 = Utils.list_compare lterm_compare lexp1 lexp2

let lconstr_compare lc1 lc2 =
  let tag_to_int lc =
    match lc with
    | Eq _ -> 0
    | Le _ -> 1
    | Ge _ -> 2
  in
  match lc1, lc2 with
  | Eq (le1, i1), Eq (le2, i2)
  | Le (le1, i1), Le (le2, i2)
  | Ge (le1, i1), Ge (le2, i2) ->
    Utils.compare_both
      (lexp_compare le1 le2)
      (fun () -> Int.compare i1 i2)
  | (Eq _ | Le _ | Ge _), _ ->
    Utils.int_compare (tag_to_int lc1) (tag_to_int lc2)

module ConstrSet =
  Set.Make
    (struct
        type t = lconstr
        let compare = lconstr_compare
     end)

module LvarSet =
  Set.Make
    (struct
        type t = lvar
        let compare = lvar_compare
     end)

(* <<< *)

let find_nbones csys c = Utils.Env.find c csys.nbones_per_unknown

let find_k csys c =
  try fst (Utils.Env.find c csys.unfolding_per_unknown)
  with Not_found -> csys.global_k

let find_k' csys c =
    try snd (Utils.Env.find c csys.unfolding_per_unknown)
    with Not_found -> csys.global_k'

let get_linear_term lc =
  match lc with
  | Eq (term, _) | Le (term, _) | Ge (term, _) -> term

let neg_term (i, l) = Int.neg i, l

let fold_left_over_linear_constraints f acc csys =
  let acc = List.fold_left f acc csys.synchronizability in
  let acc = List.fold_left f acc csys.precedence in
  let acc = List.fold_left f acc csys.periodicity in
  let acc = List.fold_left f acc csys.sufficient_size in
  let acc = List.fold_left f acc csys.split_prefix_period in
  let acc = List.fold_left f acc csys.increasing_indexes in
  let acc = List.fold_left f acc csys.max_burst_indexes in
  let acc = List.fold_left f acc csys.sufficient_indexes in
  acc

(* [make_concrete_system sys] takes a system [sys] and returns an equivalent
   concrete system. *)
let make_concrete_system
    ?(k = Int.zero) ?(k' = Int.one) ?(max_burst = Int.of_int 1)
    ?(complete = false)
    verbose
    sys =
  assert (k >= Int.zero);
  assert (k' >= Int.one);
  assert (max_burst >= Int.one);

  let reduce_on sys =
    let reduce_on_side side =
      let const =
        match side.const with
        | [] -> [Pword.unit_pword]
        | _ :: _ -> [Utils.fold_left_1 Pword.on side.const]
      in
      { side with const = const; }
    in

    let reduce_on_constr constr =
      {
        constr with
          lhs = reduce_on_side constr.lhs;
          rhs = reduce_on_side constr.rhs;
      }
    in
    { sys with body = List.map reduce_on_constr sys.body; }
  in

  let check_rigid_constraints sys =
    let check_rigid_constr sys c =
      match c.lhs.var, c.rhs.var with
      | None, None ->
        let lhs = Utils.get_single c.lhs.const in
        let rhs = Utils.get_single c.rhs.const in
        let check_fun =
          match c.kind with
          | Equal -> Pword.equal
          | Adapt -> Pword.adapt ~delay:Int.zero
        in
        if not (check_fun lhs rhs)
        then Resolution_errors.constant_inconsistency ();
        sys
      | _ -> c :: sys
    in
    { sys with body = List.fold_left check_rigid_constr [] sys.body; }
  in

  (* Simpify "c_x on p = c_y on p" into "c_x on (1) = c_y on (1)".
     This is correct but not complete. *)
  let simplify_equalities_same_p sys =
    let simplify_equality_same_p sys c =
      match c.kind with
      | Equal ->
        let lhs = Utils.get_single c.lhs.const in
        let rhs = Utils.get_single c.rhs.const in
        if Pword.equal lhs rhs
        then
          let lhs = { c.lhs with const = [Pword.unit_pword]; } in
          let rhs = { c.rhs with const = [Pword.unit_pword]; } in
          { c with lhs = lhs; rhs = rhs; } :: sys
        else
          c :: sys
      | Adapt -> c :: sys
    in
    { sys with body = List.fold_left simplify_equality_same_p [] sys.body; }
  in

  let p_sys pref sys =
    if verbose >= 5
    then
      (
        Format.printf "(* %s: @[%a@] *)@." pref print_system sys;
        flush stdout
      )
  in

  let sys = reduce_on sys in
  p_sys "Reduced system" sys;
  let sys = check_rigid_constraints sys in
  p_sys "System without rigid constraints" sys;
  let sys =
    if not complete
    then
      let sys = simplify_equalities_same_p sys in
      p_sys "System without same p equations" sys;
      sys
    else sys
  in
  let sys, pre_sol = simplify_redundant_equations sys in
  p_sys "System without redundant equations" sys;
  let sys = lower_equality_constraints sys in

  let extract c =
    assert (c.kind = Adapt);
    (c.lhs.var, Utils.get_single c.lhs.const),
    (c.rhs.var, Utils.get_single c.rhs.const)
  in
  {
    global_k = k;
    global_k' = k';
    max_burst = max_burst;
    constraints = List.map extract sys.body;

    sampler_size_per_unknown = Utils.Env.empty;
    balance_results = Utils.Env.empty;
    unfolding_per_unknown = Utils.Env.empty;
    nbones_per_unknown = Utils.Env.empty;

    synchronizability = [];
    precedence = [];
    periodicity = [];
    sufficient_size = [];
    split_prefix_period = [];
    increasing_indexes = [];
    max_burst_indexes = [];
    sufficient_indexes = [];
    objective = [];
  },
  pre_sol

(** [compute_sampler_sizes csys] returns an equivalent concrete systems [csys']
    where all the samplers of a given unknown have the same prefix and period
    sizes. These lengths are stored in the [csys'.sampler_size_per_unknown]
    field. *)
let compute_sampler_sizes csys =
  let walk_side env (co, p) =
    let open Int in
    let open Pword in

    match co with
    | None -> env
    | Some c ->
      let size_u, size_v =
        try Utils.Env.find c env with Not_found -> zero, one
      in

      let size_u = max size_u (size p.u) in
      let size_v = lcm size_v (size p.v) in

      Utils.Env.add c (size_u, size_v) env
  in

  let walk_constr env (s1, s2) = walk_side (walk_side env s1) s2 in

  let sampler_size_per_unknown =
    List.fold_left walk_constr Utils.Env.empty csys.constraints
  in

  let adjust_size (co, p) =
    let open Pword in

    co,
    match co with
    | None -> p
    | Some c ->
      let max_u, max_v = Utils.Env.find c sampler_size_per_unknown in

      let p = Pword.lengthen_prefix p Int.(max_u - size p.u) in
      let p = Pword.repeat_period p Int.(max_v / size p.v) in
      p
  in

  let adjust_constr (s1, s2) = adjust_size s1, adjust_size s2 in

  {
    csys with
      constraints = List.map adjust_constr csys.constraints;
      sampler_size_per_unknown = sampler_size_per_unknown;
  }

(**
   c_x on p_x <: c_y on p_y

   ->

        |p_x.u|_1 + k_x * (|p_x.v|_1 <> 0) = |p_y.u|_1 + k_y * (|p_y.v|_1 <> 0)
   and
        k'_x * |p_x.v|_1 = k'_y * |p_y.v|_1

*)
let solve_balance_equations solver verbose max_int csys =
  let r = ref 0 in

  let find_c lsys env c =
    try Utils.Env.find c env, lsys, env
    with Not_found ->
      let open Mllp in
      let k' = make_var lsys (c ^ "_k'") in
      k', lsys, Utils.Env.add c k' env
  in

  let add_balance_equations (lsys, env) ((co_x, p_x), (co_y, p_y)) =
    let open Pword in

    let find_vars lsys env co =
      let c =
        match co with
        | None ->
          incr r;
          "u" ^ string_of_int !r
        | Some c ->
          c
      in
      find_c lsys env c
    in

    let k'_x, lsys, env = find_vars lsys env co_x in
    let k'_y, lsys, env = find_vars lsys env co_y in

    let bal_eq_k' =
      (* |p_x.v|_1 * k'_x - |p_y.v|_1 * k'_y = 0 *)
      Mllp.(nbones p_x.v * var k'_x = nbones p_y.v * var k'_y)
    in

    Mllp.add_constraint lsys bal_eq_k', env
  in

  (* Build linear system *)
  let lsys, env =
    List.fold_left
      add_balance_equations
      (Mllp.make_system (), Utils.Env.empty)
      csys.constraints
  in

  (* Minimize variables *)
  let lsys =
    let open Mllp in
    bound_all
      (set_objective lsys (minimize_all_variables lsys))
      (Int.one, max_int)
  in

  Format.print_flush ();

  (* Solve it *)
  let sol =
    let open Mllp in
    try
      (
        match solve ~solver ~verbose:Pervasives.(verbose >= 2) lsys with
        | None -> Resolution_errors.rate_inconsistency ()
        | Some sol -> sol
      )
    with Error err ->
      Resolution_errors.solver_error err
  in

  (* Reconstruct per-unknown solution *)
  let reconstruct c _ balance_results =
    let k'_c = Utils.Env.find c env in
    let k' = Mllp.value_of sol k'_c in
    Utils.Env.add c k' balance_results
  in

  let balance_results =
    Utils.Env.fold reconstruct csys.sampler_size_per_unknown Utils.Env.empty
  in

  { csys with balance_results = balance_results; }

let choose_nbones_unknowns csys =
  let add_nbones c (sampler_u_size, sampler_v_size) nbones =
    let open Int in
    let u_nbones = sampler_u_size + find_k csys c * sampler_v_size in
    let v_nbones = find_k' csys c * sampler_v_size in
    Utils.Env.add c (u_nbones, v_nbones) nbones
  in

  {
    csys with
      nbones_per_unknown =
      Utils.Env.fold add_nbones csys.sampler_size_per_unknown Utils.Env.empty;
  }

let build_synchronizability_constraints csys =
  let add_synchronizability_constraint lsys ((co_x, p_x), (co_y, p_y)) =
    let open Pword in
    let open Int in

    let var_term co_x co_y p_x p_y =
      let k' =
        match co_y with
        | None -> one
        | Some c_y -> find_k' csys c_y
      in
      nbones p_y.v * k',
      match co_x with
      | None -> Const (size p_x.v)
      | Some c_x -> Size c_x
    in

    Eq ([var_term co_x co_y p_x p_y; neg_term (var_term co_y co_x p_y p_x)],
        zero)
    :: lsys
  in

  let synchronizability =
    List.fold_left
      add_synchronizability_constraint
      csys.synchronizability
      csys.constraints
  in

  { csys with synchronizability = synchronizability; }

let build_direct_precedence_constraints csys =
  let add_precedence_constraints lsys ((co_x, p_x), (co_y, p_y)) =
    let open Int in
    let open Pword in

    let h =
      let on_u_size co p =
        match co with
        | None -> size p.u
        | Some c -> nbones p.u + find_k csys c * nbones p.v
      in

      let on_v_size co p =
        match co with
        | None -> size p.v
        | Some c -> find_k' csys c * nbones p.v
      in

      max (on_u_size co_x p_x) (on_u_size co_y p_y)
      + lcm (on_v_size co_x p_x) (on_v_size co_y p_y)
    in

    let iof co p j =
      let i = Pword.iof p j in
      match co with
      | None -> i, Const Int.one
      | Some c -> one, Iof (c, i)
    in

    let rec build lsys j =
      if j > h then lsys
      else
        let cstr = Le ([iof co_x p_x j; neg_term (iof co_y p_y j)], Int.zero) in
        build (cstr :: lsys) (Int.succ j)
    in
    build lsys Int.one
  in

  let precedence =
    List.fold_left add_precedence_constraints csys.precedence csys.constraints
  in
  { csys with precedence = precedence; }

let build_refined_precedence_constraints csys =
  let add_precedence_constraints (lsys, seen_set) ((co_x, p_x), (co_y, p_y)) =
    let open Int in
    let open Pword in

    let h =
      let on_u_size co p =
        match co with
        | None -> size p.u
        | Some c -> nbones p.u + find_k csys c * nbones p.v
      in

      let on_v_size co p =
        match co with
        | None -> size p.v
        | Some c -> find_k' csys c * nbones p.v
      in

      max (on_u_size co_x p_x) (on_u_size co_y p_y)
      + lcm (on_v_size co_x p_x) (on_v_size co_y p_y)
    in

    let iof co i =
      match co with
      | None -> i, Const Int.one
      | Some c -> one, Iof (c, i)
    in

    let check_seen seen_set cstr =
      let seen = ConstrSet.mem cstr seen_set in
      seen, if seen then seen_set else ConstrSet.add cstr seen_set
    in

    let p_x_c_iof = Pword.cache_iof p_x in
    let p_y_c_iof = Pword.cache_iof p_y in
    let p_x_c_ones = Pword.cache_ones p_x in
    let p_y_c_ones = Pword.cache_ones p_y in

    let rec build lsys seen_set prev_o_i_x j =
      if j > h then lsys, seen_set
      else
        (* let i_x = Pword.iof p_x j in *)
        (* let i_y = Pword.iof p_y j in *)
        (* let o_i_x = Pword.ones p_x i_x in *)
        (* let o_i_y = Pword.ones p_y i_y in *)
        let i_x = Pword.iof_cached p_x_c_iof j in
        let i_y = Pword.iof_cached p_y_c_iof j in
        let o_i_x = Pword.ones_cached p_x_c_ones i_x in
        let o_i_y = Pword.ones_cached p_y_c_ones i_y in
        let lsys, seen_set =
          if o_i_x >= o_i_y && prev_o_i_x < o_i_x
          then
            let cstr = Le ([iof co_x i_x; neg_term (iof co_y i_y)], Int.zero) in
            let seen, seen_set = check_seen seen_set cstr in
            (if seen then lsys else cstr :: lsys), seen_set
          else lsys, seen_set
        in
        build lsys seen_set o_i_x (Int.succ j)
    in
    build lsys seen_set zero one
  in

  let precedence, _ =
    List.fold_left
      add_precedence_constraints
      (csys.precedence, ConstrSet.empty)
      csys.constraints
  in

  { csys with precedence = precedence; }

let build_precedence_constraints ?(build_unrefined = false) sys =
  if build_unrefined
  then build_direct_precedence_constraints sys
  else build_refined_precedence_constraints sys

let build_periodicity_constraints csys =
  let module S =
    Set.Make(Utils.OrderedTuple(Utils.OrderedString)(Int.Ordered))
  in

  let open Int in

  let check_seen seen_set c j =
    let seen = S.mem (c, j) seen_set in
    seen, if seen then seen_set else S.add (c, j) seen_set
  in

  let add_periodicity_constraint (seen_set, lsys) lv =
    match lv with
    | Size _ | Const _ -> seen_set, lsys
    | Iof (c, j') ->
      let seen, seen_set = check_seen seen_set c j' in
      if seen
      then seen_set, lsys
      else
        let nbones_c_u, nbones_c_v = find_nbones csys c in
        if j' <= nbones_c_u + nbones_c_v then seen_set, lsys
        else
          let j'_v = j' - nbones_c_u in
          let j = mod_b1 j'_v nbones_c_v + nbones_c_u in
          let l = Int.div_b1 j'_v nbones_c_v in
          assert (j' = j + l * nbones_c_v);
          assert (j > nbones_c_u && j <= nbones_c_u + nbones_c_v);
          let t1 = one, Iof (c, j') in
          let t2 = neg one, Iof (c, j) in
          let t3 = neg l, Size c in
          seen_set, Eq ([t1; t2; t3], zero) :: lsys
  in

  let add_periodicity_constraints (seen_set, lsys) lc =
    let iof_l = List.map snd (get_linear_term lc) in
    List.fold_left add_periodicity_constraint (seen_set, lsys) iof_l
  in

  let _, periodicity =
    fold_left_over_linear_constraints
      add_periodicity_constraints
      (S.empty, csys.periodicity)
      csys
  in

  { csys with periodicity = periodicity; }

let build_sufficient_size_constraints csys =
  let open Int in

  let add_sufficient_size c (nbones_c_u, nbones_c_v) lsys =
    let t1 = one, Iof (c, nbones_c_u + nbones_c_v) in
    let t2 = neg one, Iof (c, nbones_c_u + one) in
    let t3 = neg one, Size c in
    Le ([t1; t2; t3], neg one) :: lsys
  in

  let sufficient_size =
    Utils.Env.fold
      add_sufficient_size
      csys.nbones_per_unknown
      csys.sufficient_size
  in

  { csys with sufficient_size = sufficient_size; }

let build_split_prefix_period_constraints csys =
  let open Int in

  (* I_c(|c.u|_1) < I_c(|c.u|_1 + 1) == I_c(|c.u|_1 + 1) - I_c(|c.u|_1) >= 1 *)
  let add_split_prefix_period_constraint c (nbones_c_u, _) lsys =
    if nbones_c_u = zero then lsys
    else
      let t1 = one, Iof (c, succ nbones_c_u) in
      let t2 = neg one, Iof (c, nbones_c_u) in
      Ge ([t1; t2], one) :: lsys
  in

  let split_prefix_period =
    Utils.Env.fold
      add_split_prefix_period_constraint
      csys.nbones_per_unknown
      csys.split_prefix_period
  in

  { csys with split_prefix_period = split_prefix_period; }

let all_iof_constraints csys =
  let gather_iof indexes lc =
    let add indexes (_, c) =
      match c with
      | Size _ | Const _ -> indexes
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
  fold_left_over_linear_constraints gather_iof Utils.Env.empty csys

let build_increasing_indexes_constraints csys =
  let open Int in

  let indexes = all_iof_constraints csys in

  let add_increasing_indexes_constraints c indexes_for_c lsys =
    let min_j = Int.Set.min_elt indexes_for_c in
    let indexes_for_c = Int.Set.remove min_j indexes_for_c in
    let add_constraint j' (j, lsys) =
      let t1 = one, Iof (c, j') in
      let t2 = neg one, Iof (c, j) in
      let c = if csys.max_burst = Int.one then j' - j else Int.zero in
      j', Ge ([t1; t2], c) :: lsys
    in
    let _, lsys = Int.Set.fold add_constraint indexes_for_c (min_j, lsys) in
    lsys
  in

  let increasing_indexes =
    Utils.Env.fold
      add_increasing_indexes_constraints
      indexes
      csys.increasing_indexes
  in

  { csys with increasing_indexes = increasing_indexes; }

let build_indexes_max_burst_constraints csys =
  let open Int in

  if csys.max_burst = Int.one
  then csys
  else
    let indexes = all_iof_constraints csys in

    let add_max_burst_index_constraints c indexes_for_c lsys =
      let add_constraint j' (constrained, lsys) =
        let smaller, jo, constrained = Int.Env.split j' constrained in
        let jo =
          match jo with
          | Some j -> Some j
          | None ->
            (
              try
                let _, j = Int.Env.max_binding smaller in
                Some j
              with Not_found ->
                None
            )
        in
        Int.Env.add (j' + csys.max_burst) j' constrained,
        match jo with
        | None -> lsys
        | Some j ->
          assert (j < j');
          let t1 = one, Iof (c, j') in
          let t2 = neg one, Iof (c, j) in
          let c = Int.div_upper (j' - j) csys.max_burst in
          Ge ([t1; t2], c) :: lsys
      in
      let _, lsys =
        Int.Set.fold
          add_constraint
          indexes_for_c
          (Int.Env.empty, lsys)
      in
      lsys
    in

    let max_burst_indexes =
      Utils.Env.fold
        add_max_burst_index_constraints
        indexes
        csys.max_burst_indexes
    in

    { csys with max_burst_indexes = max_burst_indexes; }

(* For all I_c(j) with j minimal,

   I_c(j) >= j / max_burst
 *)
let build_sufficient_indexes_constraints csys =
  let open Int in

  let indexes = all_iof_constraints csys in

  let add_sufficient_index_constraint c indexes_for_c lsys =
    let j_min = Int.Set.min_elt indexes_for_c in
    Ge ([one, Iof (c, j_min)], succ (div_b1 j_min csys.max_burst)) :: lsys
  in

  let sufficient_indexes =
    Utils.Env.fold
      add_sufficient_index_constraint
      indexes
      csys.sufficient_indexes
  in

  { csys with sufficient_indexes = sufficient_indexes; }

let build_objective_function csys =
  let gather_term (iof_vars, size_vars) (_, t) =
    match t with
    | Iof _ -> LvarSet.add t iof_vars, size_vars
    | Size _ -> iof_vars, LvarSet.add t size_vars
    | Const _ -> iof_vars, size_vars
  in

  let gather_constraint (iof_vars, size_vars) cstr =
    let t =
      match cstr with
      | Eq (t, _)
      | Le (t, _)
      | Ge (t, _) ->
        t
    in
    List.fold_left gather_term (iof_vars, size_vars) t
  in

  let iof_vars, size_vars =
    fold_left_over_linear_constraints
      gather_constraint
      (LvarSet.empty, LvarSet.empty)
      csys
  in

  (* For now, minimize size *)
  let objective =
    LvarSet.fold (fun v t -> (Int.one, v) :: t) size_vars csys.objective
  in

  let objective =
    let add_i_nbones_prefix c (nbones_u, _) objective =
      Int.(one, Iof (c, succ nbones_u)) :: objective
    in
    Utils.Env.fold add_i_nbones_prefix csys.nbones_per_unknown objective
  in

  { csys with objective = objective; }

let solve_linear_system
    ~verbose
    ~profile
    solver
    max_int
    csys =
  let lsys = Mllp.make_system () in

  let find_size_var size_vars c =
    try size_vars, Utils.Env.find c size_vars
    with Not_found ->
      let s = "size_" ^ c in
      let v = Mllp.make_var lsys s in
      Utils.Env.add c v size_vars, v
  in

  let find_index indexes_vars c j =
    let indexes_c =
      try Utils.Env.find c indexes_vars with Not_found -> Int.Env.empty
    in

    let v, indexes_c =
      try Int.Env.find j indexes_c, indexes_c
      with Not_found ->
        let s = Printf.sprintf "I_%s_%s" c (Int.to_string j) in
        let v = Mllp.make_var lsys s in
        v, Int.Env.add j v indexes_c
    in

    Utils.Env.add c indexes_c indexes_vars, v
  in

  let translate_lvar (size_vars, indexes_vars) lv =
    match lv with
    | Size c ->
      let size_vars, v = find_size_var size_vars c in
      (size_vars, indexes_vars), Mllp.var v
    | Iof (c, j) ->
      let indexes_vars, v = find_index indexes_vars c j in
      (size_vars, indexes_vars), Mllp.var v
    | Const cst ->
      (size_vars, indexes_vars), Mllp.const cst
  in

  let translate_linear_term acc (i, lv) =
    let acc, t = translate_lvar acc lv in
    acc, Mllp.(i * t)
  in

  let translate_linear_terms acc t_l =
    let acc, t_l = Utils.mapfold_left translate_linear_term acc t_l in
    acc, Utils.fold_left_1 Mllp.(+) t_l
  in

  let translate_linear_constr (vars, lsys) cstr =
    let open Mllp in
    match cstr with
    | Eq (t, cst) ->
      let vars, t = translate_linear_terms vars t in
      vars, add_constraint lsys (t = const cst)
    | Le (t, cst) ->
      let vars, t = translate_linear_terms vars t in
      vars, add_constraint lsys (t <= const cst)
    | Ge (t, cst) ->
      let vars, t = translate_linear_terms vars t in
      vars, add_constraint lsys (t >= const cst)
  in

  let acc, lsys =
    fold_left_over_linear_constraints
      translate_linear_constr
      ((Utils.Env.empty, Utils.Env.empty), lsys)
      csys
  in

  let (size_vars, indexes_vars), obj =
    translate_linear_terms acc csys.objective
  in

  let lsys = Mllp.(set_objective lsys (Minimize obj)) in
  let lsys = Mllp.bound_all lsys (Int.one, max_int) in

  Format.print_flush ();

  let lsol =
    try
      (
        match Mllp.solve ~solver ~verbose:(verbose >= 2) ~profile lsys with
        | Some sol -> sol
        | None -> Resolution_errors.precedence_inconsistency ()
      )
    with Mllp.Error err -> Resolution_errors.solver_error err
  in

  let reconstruct_word c (nbones_c_u, nbones_c_v) sol =
    let indexes_for_c = Utils.Env.find c indexes_vars in

    let size_c_v =
      let size_v = Utils.Env.find c size_vars in
      Mllp.value_of lsol size_v
    in

    let size_c_u =
      let first_one_v = Int.Env.find (Int.succ nbones_c_u) indexes_for_c in
      Int.pred (Mllp.value_of lsol first_one_v)
    in

    let iof =
      let add j v_i iof = (j, Mllp.value_of lsol v_i) :: iof in
      List.rev (Int.Env.fold add indexes_for_c [])
    in

    let iof_u =
      List.filter (fun (j, _) -> j <= nbones_c_u) iof
    in
    let iof_v =
      let open Int in
      let iof_v =
        let is_in_period (j, _) =
          j > nbones_c_u && j <= nbones_c_u + nbones_c_v
        in
        List.filter is_in_period iof
      in
      List.map (fun (j, i) -> j - nbones_c_u, i - size_c_u) iof_v
    in

    let u =
      Pword.make_word_alap
        ~max_burst:csys.max_burst
        ~size:size_c_u
        ~nbones:nbones_c_u
        iof_u
    in
    let v =
      Pword.make_word_alap
        ~max_burst:csys.max_burst
        ~size:size_c_v
        ~nbones:nbones_c_v
        iof_v
    in

    Utils.Env.add c (Pword.make u v) sol
  in
  Utils.Env.fold reconstruct_word csys.nbones_per_unknown Utils.Env.empty

(* This function takes a system, a pre-solution (mapping eliminated
   unknowns to unknowns) and a solution (mapping unknowns to words),
   and returns a solution *)
let build_solution sys pre_sol sol =
  let add_sol c final_sol =
    (* Three cases, examinated in order:
       - c -> p is present in sol, we map c to p in final_sol
       - c -> c_final is present in pre_sol, we look for c_final into sol
       - c is absent in both pre_sol and sol, then it was
       completely eliminated and we map it to (1) *)
    let p =
      try Utils.Env.find c sol
      with Not_found ->
        try Utils.Env.find (Utils.Env.find c pre_sol) sol
        with Not_found -> Pword.unit_pword
    in
    Utils.Env.add c (Pword.to_tree_pword p) final_sol
  in
  Utils.String_set.fold add_sol (unknowns_of_system sys) Utils.Env.empty

let solve sys =
  let open Resolution_options in
  let verbose =
    Int.to_int (find_int ~default:Int.zero sys.options "verbose")
  in
  let max_int =
    find_int ~default:(Int.of_int Pervasives.max_int) sys.options "max_int"
  in
  let profile = find_bool ~default:false sys.options "profile" in

  let solver =
    let table =
      [
        "glpk", Mllp.Glpk;
        "gurobi", Mllp.Gurobi;
      ]
    in
    try List.assoc (find_string ~default:"glpk" sys.options "ilp") table
    with Not_found -> Resolution_errors.bad_option "solver"
  in

  let run_profiled pref f x =
    if profile then Utils.time_call ~name:pref f x else f x
  in

  let csys, pre_sol =
    let k = find_int ~default:Int.zero sys.options "k" in
    let k' = find_int ~default:Int.one sys.options "k'" in
    let max_burst = find_int ~default:Int.one sys.options "max_burst" in
    let complete = find_bool ~default:false sys.options "complete" in
    run_profiled
      "make_concrete_system"
      (make_concrete_system ~k ~k' ~max_burst ~complete verbose)
      sys
  in

  let csys =
    run_profiled "compute_sampler_sizes" compute_sampler_sizes csys
  in
  let csys =
    run_profiled
      "solve_balance_equations"
      (solve_balance_equations solver verbose max_int)
      csys
  in
  let csys =
    run_profiled "choose_nbones_unknowns" choose_nbones_unknowns csys
  in
  if verbose >= 1
  then
    Format.printf "(* Adjusted concrete system: @[%a@] *)@."
      print_concrete_system csys;
  let csys =
    run_profiled
      "build_synchronizability_constraints"
      build_synchronizability_constraints
      csys
  in
  let csys =
    let build_unrefined = find_bool ~default:false sys.options "unrefined" in
    run_profiled
      "build_precedence_constraints"
      (build_precedence_constraints ~build_unrefined)
      csys
  in
  let csys =
    run_profiled
      "build_periodicity_constraints"
      build_periodicity_constraints
      csys
  in
  let csys =
    run_profiled
      "build_sufficient_indexes_constraints"
      build_sufficient_size_constraints
      csys
  in
  let csys =
    run_profiled
      "build_split_prefix_period_constraints"
      build_split_prefix_period_constraints
      csys
  in
  let csys =
    run_profiled
      "build_increasing_indexes_constraints"
      build_increasing_indexes_constraints
      csys
  in
  let csys =
    run_profiled
      "build_indexes_max_burst_constraints"
      build_indexes_max_burst_constraints
      csys
  in
  let csys =
    run_profiled
      "build_sufficient_indexes_constraints"
      build_sufficient_indexes_constraints
      csys
  in
  let csys =
    run_profiled
      "build_objective_function"
      build_objective_function
      csys
  in
  if verbose >= 4
  then
    Format.printf "(* Linear system: @[%a@] *)@."
      print_linear_systems csys;
  let sol =
    run_profiled
      "solve_linear_system"
      (solve_linear_system ~verbose ~profile solver max_int)
      csys
  in
  build_solution sys pre_sol sol
