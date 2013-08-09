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

type error =
  | Ill_formed_objective_function
  | Solver_internal_error of int
  | Could_not_parse_solution of string (* file name *)
  | Library_internal_error
  | Could_not_solve

exception Error of error

let print_error fmt err =
  match err with
  | Ill_formed_objective_function ->
    Format.fprintf fmt "ill-formed objective function"
  | Solver_internal_error exit_code ->
    Format.fprintf fmt "solver exited with code %d" exit_code
  | Could_not_parse_solution sol_fn ->
    Format.fprintf fmt "could not parse linear solver output (%s)" sol_fn
  | Library_internal_error ->
    Format.fprintf fmt "linear solver internal error"
  | Could_not_solve ->
    Format.fprintf fmt "could not solve linear system"

let ill_formed_objective_function () =
  raise (Error Ill_formed_objective_function)

let solver_internal_error exit_code =
  raise (Error (Solver_internal_error exit_code))

let could_not_parse_solution sol_fn =
  raise (Error (Could_not_parse_solution sol_fn))

let library_internal_error () =
  raise (Error Library_internal_error)

let could_not_solve () =
  raise (Error Could_not_solve)

type var = string

type terms = (Int.t * var) list

type linear_comp = Leq | Lgt | Lge | Llt | Lle

type linear_constraint =
  {
    lc_terms : (Int.t * string) list;
    lc_comp : linear_comp;
    lc_const : Int.t;
  }

type linear_system =
  {
    ls_variables : Utils.String_set.t;
    ls_constraints : linear_constraint list;
    ls_bounds : (Int.t * Int.t) Utils.Env.t;
    ls_objective : terms;
  }

let empty_system =
  {
    ls_variables = Utils.String_set.empty;
    ls_bounds = Utils.Env.empty;
    ls_constraints = [];
    ls_objective = [];
  }

let negate_terms terms = List.map (fun (c, id) -> Int.neg c, id) terms

let add_variable lsys s =
  if Utils.String_set.mem s lsys.ls_variables
  then invalid_arg ("add_var: duplicate variable " ^ s);
  { lsys with ls_variables = Utils.String_set.add s lsys.ls_variables; }, s

let make_equality x c y c' =
  {
    lc_terms = x @ negate_terms y;
    lc_comp = Leq;
    lc_const = Int.(c' - c);
  }

let add_vars_of_terms sys terms =
  let vars = List.map snd terms in
  { sys with
    ls_variables = List.fold_right Utils.String_set.add vars sys.ls_variables; }

let factor_variables_in_constraint lc =
  let open Int in

  let add cstr (i, v) =
    let i' = try Utils.Env.find v cstr with Not_found -> zero in
    Utils.Env.add v (i + i') cstr
  in

  let cstr = List.fold_left add Utils.Env.empty lc.lc_terms in

  let add k i term = if i = Int.zero then term else (i, k) :: term in

  { lc with lc_terms = Utils.Env.fold add cstr []; }

let add_constraint sys lc =
  let lc = factor_variables_in_constraint lc in
  match lc.lc_terms with
  | [] -> sys
  | _ :: _ ->
    let sys = add_vars_of_terms sys lc.lc_terms in
    { sys with ls_constraints = lc :: sys.ls_constraints; }

let minimize_all_variables sys =
  Utils.String_set.fold (fun id obj -> (Int.one, id) :: obj) sys.ls_variables []

let set_objective_function sys obj =
  let sys = add_vars_of_terms sys obj in
  { sys with ls_objective = obj; }

let bound_variable (min, max) sys id =
  {
    sys with
      ls_bounds = Utils.Env.add id (min, max) sys.ls_bounds;
      ls_variables = Utils.String_set.add id sys.ls_variables;
  }

let bound_all_variables sys (min, max) =
  let bound id bounds = Utils.Env.add id (min, max) bounds in
  let bounds =
    Utils.String_set.fold bound sys.ls_variables sys.ls_bounds
  in
  { sys with ls_bounds = bounds; }

(********** I/O RELATED FUNCTIONS **********)

let variables_in_textual_order sys =
  let add_variable (variables, waiting) var =
    if Utils.String_set.mem var waiting
    then (var :: variables, Utils.String_set.remove var waiting)
    else (variables, waiting)
  in

  let add_variables_of_terms (variables, waiting) term =
    List.fold_left add_variable (variables, waiting) (List.map snd term)
  in

  let variables, waiting =
    add_variables_of_terms ([], sys.ls_variables) sys.ls_objective
  in

  let walk_constraints (variables, waiting) cstr =
    if Utils.String_set.cardinal waiting = 0 then (variables, waiting)
    else add_variables_of_terms (variables, waiting) cstr.lc_terms
  in

  let variables, _ =
    List.fold_left walk_constraints (variables, waiting) sys.ls_constraints
  in
  List.rev variables

type solver_command = string

let replace_vars_in_command ~sys_fn ~sol_fn ~out_fn ~log_fn cmd =
  let open Str in
  let cmd = replace_first (regexp "%SYS") sys_fn cmd in
  let cmd = replace_first (regexp "%SOL") sol_fn cmd in
  let cmd = replace_first (regexp "%OUT") out_fn cmd in
  let cmd = replace_first (regexp "%LOG") log_fn cmd in
  cmd

let default_solver_command : solver_command =
  "glpsol --cpxlp -o %OUT -w %SOL --log %LOG %SYS >/dev/null"
  (* "gurobi_cl LogFile=%LOG ResultFile=%SOL %SYS" *)

let write_const_cplex_format fmt cst =
  let sign = if cst < Int.zero then "-" else "+" in
  Format.fprintf fmt "%s %a" sign Int.print (Int.abs cst)

let print_var fmt v = Format.fprintf fmt "%s" v

let write_terms_cplex_format fmt terms =
  let write_term (cst, var) =
    Format.fprintf fmt " %a %a"
      write_const_cplex_format cst
      print_var var
  in
  List.iter write_term terms

let write_comparator_cplex_format fmt cmp =
  let table =
    [
      (Leq, "=");
      (Lgt, ">");
      (Lge, ">=");
      (Llt, "<");
      (Lle, "<=");
    ]
  in
  Format.fprintf fmt "%s" (List.assoc cmp table)

let write_constraint_cplex_format fmt constr =
  Format.fprintf fmt " %a %a %a@\n"
    write_terms_cplex_format constr.lc_terms
    write_comparator_cplex_format constr.lc_comp
    write_const_cplex_format constr.lc_const

let print_system fmt lsys =
  Format.fprintf fmt
    "Minimize @[%a@]@\n"
    write_terms_cplex_format lsys.ls_objective;
  Format.fprintf fmt "Subject to:@\n";
  List.iter (write_constraint_cplex_format fmt) lsys.ls_constraints;
  Format.fprintf fmt "@?"

let write_system_cplex_format sys sys_file =
  let fmt = Format.formatter_of_out_channel sys_file in

  (* Header *)
  Format.fprintf fmt "Minimize@\n";
  Format.fprintf fmt " %a@\n" write_terms_cplex_format sys.ls_objective;
  Format.fprintf fmt "@\n";

  (* Constraints *)
  Format.fprintf fmt "Subject To@\n";
  List.iter (write_constraint_cplex_format fmt) sys.ls_constraints;
  Format.fprintf fmt "@\n";

  (* Bounds *)

  let write_bound_cplex_format fmt id (min, max) =
    Format.fprintf fmt " %a <= %s <= %a@\n"
      Int.print min
      id
      Int.print max
  in

  Format.fprintf fmt "Bounds@\n";
  Utils.Env.iter (write_bound_cplex_format fmt) sys.ls_bounds;
  Format.fprintf fmt "@\n";

  (* Variable declarations *)
  (* Only integer variables for now *)

  Format.fprintf fmt "Integers@\n";
  Utils.String_set.iter
    (fun s -> Format.fprintf fmt " %s@\n" s)
    sys.ls_variables;
  Format.fprintf fmt "end@."

(* Read solution in GLP MIP format *)
let read_solution sys sol_fn =
  let sol_file = open_in sol_fn in
  (* Format:

     m n
     stat obj_val
     r_val[1]
     ...
     r_val[m]
     c_val[1]
     ...
     c_val[n]

     where
     m: row count
     n: column count
     stat: sol status (UNDEF = 1, FEASIBLE = 2, NOFEASIBLE = 4, OPTIMAL = 5)
     obj_val: objective function value
  *)

  (* See GLPK manual, pp. 105-106 *)

  try
    let read_two_integers () =
      let l = input_line sol_file in
      Scanf.sscanf l "%d %d" (fun i1 i2 -> (Int.of_int i1, Int.of_int i2))
    in

    let read_one_integer () =
      let l = input_line sol_file in
      Scanf.sscanf l "%d" (fun i -> Int.of_int i)
    in

    let m, n = read_two_integers () in
    let stat, _ = read_two_integers () in

    if stat <> Int.of_int 2 && stat <> Int.of_int 5 then could_not_solve ();

    if n <> Int.of_int (Utils.String_set.cardinal sys.ls_variables)
    then library_internal_error ();

    let rec skip_rows m =
      if m = Int.zero then ()
      else (ignore (input_line sol_file); skip_rows Int.(m - one))
    in
    skip_rows m;

    let ordered_vars = variables_in_textual_order sys in

    if Int.of_int (List.length ordered_vars) <> n
    then library_internal_error ();

    let read_column_solution solutions var =
      let s = read_one_integer () in
      Utils.Env.add var s solutions
    in

    let res =
      List.fold_left read_column_solution Utils.Env.empty ordered_vars
    in
    close_in sol_file;
    res
  with
  | End_of_file | Scanf.Scan_failure _ ->
    close_in sol_file;
    could_not_parse_solution sol_fn

module Env = Utils.Env

let solve ?(command = default_solver_command) ?(verbose = false) sys =
  if sys.ls_variables = Utils.String_set.empty then Utils.Env.empty
  else
    (
      if sys.ls_objective = [] then ill_formed_objective_function ();

      let sys =
        if sys.ls_constraints <> []
        then sys
        else
          (* Since stupid linear solvers such as GLPK do not accept empty
             Subject To sections, we add a dummy variable and trivial constraint
             "dummy = 0". *)
          let dummy_v =
            let rec find i =
              let v = "dummy" ^ string_of_int i in
              if Utils.String_set.mem v sys.ls_variables
              then find (i + 1) else v
            in
            find 0
          in

          let sys, dummy_v = add_variable sys dummy_v in

          let sys = bound_variable (Int.zero, Int.zero) sys dummy_v in

          let dummy_constraint =
            {
              lc_terms = [Int.one, dummy_v];
              lc_comp = Leq;
              lc_const = Int.zero;
            }
          in

          add_constraint sys dummy_constraint
      in

      let sys_fn, sys_file = Filename.open_temp_file "sys-" ".lp" in
      let sol_fn = Filename.temp_file "sol-" ".sol" in
      let out_fn = Filename.temp_file "out-" ".out" in
      let log_fn = Filename.temp_file "log-" ".log" in

      if verbose then
        begin
          Format.printf "(* @[Problem file:\t%s@\n" sys_fn;
          Format.printf "Solution file:\t%s@\n" sol_fn;
          Format.printf "Output file:\t%s@\n" out_fn;
          Format.printf "Log file:\t%s@] *)@\n" log_fn;
        end;

      write_system_cplex_format sys sys_file;
      close_out sys_file;

      let cmd =
        replace_vars_in_command ~sys_fn ~sol_fn ~out_fn ~log_fn command
      in

      if verbose then Format.printf "(* Running: %s *)@." cmd;

      let status =
        if verbose
        then Utils.time_call ~name:"to linear solver" Sys.command cmd
        else Sys.command cmd
      in

      if verbose then Format.printf "(* Solving process terminated. *)@\n";

      if status <> 0 then solver_internal_error status;
      let solution = read_solution sys sol_fn in
      solution
    )
