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

(** {2 Exceptions} *)

type error =
  | Duplicate_variable of string
  | No_objective
  | No_bounds
  | Internal_error of string
  | Internal_solver_error of int

exception Error of error

let print_error fmt err =
  match err with
  | Duplicate_variable name ->
    Format.fprintf fmt "duplicate variable %s" name
  | No_objective ->
    Format.fprintf fmt "no objective"
  | No_bounds ->
    Format.fprintf fmt "no bounds"
  | Internal_error reason ->
    Format.fprintf fmt "internal error (%s)" reason
  | Internal_solver_error code ->
    Format.fprintf fmt "internal solver (exit code %d)" code

let duplicate_variable name = raise (Error (Duplicate_variable name))

let no_objective () = raise (Error No_objective)

let no_bounds () = raise (Error No_bounds)

let internal_error reason = raise (Error (Internal_error reason))

let internal_solver_error code = raise (Error (Internal_solver_error code))

(** {2 Type definitions} *)

type var = Mllp_backend.var

type term =
  | Var of var
  | Const of Int.t
  | Add of term * term
  | Sub of term * term
  | Mult of Int.t * term

type comp = Lt | Le | Gt | Ge | Eq

type cstr =
  {
    lhs : term;
    comp : comp;
    rhs : term;
  }

type objective =
  | Minimize of term
  | Mazimize of term

type system =
  {
    vars : (string, var) Hashtbl.t;
    mutable next_free_var : int;
    cstrs : cstr list;
    obj : objective option;
    bounds : (Int.t * Int.t) option;
  }

(** {2 Systems} *)

open Mllp_backend

let make_system () =
  {
    vars = Hashtbl.create 117;
    next_free_var = 0;
    cstrs = [];
    obj = None;
    bounds = None;
  }

let make_var sys name =
  if Hashtbl.mem sys.vars name
  then duplicate_variable name
  else
    let v =
      {
        name = name;
        id = sys.next_free_var;
      }
    in
    sys.next_free_var <- sys.next_free_var + 1;
    Hashtbl.add sys.vars name v;
    v

(** {2 Terms and constraints} *)

let var x = Var x

let const cst = Const cst

let ( + ) t1 t2 = Add (t1, t2)

let ( - ) t1 t2 = Sub (t1, t2)

let ( * ) v t = Mult (v, t)

let make_cstr comp lhs rhs = { lhs = lhs; comp = comp; rhs = rhs; }

let ( < ) = make_cstr Lt

let ( <= ) = make_cstr Le

let ( > ) = make_cstr Gt

let ( >= ) = make_cstr Ge

let ( = ) = make_cstr Eq

(** {2 System construction} *)

let add_constraint sys cstr = { sys with cstrs = cstr :: sys.cstrs; }

let minimize_all_variables sys =
  let form_obj _ v obj = var v + obj in
  Minimize (Hashtbl.fold form_obj sys.vars (const Int.zero))

let set_objective sys obj = { sys with obj = Some obj; }

let bound_all sys bounds = { sys with bounds = Some bounds; }

(** {2 Utilities} *)

(* Term to sum of products *)
let low_level_term
    ?(factor = Int.one)
    ?(sop = Utils.Int_map.empty)
    term
    =
  let rec eval factor sop term =
    let open Int in
    match term with
    | Var v ->
      (
        let v_factor =
          try fst (Utils.Int_map.find v.id sop)
          with Not_found -> zero
        in
        zero, Utils.Int_map.add v.id (factor + v_factor, v) sop
      )
    | Const c ->
      c, sop
    | Add (t1, t2) ->
      let c1, sop = eval factor sop t1 in
      let c2, sop = eval factor sop t2 in
      c1 + c2, sop
    | Sub (t1, t2) ->
      let c1, sop = eval factor sop t1 in
      let c2, sop = eval (neg factor) sop t2 in
      c1 - c2, sop
    | Mult (c, t) ->
      eval (c * factor) sop t
  in
  eval factor sop term

let term_of_sop sop : Mllp_backend.term =
  let add _ (i, v) term =
    if Int.(i = zero) then term else (i, v) :: term
  in
  Utils.Int_map.fold add sop []

let low_level_constraint acc cstr =
  let open Int in
  (* [compute (x + c1) (y + c2)] returns [x - y, c2 - c1]  *)
  let compute lhs rhs : Mllp_backend.term * Int.t =
    let c1, sop = low_level_term lhs in
    let c2, sop = low_level_term ~sop ~factor:Int.(neg one) rhs in
    term_of_sop sop, c2 - c1
  in

  let add (t, c) acc =
    if Pervasives.(=) t [] then (assert (c = zero); acc) else (t, c) :: acc
  in

  match cstr.comp with
  | Le ->
    (*
      x + c1 <= y + c2
      ->
      x - y <= c2 - c1
    *)
    add (compute cstr.lhs cstr.rhs) acc
  | Lt ->
    (*
      x + c1 < y + c2
      ->
      x - y <= c2 - c1 - 1
    *)
    let t, c = compute cstr.lhs cstr.rhs in
    add (t, pred c) acc
  | Ge ->
    (*
      x + c1 >= y + c2
      ->
      x - y >= c1 - c2
      ->
      y - x <= c2 - c1
    *)
    add (compute cstr.rhs cstr.lhs) acc
  | Gt ->
    (*
      x + c1 > y + c2
      ->
      x - y > c1 - c2
      ->
      y - x < c2 - c1
      ->
      y - x <= c2 - c1 - 1
    *)
    let t, c = compute cstr.rhs cstr.lhs in
    add (t, pred c) acc
  | Eq ->
    (*
      x + c1 = y + c2
      ->
      x - y = c2 - c1
      ->
      x - y <= c2 - c1
      x - y >= c2 - c1
      ->
      x - y <= c2 - c1
      y - x <= c1 - c2
    *)
    add (compute cstr.lhs cstr.rhs) (add (compute cstr.rhs cstr.lhs) acc)

let low_level_system_of_system sys =
  match sys.obj, sys.bounds with
  | None, _ -> no_objective ()
  | _, None -> no_bounds ()
  | Some obj, Some bounds ->
    let _, sop_obj_minimize =
      match obj with
      | Minimize obj -> low_level_term obj
      | Mazimize obj -> low_level_term ~factor:Int.(neg one) obj
    in
    {
      ll_minimize = term_of_sop sop_obj_minimize;
      ll_constraints = List.fold_left low_level_constraint [] sys.cstrs;
      ll_bounds = bounds;
      ll_vars = sys.vars;
    }

(** {2 Resolution} *)

type solution = Int.t Utils.Int_map.t

type solver =
  | Glpk
  | Gurobi

let prefered = Glpk

let backend_of_solver solver =
  match solver with
  | Glpk -> Mllp_backend_glpk.backend
  | Gurobi -> Mllp_backend_gurobi.backend

let solve
    ?(solver = prefered)
    ?(verbose = false)
    ?(profile = false)
    sys =
  if Pervasives.(=) sys.next_free_var 0
  then Some Utils.Int_map.empty
  else
    let backend = backend_of_solver solver in
    let log_fn = Filename.temp_file "mllp-" ".log" in
    let prob_fn = Filename.temp_file "mllp-" ".lp" in
    let out_fns =
      List.map
        (fun ext -> Filename.temp_file "mllp-" ("." ^ ext))
        backend.output_exts
    in
  (* Translate to low-level system *)
    let sys = low_level_system_of_system sys in
  (* Write problem file *)
    let prob_chan = open_out prob_fn in
    backend.write_problem_file prob_chan sys;
    close_out prob_chan;
  (* Solve system *)
    let cmd =
      backend.make_command
        ~log:log_fn
        ~problem:prob_fn
        ~outputs:out_fns
    in
    if verbose
    then
      Format.printf
        "(* @[Problem:\t%s@\nSolutions:\t@[%a@]@\nCommand:\t%s@] *)@\n"
        prob_fn
        (Utils.print_list_r Utils.print_string ",") out_fns
        cmd
    ;
    let status =
      if profile
      then Utils.time_call ~name:"to linear solver" Sys.command cmd
      else Sys.command cmd
    in
    if status <> 0 then internal_solver_error status;
  (* Read solution *)
    let out_chans = List.map open_in out_fns in
    let solution = backend.read_solution_files out_chans sys in
    List.iter close_in out_chans;
    match solution with
    | Solution sol -> Some sol
    | No_solution -> None
    | Error reason -> internal_error reason

let value_of sol v = Utils.Int_map.find v.id sol
