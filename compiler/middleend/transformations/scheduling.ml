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

open Scheduler

(** {2 Errors} *)

type err =
  | Unknown_scheduler of string

exception Scheduling_error of err

let print_error fmt err =
  match err with
  | Unknown_scheduler name ->
    Format.fprintf fmt "Unknown scheduler %s" name

let unknown_scheduler name =
  raise (Scheduling_error (Unknown_scheduler name))

(** {2 Scheduler table} *)

let schedulers : (string * (module SCHEDULER)) list =
  [
    "naive", (module Scheduler_naive.S);
  ]

let current_scheduler () =
  let name = !Compiler_options.scheduler in
  try List.assoc name schedulers with Not_found -> unknown_scheduler name

let node () nd =
  let module SCHEDULER = (val current_scheduler ()) in
  let module P = Scheduler.Make(SCHEDULER) in
  P.node nd

(** {2 The pass itself} *)

module U = Middleend_utils.Make(Nir_sliced)(Nir_sliced)

let tr ctx file =
  U.map_to_nodes (node ()) ctx file

let pass =
  U.(make_transform "scheduling" tr)

let _ =
  Compiler_options.scheduler_list := List.map fst schedulers;
  Compiler_options.scheduler := fst (List.hd schedulers)
