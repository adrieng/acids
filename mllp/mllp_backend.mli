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

type var =
  {
    name : string;
    id : int;
  }

type term = (Int.t * var) list

type low_level_system =
  {
    ll_minimize : term;
    ll_constraints : (term * Int.t) list; (* Ax <= B *)
    ll_bounds : Int.t * Int.t;
    ll_vars : (string, var) Hashtbl.t;
  }

type status =
  | Solution of Int.t Utils.Int_map.t
  | No_solution
  | Error of string

type backend =
  {
    output_exts : string list;
    write_problem_file : out_channel -> low_level_system -> unit;
    make_command :
      log:string ->
      problem:string ->
      outputs:string list ->
      string;
    read_solution_files :
      in_channel list -> low_level_system -> status;
  }
