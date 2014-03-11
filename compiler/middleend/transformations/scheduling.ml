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

open Nir_sliced
type eq_id = int

module type SCHEDULER =
sig
  type deps
  val make : unit -> deps
  val add_eq : deps -> eq_id -> eq -> unit
  (** [add_dependency_for_eq deps eq_id x y] notifies [deps] that [y] depends on
      [x] because of the equation corresponding to [eq_id]. In other words, [x]
      should be scheduled done before [y]. *)
  val add_dependency_for_eq : deps -> eq_id -> Ident.t -> Ident.t -> unit

  type schedule
  val compare : schedule -> eq_id -> eq_id -> int

  val schedule : deps -> schedule
end

module Make(S : SCHEDULER) =
struct
  let rec schedule_eq deps eq_id eq =
    S.add_eq deps eq_id eq;
    (* At this point in the compiler all functions are strict *)
    let outputs = eq_output [] eq in
    let inputs = eq_input [] eq in
    List.iter
      (fun inp ->
        List.iter
          (S.add_dependency_for_eq deps eq_id inp)
          outputs)
      inputs;
    let eq =
      match eq.eq_desc with
      | Var _ | Const _ | Pword _ | Call _ | Merge _ | Split _ | Buffer _
      | Delay _ ->
        eq
      | Block block ->
        make_eq
          ~loc:eq.eq_loc
          (Block (schedule_block block))
          eq.eq_base_clock
    in
    eq_id + 1, (eq_id, eq)

  and schedule_block block =
    let deps = S.make () in
    let _, body = Utils.mapfold_left (schedule_eq deps) 0 block.b_body in
    let sched = S.schedule deps in
    let body =
      List.sort
        (fun (eq_id1, _) (eq_id2, _) -> S.compare sched eq_id1 eq_id2)
        body
    in
    make_block
      ~loc:block.b_loc
      block.b_id
      (List.map snd body)

  let node () nd =
    make_node
      ~loc:nd.n_loc
      nd.n_name
      nd.n_orig_info
      ~input:nd.n_input
      ~output:nd.n_output
      ~env:nd.n_env
      ~body:(schedule_block nd.n_body)

  module U = Middleend_utils.Make(Nir_sliced)(Nir_sliced)

  let tr ctx file =
    U.map_to_nodes (node ()) ctx file

  let pass =
    U.(make_transform "scheduling" tr)
end
