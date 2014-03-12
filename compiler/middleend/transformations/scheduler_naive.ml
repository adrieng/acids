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

module G = Graph.Pack.Digraph

module S =
struct
  type deps =
    {
      mutable ids : G.vertex Utils.Int_map.t;
      g : G.t;
    }

  let make () =
    {
      ids = Utils.Int_map.empty;
      g = G.create ();
    }

  let find deps eq_id =
    try Utils.Int_map.find eq_id deps.ids
    with Not_found ->
      let v = G.V.create eq_id in
      G.add_vertex deps.g v;
      deps.ids <- Utils.Int_map.add eq_id v deps.ids;
      v

  let add_eq deps eq_id _ =
    ignore (find deps eq_id)

  let add_dependency deps eq_id1 eq_id2 =
    G.add_edge deps.g (find deps eq_id1) (find deps eq_id2)

  type schedule = int Utils.Int_map.t

  let compare sched eq_id1 eq_id2 =
    let rank1 = Utils.Int_map.find eq_id1 sched in
    let rank2 = Utils.Int_map.find eq_id2 sched in
    Utils.int_compare rank1 rank2

  let schedule deps =
    let add v (rank, sched) =
      let eq_id = G.V.label v in
      rank + 1, Utils.Int_map.add eq_id rank sched
    in
    let _, sched = G.Topological.fold add deps.g (0, Utils.Int_map.empty) in
    sched
end
