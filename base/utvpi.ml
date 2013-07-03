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

module Int_ =
struct
  type t = int
  let compare x y = x - y
  let equal x y = 0 = compare x y
  let hash = Hashtbl.hash
end

module Edge =
struct
  type t =
      {
        weight : Int.t;
        mutable pred : int;
      }
  let compare = Pervasives.compare
  let default = { weight = Int.zero; pred = 0; }
end

open Edge
module G = Graph.Imperative.Digraph.ConcreteBidirectionalLabeled(Int_)(Edge)

type t =
    {
      graph : G.t;
      mutable env : int Utils.String_map.t;
      mutable last : int;
    }

type var = int

let make_system () =
  {
    graph = G.create ();
    env = Utils.String_map.empty;
    last = 1;
  },
  0

let print_var env fmt i =
  if i = 0
  then Format.fprintf fmt "0"
  else
    let print_var v j = if i = j then Format.fprintf fmt "%s" v in
    Utils.String_map.iter print_var env

let print_system fmt g =
  let print_constraint edge =
    let x = G.V.label (G.E.src edge) in
    let y = G.V.label (G.E.dst edge) in
    let c = G.E.label edge in
    Format.fprintf fmt "  %a - %a <= %a@\n"
      (print_var g.env) y
      (print_var g.env) x
      Int.print c.weight
  in
  Format.fprintf fmt "@[";
  G.iter_edges_e print_constraint g.graph;
  Format.fprintf fmt "@]"

(* UGLY *)
let r = ref Utils.String_map.empty
module D = Graph.Graphviz.Dot(
  struct
    include G

    let graph_attributes _ =
      [`Orientation `Landscape; `Rankdir `LeftToRight]
    let default_vertex_attributes _ = []
    let vertex_name v = string_of_int (G.V.label v)
    let vertex_attributes v =
      let s =
        ignore (Format.flush_str_formatter ());
        Format.fprintf Format.str_formatter "%a" (print_var !r) (G.V.label v);
        Format.flush_str_formatter ()
      in
      [`Label s]
    let get_subgraph _ = None
    let default_edge_attributes _ = []
    let edge_attributes e = [`Label (Int.to_string (G.E.label e).weight)]
  end)

let print_system_dot fmt g =
  r := g.env;
  D.output_graph fmt g.graph;
  r := Utils.String_map.empty

(** [add_constraint sys x y c] returns the system [sys] with the added
    constraint [y - x <= c] *)
let add_constraint g x y c =
  let edge = G.E.create x { weight = c; pred = x; } y in
  G.add_edge_e g.graph edge

let add_variable g id =
  if Utils.String_map.mem id g.env
  then invalid_arg ("Utvpi.add_variable: " ^ id);
  g.env <- Utils.String_map.add id g.last g.env;
  (* add_constraint g g.last 0 Z.zero; *)
  g.last <- g.last + 1;
  g.last - 1

let dualize_system g =
  let dual_g = G.create () in

  let add_dual_edge edge =
    let x = G.V.label (G.E.src edge) in
    let y = G.V.label (G.E.dst edge) in
    let c = G.E.label edge in

    let d_edge = G.E.create y c x in
    G.add_edge_e dual_g d_edge
  in
  G.iter_edges_e add_dual_edge g.graph;

  {
    graph = dual_g;
    last = g.last;
    env = g.env;
  }

exception No_solution

type objective = Maximize | Minimize

(* Bellman-Ford algorithm *)
let solve_system
    ?(verbose = false)
    ?(bound = Int.of_int 100000000)
    ~obj
    sys =
  let sys = match obj with Maximize -> sys | Minimize -> dualize_system sys in
  let dist = Array.make sys.last bound in
  dist.(0) <- Int.zero;

  if verbose
  then
    Format.eprintf "Running Bellman-Ford, %d variables...@?" sys.last;

  let changed = ref true in
  let i = ref 0 in

  (* Relaxation phase *)
  while !changed && !i < sys.last do
    changed := false;
    incr i;

    let relax_edge edge =
      let x = G.V.label (G.E.src edge) in
      let y = G.V.label (G.E.dst edge) in
      let xy = G.E.label edge in

      let d_from_x = Int.(dist.(x) + xy.weight) in

      if d_from_x < dist.(y) then
        (
          changed := true;
          dist.(y) <- d_from_x;
          xy.pred <- x;
        )
    in
    G.iter_edges_e relax_edge sys.graph;
  done;

  (* Check for negative-weight cycles *)
  let check_edge edge =
    let xy = G.E.label edge in
    let x = xy.pred in
    let y = G.V.label (G.E.dst edge) in

    if Int.(dist.(x) + xy.weight) < dist.(y)
    then
      (
        if verbose then Format.eprintf " error.@.";
        raise No_solution
      )
  in
  G.iter_edges_e check_edge sys.graph;

  if verbose then Format.eprintf " done.@.";

  (* Create the solution environment *)
  let add_binding id idx sol =
    let v =
      match obj with
      | Maximize -> dist.(idx)
      | Minimize -> Int.neg dist.(idx)
    in
    Utils.String_map.add id v sol
  in
  Utils.String_map.fold add_binding sys.env Utils.String_map.empty


let _ =
  if false
  then
    (
      let sys, init = make_system () in
      let x = add_variable sys "x" in
      let y = add_variable sys "y" in
      let z = add_variable sys "z" in
      let k = add_variable sys "k" in

      (*
        0 - x <= - 3
        0 - x <= 1
            x <= 7
        x - y <= 0
      *)
      (* add_constraint sys x init (Z.of_int (- 4)); *)
      (* add_constraint sys x init (Z.of_int 1); *)
      (* add_constraint sys init x (Z.of_int 4); *)
      (* add_constraint sys init x (Z.of_int 5); *)
      (* add_constraint sys y x Z.zero; *)

      (*
        0 - x <= -3
        y - x <= 0
        0 - y <= -3
        0 - z <= -1
        k - z <= 0
        0 - k <= -2
      *)

      add_constraint sys x init (Int.of_int (- 3));
      add_constraint sys y x Int.zero;
      add_constraint sys y init (Int.of_int (- 3));
      add_constraint sys z init (Int.of_int (- 1));
      add_constraint sys k z Int.zero;
      add_constraint sys k init (Int.of_int (- 2));


      (* add_constraint sys    x y (Z.of_int (- 1)); *)
      (* add_constraint sys    y x (Z.of_int     0); *)

      (* add_constraint sys x y (Z.of_int 1); *)
      (* add_constraint sys y z (Z.of_int 1); *)
      (* add_constraint sys x z (Z.of_int 2); *)

      try
        Format.eprintf "System:@\n%a@?" print_system sys;
        let sol = solve_system ~verbose:true ~obj:Maximize sys in
        Format.eprintf "Solution:@\n";
        Utils.String_map.iter
          (fun id s ->
            Format.eprintf "  %s = %a@." id Int.print s)
          sol;
      with No_solution ->
        Format.eprintf "No solution!@.";
    )
