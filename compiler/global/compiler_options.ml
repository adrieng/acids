(* Copyright (C) Adrien Guatto <adrien.guatto@laposte.net> 2012
 *
 * This file is part of nsched.
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

let debug = ref false

let check_transforms = ref false

let print_full_info = ref false

let print_data_info = ref false

let print_static_info = ref false

let print_spec_info = ref false

let print_clock_info = ref false

let print_causality_info = ref false

let print_buffer_info = ref false

let info_list =
  [
    "full", print_full_info;
    "data", print_data_info;
    "static", print_static_info;
    "spec", print_spec_info;
    "clock", print_clock_info;
    "caus", print_causality_info;
    "buff", print_buffer_info;
  ]

let set_info s = List.assoc s info_list := true

let serialize_transforms = (ref [] : string list ref)

let stop_after = (ref None : string option ref)

let no_pervasives = ref false

let optimize = ref true

let print_interface = ref false

let search_path =
  ref
    [
      Filename.current_dir_name;
      Filename.concat (Filename.dirname Sys.argv.(0)) Compiler.lib;
    ]

let resolution_options =
  [
    "ilp",
    ref (Resolution_options.String "glpk"),
    ["glpk"; "gurobi"],
    " Choice of ILP solver (default: glpk)";

    "max_burst",
    ref (Resolution_options.Int Int.one),
    [],
    " Maximum inferred burst (default: 1)";

    "profile",
    ref (Resolution_options.Bool false),
    [],
    " Gather timing information";
  ]

let make_arg_option_of_resolution_option (key, value_ref, choices, msg) =
  let open Resolution_options in
  let key, arg =
    match !value_ref with
    | String _ ->
      key,
      if choices <> []
      then Arg.Symbol (choices, (fun s -> value_ref := String s))
      else Arg.String (fun s -> value_ref := String s)
    | Int _ ->
      key,
      Arg.Int (fun i -> value_ref := Int (Int.of_int i))
    | Bool false ->
      key,
      Arg.Unit (fun () -> value_ref := Bool true)
    | Bool true ->
      "no" ^ key,
      Arg.Unit (fun () -> value_ref := Bool false)
  in
  "-" ^ key, arg, msg

let set r x () = r := x

let add lr x = set lr (x :: !lr) ()

let set_once r x =
  match !r with
  | None -> r := Some x
  | Some _ -> failwith "Could not set this option twice"

type default =
  | Enabled of bool ref
  | Disabled of bool ref

let ref_of_ctx_option def =
  match def with
  | Enabled r -> r
  | Disabled r -> r

let ctx_options =
  [
    "debug", Disabled debug, "Enable debugging features";
    "check", Disabled check_transforms, "Check transformation invariants";
    "O", Enabled optimize, "Enable optimizations";
    "i", Disabled print_interface, "Print signatures";
  ]

let options =
  let make (id, def, msg) =
    let switch =
      match def with
      | Enabled r -> Arg.Clear r
      | Disabled r -> Arg.Set r
    in
    "-" ^ id, switch, " " ^ msg
  in

  Arg.align
    (
      List.map make ctx_options
      @ List.map make_arg_option_of_resolution_option resolution_options
      @
        [
          "-nopervasives",
          Arg.Unit (set no_pervasives true),
          " Do not load the Pervasives module";

          "-ann",
          Arg.Symbol (List.map fst info_list, set_info),
          " Print annotations";

          "-s",
          Arg.String (add serialize_transforms),
          " Serialize the output of the given transform";

          "-stop",
          Arg.String (set_once stop_after),
          " Stop after the given transform";

          "-I",
          Arg.String (fun s -> search_path := s :: !search_path),
          " Add the given directory to search path";
        ]
    )

let usage = Sys.argv.(0) ^ ": [options] files"

let has_something_to_print =
  (* we cache the result, since it is called after arguments have been set *)
  let r = ref None in
  fun () ->
    match !r with
    | None ->
      let res = List.fold_left (||) false (List.map (fun (_, r) -> !r) info_list) in
      r := Some res;
      res
    | Some res ->
      res
