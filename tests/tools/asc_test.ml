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

(* Configuration *)

let final_res = ref 0

let exec = ref "asc"

let additional_opts = ref "-ann full"

let regen = ref false

let verbose = ref false

let default_info_passes =
  [
    "data_typing";
    "interval_typing";
    "const_typing";
  ]

let passes = ref []

(* Utilities *)

let green s = "\027[32m" ^ s ^ "\027[0m"

let red s = "\027[31m" ^ s ^ "\027[0m"

let time_string () =
  let tm = Unix.localtime (Unix.time ()) in
  Printf.sprintf "%d-%d-%d_%d:%d:%d"
    tm.Unix.tm_mon
    tm.Unix.tm_mday
    tm.Unix.tm_year
    tm.Unix.tm_sec
    tm.Unix.tm_min
    tm.Unix.tm_hour

let log_file_name file_n =
  let base_n = Filename.chop_extension file_n in
  Printf.sprintf "%s-%s.log" base_n (time_string ())

let output_file_name_for_pass file_n pass =
  let base_n = Filename.chop_extension file_n in
  Printf.sprintf "%s.log.%s.as" base_n pass

let reference_file_name_for_pass file_n pass =
  let base_n = Filename.chop_extension file_n in
  Printf.sprintf "%s_%s.ref" base_n pass

let build_command file_n =
  let buff = Buffer.create 100 in
  Buffer.add_string buff (!exec ^ " " ^ !additional_opts);
  List.iter (fun s -> Buffer.add_string buff (" -s " ^ s)) !passes;
  Buffer.add_string buff (" " ^ file_n);
  Buffer.add_string buff (Printf.sprintf " >%s 2>&1" (log_file_name file_n));
  Buffer.contents buff

(* Checking code *)

let run_cmd mk_cmd out_file_n ref_file_n =
  let cmd = mk_cmd out_file_n ref_file_n in
  if !verbose then Printf.printf "%s\n" cmd;
  Sys.command cmd = 0

let regenerate_cmd out_file_n ref_file_n =
  Printf.sprintf "mv '%s' '%s'" out_file_n ref_file_n

let check_cmd out_file_n ref_file_n =
  (* Printf.sprintf "cmp -s '%s' '%s'" out_file_n ref_file_n *)
  Printf.sprintf "diff -wB '%s' '%s'>/dev/null 2>&1" out_file_n ref_file_n

let pass_action file_n pass_n =
  let output_file_n = output_file_name_for_pass file_n pass_n in
  let reference_file_n = reference_file_name_for_pass file_n pass_n in
  let ok =
    run_cmd
      (if !regen then regenerate_cmd else check_cmd)
      output_file_n
      reference_file_n
  in
  if !regen && not ok
  then
    (
      Printf.printf
        "%s: could not save %s\n"
        file_n
        (red (output_file_name_for_pass file_n pass_n));
      exit 4
    );
  if not !regen
  then
    (
      if not ok then final_res := 3;
      Printf.printf "%s: %s for pass %s\n"
        file_n
        (if ok then green "OK" else red "KO")
        pass_n
    );
  flush stdout

let process file_n =
  let cmd = build_command file_n in
  if !verbose then Printf.printf "%s\n" cmd;
  let ret = Sys.command cmd in
  if !verbose then Printf.printf "exit status %d\n" ret;
  if ret <> 0
  then
    (
      Printf.printf "%s: compilation %s\n" file_n (red "KO");
      final_res := 3;
    )
  else List.iter (pass_action file_n) !passes

(* Command-line parsing and main *)

let set r v = r := v

let add l s = l := s :: !l

let enable r () = set r true

let spec =
  let enable_default_passes () =
    List.iter (add passes) default_info_passes
  in
  Arg.align
    [
      "-regen", Arg.Unit (enable regen), " regenerate info files";
      "-exec", Arg.String (set exec), " compiler name";
      "-opts", Arg.String (set additional_opts), " additional options";
      "-add", Arg.String (add passes), " passes to check";
      "-def", Arg.Unit enable_default_passes, " check default passes";
      "-v", Arg.Unit (enable verbose), " be verbose";
    ]

let usage =
  "Usage: " ^ Sys.argv.(0) ^ " [options] FILES\n"
  ^ "Annotation checker for Acid Synchrone."

let files = ref []

let _ =
  Arg.parse spec (add files) usage;
  if !verbose then
    (
      Printf.printf "Doing passes: ";
      List.iter (Printf.printf " %s") !passes;
      Printf.printf "\n"
    );
  List.iter process !files;
  exit !final_res
