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

(*****************************************************************************)
(* Error handling *)

let error_is_internal exn =
  match exn with
  | Failure("lexing: empty token")
  | Parsing_pass.Could_not_open _
  | Lexer.Lexical_error _
  | Parser_utils.Parse_error _
  | Scoping.Scoping_error _
  | Interface.Interface_error _
  | Data_typing.Typing_error _
  | Const_typing.Typing_error _
  | Const_simpl.Simplification_error _
  | Spec_annot.Annotation_error _
  | Clocking.Clocking_error _
  | Clocking_resolution.Resolution_error _
  | Causality.Causality_error _
  | Scheduling.Scheduling_error _
  | Output.Output_error _
    ->
    false
  | _
    ->
    true

let print_error _ fmt exn =
  match exn with
  | Failure("lexing: empty token") ->
    Format.fprintf fmt "Lexical error"
  | Parsing_pass.Could_not_open filen ->
    Format.fprintf fmt "Cannot find file %s" filen
  | Lexer.Lexical_error reason ->
    Loc.report fmt reason;
    Format.fprintf fmt "Lexical error: %s" (Loc.view reason)
  | Parser_utils.Parse_error reason ->
    Loc.print fmt reason;
    Format.fprintf fmt "Syntax error"
  | Scoping.Scoping_error err ->
    Scoping.print_error fmt err
  | Interface.Interface_error err ->
    Interface.print_error fmt err
  | Data_typing.Typing_error err ->
    Data_typing.print_error fmt err
  | Const_typing.Typing_error err ->
    Const_typing.print_error fmt err
  | Const_simpl.Simplification_error err ->
    Const_simpl.print_error fmt err
  | Spec_annot.Annotation_error err ->
    Spec_annot.print_error fmt err
  | Clocking.Clocking_error err ->
    Clocking.print_error fmt err
  | Clocking_resolution.Resolution_error err ->
    Clocking_resolution.print_error fmt err
  | Causality.Causality_error err ->
    Causality.print_error fmt err
  | Scheduling.Scheduling_error err ->
    Scheduling.print_error fmt err
  | Output.Output_error err ->
    Output.print_error fmt err
  | exn ->
    Format.fprintf fmt "Unknown error (%s)" (Printexc.to_string exn)

(*****************************************************************************)
(* Compilation flow *)

let flow =
  let open Pass_manager in
  (* Parsing and scoping *)
  Parsing_pass.pass
  +>+ Scoping.pass
  (* Type systems and const inlining *)
  +>+ Data_typing.pass
  +>+ Const_typing.pass
  +>+ Const_simpl.pass
  +>+ Spec_annot.pass
  +>+ Clocking.pass
  +>+ Causality.pass
  +>+ Save_interface.pass
  +>+ Lower.pass
  (* Middle-end *)
  +>+ Nir_of_acids.pass
  +>+ Clock_slicing.pass
  +>+ Block_formation.pass
  +>+ Clock_exp_naming.pass
  +>+ Buffer_lowering.pass
  +>+ Scheduling.pass
  (* Back-end *)
  +>+ Obc_of_nir.pass
  +>+ Output.pass

(*****************************************************************************)
(* File handling *)

let handle_file filen =
  let ctx =
    Pass_manager.make_ctx
      ~serialize_transforms:!Compiler_options.serialize_transforms
      ~stop_after:!Compiler_options.stop_after
      ~current_file:filen
      ~error_is_internal:error_is_internal
      ~print_error:print_error
      ()
  in

  let ctx =
    let add_attr ctx (attr, def, _) =
      Pass_manager.ctx_set_attr
        ctx
        (attr, !(Compiler_options.ref_of_ctx_option def))
    in
    List.fold_left add_attr ctx Compiler_options.ctx_options
  in

  let b = Pass_manager.eval_to_completion flow ctx filen in
  exit (if b then 0 else 1)

let files = ref []

let _ =
  try
    Arg.parse
      (Compiler_options.options ())
      (fun s -> files := s :: !files)
      Compiler_options.usage;
    files := List.rev !files;
    List.iter handle_file !files
  with
  | Compiler.Internal_error reason ->
    Format.eprintf "Internal error: %s@." reason;
    exit 2
  | Compiler_options.Duplicate_option opt ->
    Format.eprintf "Cannot set command-line option \"%s\" twice@." opt;
    exit 1
