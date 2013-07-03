open Ocamlbuild_plugin
open Ocamlbuild_plugin.Options

let make_menhir_options ocamlc_opts =
  (S [A"--explain"; A"--table"])
      (* A "--ocamlc"; Quote (S [!Options.ocamlc; (\* hack: use zarith *\) *)
      (*                         Sh "-package zarith"; *)
      (*                         S ocamlc_opts])]) *)

let df = function
  | After_rules ->
    (* Ask Menhir to compile our stuff with proper error messages *)
    flag
      ["ocaml"; "parser" ; "menhir"]
      (make_menhir_options []);

    (* Fatal warnings for non-exhaustive pattern matchings and useless partial
       applications *)
    flag
      ["ocaml"; "compile" ]
      (S[A "-w"; A "Ae"; A "-warn-error"; A "PUF"; A "-w"; A "-9"]);

    (* Menhir generates a useless rec flag, disable warning for this file
       (I'm unhappy about this). *)
    flag
      ["ocaml"; "compile"; "parser" ]
      (S [A "-w"; A "-39"]);

    ocaml_lib "base/asc_base";
    ocaml_lib "resolution/asc_resolution";

  | _ -> ()

let _ = dispatch df
