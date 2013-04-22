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

exception Could_not_open of string

let could_not_open filen = raise (Could_not_open filen)

let parse =
  let parse_file ctx filen =
    Initial.set_current_file_name filen;
    let ic =
      try open_in filen
      with Sys_error _ -> could_not_open filen
    in
    let lexbuf = Lexing.from_channel ic in
    let ptree = Parser.source_file Lexer.token lexbuf in
    close_in ic;
    ctx, ptree
  in

  let open Pass_manager in
  P_transform
    (Frontend_utils.make_transform
       ~print_out:Acids_parsetree.print_file
       "parsing"
       parse_file)
