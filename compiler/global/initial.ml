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

let set_current_file_name, get_current_file_name =
  let current_file_name = ref "" in
  (fun s -> current_file_name := s),
  (fun () ->
    if !current_file_name = ""
    then Compiler.internal_error "current file not set";
    !current_file_name)

let make_longname ?modn shortn =
  let modn = match modn with
    | None -> Names.LocalModule
    | Some modn -> Names.Module modn
  in
  assert (shortn <> "");
  Names.make_longname modn shortn
