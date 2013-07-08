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

let check_by_default = ref true

let current_file_name = ref ""

let set_current_file_name s = current_file_name := s

let get_current_file_name () = !current_file_name

let make_loc start stop = Loc.make_loc (get_current_file_name ()) start stop

exception Parse_error of Loc.t

let parse_error start stop = raise (Parse_error (make_loc start stop))
