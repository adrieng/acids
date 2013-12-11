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

exception Parse_error of Loc.t

let make_loc startp endp =
  Loc.make_loc (Initial.get_current_file_name ()) startp endp

let parse_error startp endp =
  raise (Parse_error (make_loc startp endp))

let plus = "+"
let minus = "-"
let times = "*"
let div = "/"
let plusf = "+."
let minusf = "-."
let timesf = "*."
let divf = "/."

let lt = "<"
let gt = ">"
let le = "<="
let ge = ">="

let eq = "="
