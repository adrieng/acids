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

module Info =
struct
  type node_name = Names.longname * int
  let print_node_name fmt (ln, i) =
    Format.fprintf fmt "%a_st%d"
      Names.print_longname ln
      i
  let original_name (ln, _) = ln

  type clock_var = Cv_base
  let print_clock_var fmt Cv_base = Format.fprintf fmt "base"
end

module M = Nir.Make(Info)
include M

module P = Nir_printer.Make(M)
include P

module U = Nir_utils.Make(M)
include U
