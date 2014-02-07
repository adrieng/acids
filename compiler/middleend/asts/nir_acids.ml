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
  type node_name = Names.longname
  let print_node_name = Names.print_longname

  type clock_var =
  | Cv_base
  | Cv_clock of int
  let print_clock_var fmt cv =
    match cv with
    | Cv_base -> Format.fprintf fmt "base"
    | Cv_clock i -> Format.fprintf fmt "'a%d" i
end

module M = Nir.Make(Info)
include M

module P = Nir_printer.Make(M)
include P
