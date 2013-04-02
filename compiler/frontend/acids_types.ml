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

module Stream_type =
  MakeVar(
    struct
      type ('a, 'b) t =
        | St_var of 'a
        | St_on of ('a, 'b) t * 'b clock_exp

      let rec print print_var fmt t =
        match t with
        | St_var v -> print_var fmt v
        | St_on (st, ce) ->
          Format.fprintf fmt
            "@[%a on %a@]"
            (print print_var) st
            print_clock_exp ce
    end)

type 'a stream_type = 'a Stream_type.t

module Clock_type =
  MakeVar(
    struct
      type ('a, 'b) t =
        | Ct_var of 'a
        | Ct_tuple of ('a, 'b) t list
        | Ct_stream_type of 'b stream_type
    end
  )

type 'a clock_type = 'a Clock_type.t
