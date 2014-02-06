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

module M =
  (
    (struct
      type t =
        {
          num : Int.t;
          den : Int.t;
        }

      let make num den =
        let open Int in
        let k =
          let k = lcm num den in
          if k <> zero then k else one
        in
        { num = num / k; den = den / k; }
     end) :
      (sig
        type t = private { num : Int.t; den : Int.t; }
        val make : Int.t -> Int.t -> t
       end)
  )

include M

let ( = ) = ( = )
