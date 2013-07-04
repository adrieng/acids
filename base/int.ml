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

include Nativeint

let ( + ) = add

let ( - ) = sub

let ( * ) = mul

let ( / ) = div

let ( mod ) = rem

let ( > ) = ( > )

let ( = ) i1 i2 = i1 = i2

let min = Pervasives.min

let max = Pervasives.max

let of_char c = of_string (String.make 1 c)

let print fmt i = Format.fprintf fmt "%nd" i

let equal = (=)

let compare = Pervasives.compare

let hash = Hashtbl.hash

module Env =
  Map.Make(
    struct
      type t = Nativeint.t
      let compare = Nativeint.compare
    end
  )

let rec gcd a b = if b = zero then a else gcd b (a mod b)

let lcm a b = (a * b) / gcd a b
