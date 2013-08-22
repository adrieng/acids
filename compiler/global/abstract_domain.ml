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

module type Predomain =
sig
  type t

  val print : Format.formatter -> t -> unit

  val le : t -> t -> bool

  val join : t -> t -> t

  val meet : t -> t -> t
end

module type S =
sig
  include Predomain

  val bot : t

  val abs_const : Ast_misc.const -> t

  val abs_word : Ast_misc.static_pword -> t
end

module type Elem =
sig
  include S
  val elem : t
end

type 'a free =
  | Top
  | Bot
  | Elem of 'a

module Free(P : Predomain) =
struct
  type t = P.t free

  let bot = Bot

  let print fmt e =
    match e with
    | Top -> Format.fprintf fmt "T"
    | Bot -> Format.fprintf fmt "B"
    | Elem x -> P.print fmt x

  let join x y =
    match x, y with
    | Top, _ | _, Top -> Top
    | Bot, x | x, Bot -> x
    | Elem x, Elem y -> Elem (P.join x y)

  let meet x y =
    match x, y with
    | Bot, _ | _, Bot -> Bot
    | Top, x | x, Top -> x
    | Elem x, Elem y -> Elem (P.meet x y)

  let le x y =
    match x, y with
    | Bot, _ | _, Top -> true
    | _, Bot | Top, _ -> false
    | Elem x, Elem y -> P.le x y
end

module Interval : S with type t = Interval.t free =
struct
  module M = Free(Interval)
  include M

  let abs_const _ = Top

  let abs_word _ = Top
end
