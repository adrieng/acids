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

module Make(S : sig end) =
struct
  type word = (Int.t, Int.t) Tree_word.t

  type side =
    {
      var : string option;
      const : word list;
    }

  type constr_kind = Equal | Adapt

  type constr =
    {
      loc : Loc.t;
      lhs : side;
      kind : constr_kind;
      rhs : side;
    }

  type system =
    {
      body : constr list;
    }

  let print_words fmt w =
    Utils.print_list_r
      (Tree_word.print_upword Int.print Int.print)
      "on "
      fmt
      w

  let print_side fmt s =
    match s.var with
    | None -> print_words fmt s.const
    | Some v ->
      Format.fprintf fmt "%s on @[%a@]"
        v
        print_words s.const

  let print_kind fmt k =
    let s =
      match k with
      | Equal -> "="
      | Adapt -> "<:"
    in
    Format.fprintf fmt "%s" s

  let print_wconstr fmt wc =
    Format.fprintf fmt "@[%a %a@ %a (* %a *)@]"
      print_side wc.lhs
      print_kind wc.kind
      print_side wc.rhs
      Loc.print wc.loc

  let print_system fmt sys =
    Format.fprintf fmt "{ @[<v>%a@] }"
      (Utils.print_list_r print_wconstr ";") sys.body

  module Solution =
  struct
    type t = word Utils.String_map.t
    let get m x = try Some (Utils.String_map.find x m) with Not_found -> None
  end

  type error =
  | Rate_inconsistency
  | Precedence_inconsistency

  exception Could_not_solve of error

  let solve _ = assert false
end
