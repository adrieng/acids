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

type constr_kind = Equal | Adapt

module Make(S :
  sig
    type const
    val print_const : Format.formatter -> const -> unit
  end) =
struct
  type side =
    {
      var : string option;
      const : S.const;
    }

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

  let print_side fmt s =
    match s.var with
    | None -> S.print_const fmt s.const
    | Some v ->
      Format.fprintf fmt "%s on @[%a@]"
        v
        S.print_const s.const

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
      Loc.print_short wc.loc

  let print_system fmt sys =
    Format.fprintf fmt "{ @[<v>%a@] }"
      (Utils.print_list_r print_wconstr ";") sys.body

end

module Pp =
  Make
    (struct
      type const = Pword.pword list
      let print_const = Utils.print_list_r Pword.print_pword " on"
     end)

open Pp

let reduce_on_pp sys =
  let reduce_on_side side =
    { side with const = [Utils.fold_left_1 Pword.on side.const]; }
  in

  let reduce_on_constr constr =
    {
      constr with
        lhs = reduce_on_side constr.lhs;
        rhs = reduce_on_side constr.rhs;
    }
  in

  { body = List.map reduce_on_constr sys.body; }
