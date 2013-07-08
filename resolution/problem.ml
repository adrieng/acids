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

type var = string

module Make(S :
  sig
    type const
    val print_const : Format.formatter -> const -> unit
  end) =
struct
  type side =
    {
      var : var option;
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
      options : Resolution_options.env;
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
    Format.fprintf fmt "@[{ @[<v>%a@] }"
      (Utils.print_list_r print_wconstr ";") sys.body;
    if not (Resolution_options.is_empty sys.options)
    then
      Format.fprintf fmt "@ with @[%a@]"
        Resolution_options.print_env sys.options;
    Format.fprintf fmt "@]"

  let lower_equality_constraints sys =
    let lower_constr c sys =
      match c.kind with
      | Equal ->
        let left = { c with kind = Adapt; } in
        let right = { loc = c.loc; kind = Adapt; lhs = c.rhs; rhs = c.lhs; } in
        left :: right :: sys
      | Adapt -> c :: sys
    in
    {
      sys with
        body = List.fold_right lower_constr sys.body [];
    }
end
