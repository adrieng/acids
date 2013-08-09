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

let print_constr_kind fmt k =
  let s =
    match k with
    | Equal -> "="
    | Adapt -> "<:"
  in
  Format.fprintf fmt "%s" s

module Make(S :
  sig
    type const
    val print_const : has_var : bool -> Format.formatter -> const -> unit
    val unit_const : const -> bool

    (** [right_simpify cst] if "c_x on cst = c_y on cst" <=> "c_x = c_y" *)
    val right_simplify : const -> bool

    val equivalent_const : const -> const -> bool
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
    | None -> S.print_const ~has_var:false fmt s.const
    | Some v ->
      Format.fprintf fmt "%s %a" v (S.print_const ~has_var:true) s.const

  let print_wconstr fmt wc =
    Format.fprintf fmt "@[%a %a@ %a (* %a *)@]"
      print_side wc.lhs
      print_constr_kind wc.kind
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

  (* Propagates equations c_x = c_y *)
  let simplify_redundant_equations sys =
    let ht = Hashtbl.create 17 in

    let find_class s =
      try Hashtbl.find ht s
      with Not_found ->
        let cl = Union_find.fresh s in
        Hashtbl.add ht s cl;
        cl
    in

    let check_constraint body c =
      match c.kind, c.lhs.var, c.rhs.var with
      | Equal, Some c_x, Some c_y ->
        if S.equivalent_const c.lhs.const c.rhs.const
          && S.right_simplify c.lhs.const
        then
          (
            let c_x_cl = find_class c_x in
            let c_y_cl = find_class c_y in
            if not (Union_find.equivalent c_x_cl c_y_cl)
            then Union_find.union c_x_cl c_y_cl;
            body
          )
        else
          c :: body
      | _ ->
        c :: body
    in

    let body = List.fold_left check_constraint [] sys.body in

    let propagate_side side =
      match side.var with
      | None -> side
      | Some c ->
        try
          let cl = find_class c in
          { side with var = Some (Union_find.find cl); }
        with Not_found ->
          side
    in

    let propagate_constraint cstr =
      {
        cstr with
          lhs = propagate_side cstr.lhs;
          rhs = propagate_side cstr.rhs;
      }
    in

    let pre_sol =
      let add c cl sol =
        let c' = Union_find.find cl in
        if c <> c' then Utils.Env.add c c' sol else sol
      in
      Hashtbl.fold add ht Utils.Env.empty
    in

    { sys with body = List.map propagate_constraint body; }, pre_sol
end
