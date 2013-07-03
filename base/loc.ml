(* Copyright (C) Adrien Guatto <adrien.guatto@laposte.net> 2012
 *
 * This file is part of nsched.
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

type t =
  {
    l_file : string;
    l_startpos : Lexing.position;
    l_endpos : Lexing.position;
  }

type 'a located =
  {
    l_contents : 'a;
    l_loc : t;
  }

let make_loc file sp ep = { l_file = file; l_startpos = sp; l_endpos = ep; }

let locate file sp ep x =
  {
    l_contents = x;
    l_loc = make_loc file sp ep;
  }

let locate_between file a b x =
  {
    l_contents = x.l_contents;
    l_loc = make_loc file a b;
  }

let dummy =
  { l_file = ""; l_startpos = Lexing.dummy_pos; l_endpos = Lexing.dummy_pos; }

let dummy_locate x = { l_contents = x; l_loc = dummy; }

let print_short fmt ({ l_startpos = b; l_endpos = e; } as loc) =
  if loc = dummy
  then Format.fprintf fmt "l. ?, c. ?"
  else
    let l = b.Lexing.pos_lnum in
    let fc = b.Lexing.pos_cnum - b.Lexing.pos_bol in
    let lc = e.Lexing.pos_cnum - b.Lexing.pos_bol in
    Format.fprintf fmt "l. %d, c. %d-%d" l fc lc

let print fmt { l_file = file; l_startpos = b; l_endpos = e; } =
  let l = b.Lexing.pos_lnum in
  let fc = b.Lexing.pos_cnum - b.Lexing.pos_bol in
  let lc = e.Lexing.pos_cnum - b.Lexing.pos_bol in
  Format.fprintf fmt "File \"%s\", line %d, characters %d-%d:@\n" file l fc lc

let report fmt loc =
  let file = loc.l_loc.l_file in
  let l1 = loc.l_loc.l_startpos.Lexing.pos_lnum in
  let l2 = loc.l_loc.l_endpos.Lexing.pos_lnum in
  let fc =
    loc.l_loc.l_startpos.Lexing.pos_cnum - loc.l_loc.l_startpos.Lexing.pos_bol
  in
  let lc =
    loc.l_loc.l_endpos.Lexing.pos_cnum - loc.l_loc.l_startpos.Lexing.pos_bol
  in
  let ls =
    if l1 <> l2 then Printf.sprintf "%d/%d" l1 l2 else string_of_int l1
  in
  Format.fprintf fmt "File \"%s\", line %s, characters %d-%d:@\n" file ls fc lc

let map f loc = { loc with l_contents = f loc.l_contents }

let fold f loc acc =
  let y, acc = f loc.l_contents acc in
  { loc with l_contents = y; }, acc

let with_loc loc x = { loc with l_contents = x; }

let view { l_contents = x; } = x

class ['a] iterator =
object
  method loc : t -> 'a -> t * 'a =
    fun loc acc -> loc, acc
end
