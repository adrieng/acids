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

{
  open Parser
  open Lexing

  exception Lexical_error of string Loc.located

  let lexical_error lexbuf err =
    let pos = lexbuf.lex_curr_p in
    let str = Printf.sprintf "unknown characters \"%s\"" err in
    let errloc =
      Loc.locate (Solver_utils.get_current_file_name ()) pos pos str
    in
    raise (Lexical_error errloc)

  let newline lexbuf =
    let pos = lexbuf.lex_curr_p in
    lexbuf.lex_curr_p <-
      { pos with
        pos_lnum = pos.pos_lnum + 1;
        pos_bol = pos.pos_cnum }

}

let alpha = ['a'-'z' 'A'-'Z']
let digit = ['0'-'9']
let ident = (alpha | '_' | ''' | digit)+

rule token = parse
| "(*" { comment 1 lexbuf }

| "(" { LPAREN }
| ")" { RPAREN }
| "{" { LBRACE }
| "}" { RBRACE }
| "^" { CARET }
| "," { COMMA }
| "=" { EQUAL }
| "<:" { ADAPT }

| "on" { ON }
| "with" { WITH }

| "true" { BOOL true }
| "false" { BOOL false }

| digit+ as i { INT (Int.of_string i) }
| ident+ as s { STRING s }

| ' '+ { token lexbuf }
| '\n' { newline lexbuf; token lexbuf }

| _ { lexical_error lexbuf (lexeme lexbuf) }

| eof { EOF }

and comment n = parse
| "*)" { if n = 1 then token lexbuf else comment (n - 1) lexbuf }
| "(*" { comment (n + 1) lexbuf }
| '\n' { newline lexbuf; comment n lexbuf }
| _ { comment n lexbuf }
| eof { lexical_error lexbuf "unterminated comment" }
