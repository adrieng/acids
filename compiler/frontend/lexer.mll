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
    let errloc = Loc.locate (Initial.get_current_file_name ()) pos pos err in
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
let int = digit+
let exponent = ('e' | 'E') ('+' | '-')? digit+
let float = digit+ '.' digit* exponent?
          | digit* '.'digit+ exponent?
          | digit+ exponent
let lident = ['a'-'z'] (alpha | '_' | ''' | digit)*
let uident = ['A'-'Z'] (alpha | '_' | ''' | digit)*

let op = ['+' '-' '*' '-' '/' '^' '%' '#']+

rule token = parse
| "(*-" { pragma lexbuf }
| "(*" { comment lexbuf }

| "(" { LPAREN }
| ")" { RPAREN }
| "^" { CARET }
| "{" { LBRACE }
| "}" { RBRACE }
| "{" { LCHEVRON }
| "}" { RCHEVRON }
| "=" { EQUAL }
| "," { COMMA }
| "." { DOT }
| "::" { DCOLON }

| "true" { BOOL true }
| "false" { BOOL false }
| int as i { INT (Int.of_string i) }
| float as f { FLOAT (float_of_string f) }

| "fst" { FST }
| "snd" { SND }

| "let" { LET }
| "node" { NODE }
| "open" { OPEN }

| "where" { WHERE }
| "rec" { REC }
| "and" { AND }

| "when" { WHEN }
| "merge" { MERGE }
| "split" { SPLIT }

| "on" { ON }
| "base" { BASE }

| "dom" { DOM false }
| "pardom" { DOM true }

| "$" { word lexbuf }

| "'s"(int as i) { STVAR (int_of_string i) }

| lident as s { IDENT s }
| uident as s { UIDENT s }

| op as s { OP s }

| ' '+ { token lexbuf }
| '\n' { newline lexbuf; token lexbuf }

| _ { lexical_error lexbuf ("unknown character: " ^ lexeme lexbuf) }

| eof { EOF }

and pragma = parse
| "pragma" { BEGIN_PRAGMA }
| "-*)" { END_PRAGMA }

and comment = parse
| "*)" { token lexbuf }
| "(*" { comment lexbuf }
| '\n' { newline lexbuf; comment lexbuf }
| _ { comment lexbuf }
| eof { lexical_error lexbuf "unterminated comment" }

and word = parse
| ['0'-'9'] as c { INT (Int.of_char c) }
| '\n' { newline lexbuf; word lexbuf }
| eof { lexical_error lexbuf "unterminated word" }
| _ { token lexbuf }
