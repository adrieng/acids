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

  (**********************************************************************)

  let keywords =
    [
      "fst", FST;
      "snd", SND;
      "let", LET;
      "node", NODE;
      "const", CONST;
      "pword", PWORD;
      "open", OPEN;
      "fby", FBY;
      "if", IF;
      "then", THEN;
      "else", ELSE;
      "where", WHERE;
      "rec", REC;
      "and", AND;
      "when", WHEN;
      "merge", MERGE;
      "split", SPLIT;
      "on", ON;
      "base", BASE;
      "dom", DOM false;
      "pardom", DOM true;
      "buffer", BUFFER;
      "valof", VALOF;
      "val", VAL;
      "in", IN;
      "is", IS;
      "with", WITH;
      "end", END;
      "type", TYPE;
      "by", BY;
      "cond", COND;
      "boxed", BOXED;
      "unspec", UNSPEC;
      "bool", BOOL_TY;
      "int", INT_TY;
      "float", FLOAT_TY;
      "N", NONCONST_TY;
      "C", CONST_TY;
    ]

  let token_of_keyword =
    let ht = Hashtbl.create 17 in
    List.iter (fun (k, v) -> Hashtbl.add ht k v) keywords;
    fun kw -> Hashtbl.find ht kw

  (**********************************************************************)

  let int_list_of_string w =
    let rec add i l =
      if i >= String.length w
      then List.rev l
      else add (i + 1) (Int.of_string (String.make 1 w.[i]) :: l)
    in
    add 0 []
}

let keyword =
    "fst"
  | "snd"
  | "let"
  | "node"
  | "const"
  | "pword"
  | "open"
  | "fby"
  | "if"
  | "then"
  | "else"
  | "where"
  | "rec"
  | "and"
  | "when"
  | "merge"
  | "split"
  | "on"
  | "base"
  | "dom"
  | "pardom"
  | "buffer"
  | "valof"
  | "val"
  | "in"
  | "is"
  | "with"
  | "end"
  | "type"
  | "by"
  | "cond"
  | "unspec"
  | "bool"
  | "int"
  | "float"
  | "D"
  | "S"

let alpha = ['a'-'z' 'A'-'Z']
let digit = ['0'-'9']
let int = digit+
let posint = ['1'-'9'] digit*
let exponent = ('e' | 'E') ('+' | '-')? digit+
let float = digit+ '.' digit* exponent?
          | digit* '.'digit+ exponent?
          | digit+ exponent
let ident = alpha (alpha | '_' | ''' | digit)*
let lident = ['a'-'z'] (alpha | '_' | ''' | digit)*
let uident = ['A'-'Z'] (alpha | '_' | ''' | digit)*

let op = ['+' '-' '*' '-' '/' '^' '%' '#' '.']+

rule token = parse
  | "(*" { comment 0 lexbuf; token lexbuf }

  | "(" { LPAREN }
  | ")" { RPAREN }
  | "^" { CARET }
  | "{" { LBRACE }
  | "}" { RBRACE }
  | "[" { LBRACKET }
  | "]" { RBRACKET }
  | "=" { EQUAL }
  | "," { COMMA }
  | "." { DOT }
  | "::" { DCOLON }
  | ":" { COLON }

  | "<=" { LE }
  | ">=" { GE }
  | "<" { LT }
  | ">" { GT }

  | "->" { ARROW }
  | "|" { PIPE }

  | "true" { BOOL true }
  | "false" { BOOL false }
  | int as i { INT (Int.of_string i) }
  | float as f { FLOAT (float_of_string f) }

  | keyword as kw { token_of_keyword kw }

  | '\''(digit+ as s)'\'' { FWORD (int_list_of_string s) }

  | "'a"(posint as i) { STVAR (int_of_string i) }
  | "'a"              { STVAR 0 }
  | "'b"(posint as i) { CTVAR (int_of_string i) }
  | "'b"              { CTVAR 0 }
  | "'x"(posint as i) { TYVAR (int_of_string i) }
  | "'x"              { TYVAR 0 }
  | "'c"(posint as i) { CONSTVAR (int_of_string i) }
  | "'c"              { CONSTVAR 0 }

  | '@' (ident as s) { PRAGMAKEY s }
  | lident as s { IDENT s }
  | uident as s { UIDENT s }

  | "+" { PLUS }
  | "-" { MINUS }
  | "*" { TIMES }
  | "/" { DIV }

  | op as s { OP s }

  | ' '+ { token lexbuf }
  | '\n' { newline lexbuf; token lexbuf }

  | _ { lexical_error lexbuf ("unknown character: " ^ lexeme lexbuf) }

  | eof { EOF }

and comment cpt = parse
  | "*)" { if cpt = 0 then () else comment (cpt - 1) lexbuf }
  | "(*" { comment (cpt + 1) lexbuf }
  | '\n' { newline lexbuf; comment cpt lexbuf }
  | _ { comment cpt lexbuf }
  | eof { lexical_error lexbuf "unterminated comment" }
