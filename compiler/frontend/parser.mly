/* Copyright (C) Adrien Guatto <adrien.guatto@laposte.net> 2013
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
 */

%{
 let make_concat l =
   match l with
   | [] -> invalid_arg "make_concat: empty list"
   | [x] -> x
   | _ :: _ -> Ast_misc.Concat l

  let make_ce_pword (u, v) =
    {
      Acids_parsetree.cep_prefix = u;
      Acids_parsetree.cep_period = v;
    }

  let make_located make (x, loc) = make x loc

  let make_clock_exp ced loc =
    {
      Acids_parsetree.ce_desc = ced;
      Acids_parsetree.ce_loc = loc;
      Acids_parsetree.ce_info = ();
    }

 let make_exp ed loc =
   {
     Acids_parsetree.e_desc = ed;
     Acids_parsetree.e_loc = loc;
     Acids_parsetree.e_info = ();
   }

 let make_pat pd loc =
   {
     Acids_parsetree.p_desc = pd;
     Acids_parsetree.p_loc = loc;
     Acids_parsetree.p_info = ();
   }

 let make_eq (p, e) loc =
   {
     Acids_parsetree.eq_lhs = p;
     Acids_parsetree.eq_rhs = e;
     Acids_parsetree.eq_loc = loc;
     Acids_parsetree.eq_info = ();
   }

 let make_block eqs loc =
   {
     Acids_parsetree.b_body = eqs;
     Acids_parsetree.b_loc = loc;
     Acids_parsetree.b_info = ();
   }

 let make_node (n, p, e, pr) loc =
   {
     Acids_parsetree.n_name = n;
     Acids_parsetree.n_input = p;
     Acids_parsetree.n_body = e;
     Acids_parsetree.n_pragma = pr;
     Acids_parsetree.n_loc = loc;
     Acids_parsetree.n_env = Names.Env.empty;
     Acids_parsetree.n_info = ();
   }

  let make_file imports body =
    {
      Acids_parsetree.f_name = Initial.get_current_module ();
      Acids_parsetree.f_imports =
        if !Compiler_options.no_pervasives
        then imports
        else "Pervasives" :: imports;
      Acids_parsetree.f_initial_env = Names.Env.empty;
      Acids_parsetree.f_nodes = body;
    }
%}

/* Punctuation */

%token LPAREN RPAREN CARET LBRACE RBRACE
%token EQUAL
%token COMMA

/* Keywords */

%token VALOF LET NODE OPEN FST SND WHERE REC AND

/* Identifiers and constants */

%token<string> IDENT
%token<string> UIDENT

%token<bool> BOOL
%token<Int.t> INT
%token<float> FLOAT

/* Misc */

%token BEGIN_PRAGMA END_PRAGMA

%token EOF

/* Disambiguation tokens */

/* Precedence and associativity */

%left WHERE
%nonassoc FST SND

/* Start of the grammar */

%start file
%type<Acids_parsetree.file> file

%%

with_loc(X):
 | x = X { x, Parser_utils.make_loc $startpos $endpos }

paren(X):
| LPAREN x = X RPAREN { x }

simple_ptree(X, Y):
| X { Ast_misc.Leaf $1 }
| simple_ptree(X, Y) CARET Y { Ast_misc.Power ($1, $3) }
| LBRACE ptree(X, Y) RBRACE { $2 }

ptree(X, Y):
| nonempty_list(simple_ptree(X, Y)) { make_concat $1 }

upword(X, Y):
| v = paren(ptree(X, Y)) { (Ast_misc.Concat [], v) }
| u = ptree(X, Y) v = paren(ptree(X, Y)) { (u, v) }

nodename:
| UIDENT { Initial.make_longname $1 }

//////////////////////////////////////////////////////////////////

const:
| BOOL { Ast_misc.Cbool $1 }
| INT { Ast_misc.Cint $1 }
| FLOAT { Ast_misc.Cfloat $1 }

clock_exp_desc:
| IDENT { Acids_parsetree.Ce_var $1 }
| upword(trivial_exp, trivial_exp)
    { Acids_parsetree.Ce_pword (make_ce_pword $1) }

clock_exp:
| with_loc(clock_exp_desc) { make_located make_clock_exp $1 }

trivial_exp_desc:
| const { Acids_parsetree.E_const $1 }
| IDENT { Acids_parsetree.E_var $1 }

trivial_exp:
| with_loc(trivial_exp_desc) { make_located make_exp $1 }

simple_exp_desc:
| const { Acids_parsetree.E_const $1 }
| IDENT { Acids_parsetree.E_var $1 }
| paren(exp_desc) { $1 }

simple_exp:
| with_loc(simple_exp_desc) { make_located make_exp $1 }

exp_desc:
| trivial_exp_desc { $1 }

| FST exp { Acids_parsetree.E_fst $2 }
| SND exp { Acids_parsetree.E_snd $2 }
| paren(separated_list(COMMA, exp)) { Acids_parsetree.E_tuple $1 }

| exp WHERE REC block { Acids_parsetree.E_where ($1, $4) }

| VALOF clock_exp { Acids_parsetree.E_valof $2 }

exp:
| with_loc(exp_desc) { make_located make_exp $1 }

eq_desc:
| p = pat EQUAL e = exp { (p, e) }

eq:
| with_loc(eq_desc) { make_located make_eq $1 }

block:
| with_loc(separated_nonempty_list(AND, eq)) { make_located make_block $1 }

pat_desc:
| IDENT { Acids_parsetree.P_var $1 }

pat:
| with_loc(pat_desc) { make_located make_pat $1 }

pragma:
| { None }
| BEGIN_PRAGMA END_PRAGMA { Some () }

node_desc:
| pr = pragma LET NODE n = nodename p = pat EQUAL e = exp { (n, p, e, pr) }

node:
| with_loc(node_desc) { make_located make_node $1 }

import:
| OPEN UIDENT { $2 }

file:
| imports = list(import) nodes = list(node) EOF { make_file imports nodes }
