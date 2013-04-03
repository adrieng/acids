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

 let make_node (n, p, e) loc =
   {
     Acids_parsetree.n_name = n;
     Acids_parsetree.n_input = p;
     Acids_parsetree.n_body = e;
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

%token LPAREN RPAREN CARET
%token EQUAL

/* Keywords */

%token VALOF LET NODE OPEN

/* Identifiers and constants */

%token<string> IDENT
%token<string> UIDENT

/* MISC */

%token BEGIN_PRAGMA END_PRAGMA

%token EOF

%start file
%type<Acids_parsetree.file> file

%%

with_loc(X):
 | x = X { x, Parser_utils.make_loc $startpos $endpos }

paren(X):
| LPAREN x = X RPAREN { x }

ptree(X, Y):
| X { Ast_misc.Leaf $1 }
| list(ptree(X, Y)) { Ast_misc.Concat $1 }
| X CARET Y { Ast_misc.Power ($1, $3) }

upword(X, Y):
| u = list(ptree(X, Y)) LPAREN v = nonempty_list(ptree(X, Y)) RPAREN { (u, v) }

nodename:
| UIDENT { Initial.make_longname $1 }

//////////////////////////////////////////////////////////////////

clock_exp_desc:
| IDENT { Acids_parsetree.Ce_var $1 }

clock_exp:
| with_loc(clock_exp_desc) { make_located make_clock_exp $1 }

exp_desc:
| VALOF clock_exp { Acids_parsetree.E_valof $2 }

exp:
| with_loc(exp_desc) { make_located make_exp $1 }

pat_desc:
| IDENT { Acids_parsetree.P_var $1 }

pat:
| with_loc(pat_desc) { make_located make_pat $1 }

node_desc:
| LET NODE n = nodename p = pat EQUAL e = exp { (n, p, e) }

node:
| with_loc(node_desc) { make_located make_node $1 }

import:
| OPEN UIDENT { $2 }

file:
| imports = list(import) nodes = list(node) EOF { make_file imports nodes }
