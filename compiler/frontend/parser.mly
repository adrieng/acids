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

%token LPAREN RPAREN
%token BEGIN_PRAGMA END_PRAGMA

%token EOF

%start file
%type<Acids_parsetree.file> file

%%

with_loc(X):
 | x = X { Parser_utils.make_loc $startpos $endpos, x }

paren(X):
| LPAREN x = X RPAREN { x }

file:
| { make_file [] [] }
