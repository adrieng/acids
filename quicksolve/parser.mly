%{
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

  let make_side s w_l =
    {
      Resolution.var = s;
      Resolution.const = w_l;
    }

 let make_constr (loc, (lhs, kind, rhs)) =
   {
     Resolution.loc = loc;
     Resolution.lhs = lhs;
     Resolution.kind = kind;
     Resolution.rhs = rhs;
   }

 let make_system sys =
   {
     Resolution.body = sys;
   }

 let make_pword ?(u = Tree_word.Concat []) v =
   { Tree_word.u = u; Tree_word.v = v; }
%}

%start system
%type <Resolution.system> system

%start file
%type <Resolution.system list> file


%token LPAREN RPAREN LBRACE RBRACE CARET
%token ON

%token<string> STRING
%token<Int.t> INT
%token<Problem.constr_kind> KIND

%token EOF

%%

with_loc(X):
| x = X { Solver_utils.make_loc $startpos $endpos, x }

simple_ptree(X, Y):
| x = X { Ast_misc.Leaf x }
| t = simple_ptree(X, Y) CARET y = Y { Ast_misc.Power (t, y) }
| LBRACE t = ptree(X, Y) RBRACE { t }

%inline ptree(X, Y):
| pt = nonempty_list(simple_ptree(X, Y)) { make_concat pt }

simple_tree:
| b = INT { Tree_word.Leaf b }
| w = simple_tree CARET k = INT { Tree_word.Power (w, k) }
| LBRACE w = tree RBRACE { w }

tree:
| w_l = nonempty_list(simple_tree) { Tree_word.Concat w_l }

word:
| LPAREN v = tree RPAREN { make_pword v }
| u = tree LPAREN v = tree RPAREN { make_pword ~u v }

const:
| w_l = separated_nonempty_list(ON, word) { w_l }

side:
| s = STRING ON w_l = const { make_side (Some s) w_l }

constr_desc:
| lhs = side kind = KIND rhs = side { lhs, kind, rhs }

constr:
| with_loc(constr_desc) { make_constr $1 }

system:
| LBRACE c_l = nonempty_list(constr) RBRACE { make_system c_l }

file:
| l = list(system) EOF { l }