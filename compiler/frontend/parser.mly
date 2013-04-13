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
  let string_of_op s = "(" ^ s ^ ")"

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

  let make_pat_split (u, v) =
    {
      Acids_parsetree.ps_prefix = u;
      Acids_parsetree.ps_period = v;
    }

  let make_located make (x, loc) = make x loc

  let make_clock_exp ced loc =
    {
      Acids_parsetree.ce_desc = ced;
      Acids_parsetree.ce_loc = loc;
      Acids_parsetree.ce_info = ();
    }

  let make_domain par base e =
    let d =
      {
        Acids_parsetree.d_base_clock = base;
        Acids_parsetree.d_par = par;
      }
    in
    Acids_parsetree.E_dom (e, d)

  let make_exp ed loc =
    {
      Acids_parsetree.e_desc = ed;
      Acids_parsetree.e_loc = loc;
      Acids_parsetree.e_info = ();
    }

  let make_app ln e =
    let app =
      {
        Acids_parsetree.a_op = Acids_parsetree.O_node ln;
        Acids_parsetree.a_info = ();
      }
    in
    Acids_parsetree.E_app (app, e)

  let make_tuple e_l loc = make_exp (Acids_parsetree.E_tuple e_l) loc

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

  let make_node (s, n, p, e, pr) loc =
    {
      Acids_parsetree.n_name = n;
      Acids_parsetree.n_input = p;
      Acids_parsetree.n_body = e;
      Acids_parsetree.n_pragma = pr;
      Acids_parsetree.n_static = s;
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

%token LPAREN RPAREN CARET LBRACE RBRACE DOT LCHEVRON RCHEVRON
%token EQUAL COMMA DCOLON

/* Keywords */

%token LET NODE STATIC OPEN FST SND
%token FBY IF THEN ELSE
%token WHERE REC AND
%token WHEN SPLIT MERGE
%token ON BASE

%token<bool> DOM                        (* true for parallelism *)

/* Identifiers and constants */

%token<string> IDENT
%token<string> UIDENT
%token<string> OP
%token<int> STVAR

%token<bool> BOOL
%token<Int.t> INT
%token<float> FLOAT
%token<int list> WORD

/* Misc */

%token BEGIN_PRAGMA END_PRAGMA

%token EOF

/* Disambiguation tokens */

/* Precedence and associativity */

/* Start of the grammar */

%start file
%type<Acids_parsetree.file> file

%%

with_loc(X):
 | x = X { x, Parser_utils.make_loc $startpos $endpos }

parens(X):
| LPAREN x = X RPAREN { x }

chevrons(X):
| LCHEVRON x = X RCHEVRON { x }

simple_ptree(X, Y):
| X { Ast_misc.Leaf $1 }
| simple_ptree(X, Y) CARET Y { Ast_misc.Power ($1, $3) }
| LBRACE ptree(X, Y) RBRACE { $2 }

ptree(X, Y):
| nonempty_list(simple_ptree(X, Y)) { make_concat $1 }

upword(X, Y, Z):
| v = Z(ptree(X, Y)) { (Ast_misc.Concat [], v) }
| u = ptree(X, Y) v = Z(ptree(X, Y)) { (u, v) }

shortname:
| IDENT { Initial.make_longname $1 }
| parens(OP) { Initial.make_longname (string_of_op $1) }

longname:
| shortname { $1 }
| modn = UIDENT DOT n = IDENT { Initial.make_longname ~modn n }

//////////////////////////////////////////////////////////////////

const:
| BOOL { Ast_misc.Cbool $1 }
| INT { Ast_misc.Cint $1 }
| FLOAT { Ast_misc.Cfloat $1 }
| WORD { Ast_misc.Cword $1 }

clock_exp_desc:
| IDENT { Acids_parsetree.Ce_var $1 }
| upword(trivial_exp, trivial_exp, parens)
    { Acids_parsetree.Ce_pword (make_ce_pword $1) }

clock_exp:
| with_loc(clock_exp_desc) { make_located make_clock_exp $1 }

clock_exp_exp:
| chevrons(clock_exp) { $1 }

trivial_exp_desc:
| const { Acids_parsetree.E_const $1 }
| IDENT { Acids_parsetree.E_var $1 }

trivial_exp:
| with_loc(trivial_exp_desc) { make_located make_exp $1 }

simple_exp_desc:
| trivial_exp_desc { $1 }
| FST simple_exp { Acids_parsetree.E_fst $2 }
| SND simple_exp { Acids_parsetree.E_snd $2 }
| clock_exp_exp { Acids_parsetree.E_valof $1 }
| parens(exp_desc) { $1 }

simple_exp:
| with_loc(simple_exp_desc) { make_located make_exp $1 }

nowhere_exp_desc:
| simple_exp_desc { $1 }

| e = simple_exp COMMA t = separated_nonempty_list(COMMA, simple_exp)
          { Acids_parsetree.E_tuple (e :: t) }

| e1 = simple_exp s = OP e2 = simple_exp
          { let l = Parser_utils.make_loc $startpos $endpos in
            make_app (Initial.make_longname s) (make_tuple [e1; e2] l) }
| longname nowhere_exp { make_app $1 $2 }

| e1 = simple_exp FBY e2 = simple_exp { Acids_parsetree.E_fby (e1, e2) }
| IF e1 = simple_exp THEN e2 = simple_exp ELSE e3 = simple_exp
          { Acids_parsetree.E_ifthenelse (e1, e2, e3) }

| e = simple_exp WHEN ce = clock_exp_exp { Acids_parsetree.E_when (e, ce) }
| MERGE ce = clock_exp_exp e_l = nonempty_list(simple_exp)
          { Acids_parsetree.E_merge (ce, e_l) }
| SPLIT ce = clock_exp_exp e = simple_exp { Acids_parsetree.E_split (ce, e) }

| e = simple_exp DCOLON ck = clock_annot
          { Acids_parsetree.E_clockannot (e, ck) }

nowhere_exp:
| with_loc(nowhere_exp_desc) { make_located make_exp $1 }

exp_desc:
| nowhere_exp_desc { $1 }
| simple_exp WHERE REC block { Acids_parsetree.E_where ($1, $4) }
| par = DOM e = nowhere_exp ba = option(base_annot) { make_domain par ba e }

exp:
| with_loc(exp_desc) { make_located make_exp $1 }

base_annot:
| BASE clock_annot { $2 }

eq_desc:
| p = pat EQUAL e = nowhere_exp { (p, e) }

eq:
| with_loc(eq_desc) { make_located make_eq $1 }

block_desc:
| separated_nonempty_list(AND, eq) { $1 }

block:
| with_loc(block_desc) { make_located make_block $1 }

clock_annot:
| STVAR { Acids_parsetree.Ca_var $1 }
| clock_annot ON clock_exp { Acids_parsetree.Ca_on ($1, $3) }

pat_tuple:
| p_l = separated_list(COMMA, pat) { p_l }

pat_split:
| upword(pat, simple_exp, chevrons) { make_pat_split $1 }

pat_desc:
| IDENT { Acids_parsetree.P_var $1 }
| parens(pat_tuple) { Acids_parsetree.P_tuple $1 }
| ps = parens(pat_split) { Acids_parsetree.P_split ps }
| LPAREN p = pat DCOLON ck = clock_annot RPAREN
          { Acids_parsetree.P_clock_annot (p, ck) }

pat:
| with_loc(pat_desc) { make_located make_pat $1 }

pragma:
| { None }
| BEGIN_PRAGMA END_PRAGMA { Some () }

static:
| { false }
| STATIC { true }

node_desc:
| pr = pragma LET NODE s = static n = shortname p = pat EQUAL e = exp
          { (s, n, p, e, pr) }

node:
| with_loc(node_desc) { make_located make_node $1 }

import:
| OPEN UIDENT { $2 }

file:
| imports = list(import) nodes = list(node) EOF { make_file imports nodes }
| error { Parser_utils.parse_error $startpos $endpos }
