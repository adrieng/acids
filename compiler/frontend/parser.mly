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

  let make_ce_pword (u, v) = { Ast_misc.u = u; Ast_misc.v = v; }

  let make_pat_split (u, v) = { Ast_misc.u = u; Ast_misc.v = v; }

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

  let make_app e ln ln_loc =
    let app =
      {
        Acids_parsetree.a_op = Acids_parsetree.O_node ln;
        Acids_parsetree.a_info = ();
        Acids_parsetree.a_loc = ln_loc;
      }
    in
    Acids_parsetree.E_app (app, e)

  let make_tuple e_l loc = make_exp (Acids_parsetree.E_tuple e_l) loc

  let make_bin_op start stop op e1 e2 =
    let loc = Parser_utils.make_loc start stop in
    let ln = Initial.make_longname (string_of_op op) in
    let app =
      {
        Acids_parsetree.a_op = Acids_parsetree.O_node ln;
        Acids_parsetree.a_info = ();
        Acids_parsetree.a_loc = Parser_utils.make_loc start stop;
      }
    in
    Acids_parsetree.E_app (app, make_tuple [e1; e2] loc)

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
      Acids_parsetree.f_info = ();
      Acids_parsetree.f_nodes = body;
    }
%}

/* Punctuation */

%token LPAREN RPAREN CARET LBRACE RBRACE DOT
%token COMMA DCOLON

/* Operators */

%token EQUAL
%token LT GT LE GE
%token PLUS MINUS TIMES DIV

/* Keywords */

%token LET NODE STATIC OPEN FST SND
%token ITER
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

%token APP

/* Precedence and associativity */

%nonassoc ITER
%left EQUAL

%left WHERE
%left IF
%left SPLIT
%left WHEN
%right APP
%left LE GE LT GT
%left PLUS MINUS
%left TIMES DIV
%nonassoc FST SND
%right FBY
%nonassoc IDENT
%nonassoc OP

/* Start of the grammar */

%start file
%type<unit Acids_parsetree.file> file

%%

%inline with_loc(X):
 | x = X { x, Parser_utils.make_loc $startpos $endpos }

parens(X):
| LPAREN x = X RPAREN { x }

%inline chevrons(X):
| LT x = X GT { x }

simple_ptree(X, Y):
| x = X { Ast_misc.Leaf x }
| t = simple_ptree(X, Y) CARET y = Y { Ast_misc.Power (t, y) }
| LBRACE t = ptree(X, Y) RBRACE { t }

ptree(X, Y):
| nonempty_list(simple_ptree(X, Y)) { make_concat $1 }

upword(X, Y, Z):
| v = Z(ptree(X, Y)) { (Ast_misc.Concat [], v) }
| u = ptree(X, Y) v = Z(ptree(X, Y)) { (u, v) }

%inline name:
| s = IDENT { s }
| s = OP { string_of_op s }

%inline shortname:
| s = IDENT | s = parens(OP) { Initial.make_longname s }

%inline longname:
| n = name { Initial.make_longname n }
| modn = UIDENT DOT n = name { Initial.make_longname ~modn n }

//////////////////////////////////////////////////////////////////

const:
| BOOL { Ast_misc.Cbool $1 }
| INT { Ast_misc.Cint $1 }
| FLOAT { Ast_misc.Cfloat $1 }
| WORD { Ast_misc.Cword $1 }

clock_exp_desc:
| v = IDENT { Acids_parsetree.Ce_var v }
| ITER ce = clock_exp { Acids_parsetree.Ce_iter ce }
| ce = clock_exp EQUAL e = trivial_exp { Acids_parsetree.Ce_equal (ce, e) }
| upword(trivial_exp, trivial_exp, parens)
    { Acids_parsetree.Ce_pword (make_ce_pword $1) }

clock_exp:
| ced = with_loc(clock_exp_desc) { make_located make_clock_exp ced }

clock_exp_exp:
| ce = chevrons(clock_exp) { ce }

trivial_exp_desc:
| c = const { Acids_parsetree.E_const c }
| v = IDENT { Acids_parsetree.E_var v }

%inline trivial_exp:
| ed = with_loc(trivial_exp_desc) { make_located make_exp ed }

simple_exp_desc:
| ed = trivial_exp_desc { ed }
| ed = parens(exp_desc) { ed }
| LPAREN e = exp DCOLON ck = clock_annot RPAREN
                        { Acids_parsetree.E_clockannot (e, ck) }

%inline simple_exp:
| ed = with_loc(simple_exp_desc) { make_located make_exp ed }

exp_desc:
| ed = simple_exp_desc { ed }

| FST e = exp { Acids_parsetree.E_fst e }
| SND e = exp { Acids_parsetree.E_snd e }
| e = simple_exp COMMA e_l = separated_nonempty_list(COMMA, simple_exp)
              { Acids_parsetree.E_tuple (e :: e_l) }

| e1 = exp PLUS e2 = exp
            { make_bin_op $startpos $endpos Parser_utils.plus e1 e2 }
| e1 = exp MINUS e2 = exp
            { make_bin_op $startpos $endpos Parser_utils.minus e1 e2 }
| e1 = exp TIMES e2 = exp
            { make_bin_op $startpos $endpos Parser_utils.times e1 e2 }
| e1 = exp DIV e2 = exp
            { make_bin_op $startpos $endpos Parser_utils.div e1 e2 }
| e1 = exp LE e2 = exp
            { make_bin_op $startpos $endpos Parser_utils.le e1 e2 }
| e1 = exp GE e2 = exp
            { make_bin_op $startpos $endpos Parser_utils.ge e1 e2 }
| e1 = exp LT e2 = exp
            { make_bin_op $startpos $endpos Parser_utils.lt e1 e2 }
| e1 = exp GT e2 = exp
            { make_bin_op $startpos $endpos Parser_utils.gt e1 e2 }
| e1 = exp s = OP e2 = exp
            { make_bin_op $startpos $endpos s e1 e2 }

| ln = with_loc(longname) e = exp %prec APP { make_located (make_app e) ln }

| e1 = exp FBY e2 = exp { Acids_parsetree.E_fby (e1, e2) }
| IF e1 = exp THEN e2 = exp ELSE e3 = exp %prec IF
            { Acids_parsetree.E_ifthenelse (e1, e2, e3) }

| e = exp WHEN ce = clock_exp_exp { Acids_parsetree.E_when (e, ce) }
| MERGE ce = clock_exp_exp e_l = nonempty_list(simple_exp)
            { Acids_parsetree.E_merge (ce, e_l) }
| SPLIT ce = clock_exp_exp e = exp { Acids_parsetree.E_split (ce, e) }

| ce = clock_exp_exp { Acids_parsetree.E_valof ce }

| e = exp WHERE REC b = block { Acids_parsetree.E_where (e, b) }
| par = DOM e = simple_exp ba = option(base_annot)
                              { make_domain par ba e }

%inline exp:
| ed = with_loc(exp_desc) { make_located make_exp ed }

base_annot:
| BASE clock_annot { $2 }

eq_desc:
| p = pat EQUAL e = exp { (p, e) }

eq:
| eqd = with_loc(eq_desc) { make_located make_eq eqd }

block_desc:
| separated_nonempty_list(AND, eq) { $1 }

block:
| b = with_loc(block_desc) { make_located make_block b }

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
| pd = with_loc(pat_desc) { make_located make_pat pd }

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
| nd = with_loc(node_desc) { make_located make_node nd }

import:
| OPEN UIDENT { $2 }

file:
| imports = list(import) nodes = list(node) EOF { make_file imports nodes }
| error { Parser_utils.parse_error $startpos $endpos }
