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

  let make_pword (u, v) = { Ast_misc.u = u; Ast_misc.v = v; }

  let make_located make (x, loc) = make x loc

  let make_clock_exp ced loc =
    {
      Acids_parsetree.ce_desc = ced;
      Acids_parsetree.ce_loc = loc;
      Acids_parsetree.ce_info = ();
    }

  let make_static_exp sed loc =
    {
      Acids_parsetree.se_desc = sed;
      Acids_parsetree.se_loc = loc;
      Acids_parsetree.se_info = ();
    }

  let make_domain par base e =
    let d =
      {
        Acids_parsetree.d_base_clock = base;
        Acids_parsetree.d_par = par;
        Acids_parsetree.d_info = ();
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
        Acids_parsetree.a_op = ln;
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
        Acids_parsetree.a_op = ln;
        Acids_parsetree.a_info = ();
        Acids_parsetree.a_loc = Parser_utils.make_loc start stop;
      }
    in
    Acids_parsetree.E_app (app, make_tuple [e1; e2] loc)

  let make_pat pd loc =
    match pd with
    | Acids_parsetree.P_tuple [p] -> p
    | _ ->
      {
        Acids_parsetree.p_desc = pd;
        Acids_parsetree.p_loc = loc;
        Acids_parsetree.p_info = ();
      }

  let make_clause ((ec, e), loc) =
    {
      Acids_parsetree.c_sel = ec;
      Acids_parsetree.c_body = e;
      Acids_parsetree.c_loc = loc;
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

  let make_node_def (s, n, p, e, pr) loc =
    {
      Acids_parsetree.n_name = n;
      Acids_parsetree.n_input = p;
      Acids_parsetree.n_body = e;
      Acids_parsetree.n_pragma = pr;
      Acids_parsetree.n_static = s;
      Acids_parsetree.n_loc = loc;
      Acids_parsetree.n_info = ();
    }

  let make_node_decl (name, data, static, interv, clock) loc =
    {
      Acids_parsetree.decl_name = name;
      Acids_parsetree.decl_data = data;
      Acids_parsetree.decl_static = static;
      Acids_parsetree.decl_interv = interv;
      Acids_parsetree.decl_clock = clock;
      Acids_parsetree.decl_loc = loc;
    }

  let make_ty_sig inp out =
    {
      Data_types.data_sig_input = inp;
      Data_types.data_sig_output = out;
    }

  let make_static_sig mk_s =
    let mk_prod ty_l = Static_types.Sy_prod ty_l in
    let mk_scal ty = Static_types.Sy_scal ty in
    let mk_sig inp out =
      {
        Static_types.input = inp;
        Static_types.output = out;
        Static_types.static =
          if Static_types.is_static inp
          then Static_types.S_static
          else Static_types.S_dynamic;
      }
    in
    mk_s mk_sig (mk_prod, mk_scal)

  let make_interval_sig mk_s =
    let mk_prod ty_l = Interval_types.It_prod ty_l in
    let mk_scal ty = Interval_types.It_scal ty in
    let mk_sig inp out =
      {
        Interval_types.input = inp;
        Interval_types.output = out;
      }
    in
    mk_s mk_sig (mk_prod, mk_scal)

  let make_clock_sig mk_s =
    let mk_prod ty_l = Clock_types.Ct_prod ty_l in
    let mk_scal ty = Clock_types.Ct_stream ty in
    let mk_sig inp out =
      {
        Clock_types.ct_sig_input = inp;
        Clock_types.ct_sig_output = out;
        Clock_types.ct_constraints = [];
      }
    in
    mk_s mk_sig (mk_prod, mk_scal)

  let make_type_def ((n, c_l), loc) =
    {
      Acids_parsetree.ty_name = n;
      Acids_parsetree.ty_body = c_l;
      Acids_parsetree.ty_loc = loc;
    }

  let make_file imports body =
    {
      Acids_parsetree.f_name =
        Interface.module_name_of_file_name (Initial.get_current_file_name ());
      Acids_parsetree.f_imports =
        if !Compiler_options.no_pervasives
        then imports
        else "Pervasives" :: imports;
      Acids_parsetree.f_info = ();
      Acids_parsetree.f_body = body;
    }

  (* Ugly: a bit of scoping at parsing time *)

  let ht = Hashtbl.create 100

  let sig_scope_reinitialize () =
    Hashtbl.clear ht;
    Ident.reset_ctx ()

  let sig_scope_ident v =
    try Hashtbl.find ht v
    with Not_found ->
      let id = Ident.make_source v in
      Hashtbl.add ht v id;
      id
%}

/* Punctuation */

%token LPAREN RPAREN CARET LBRACE RBRACE LBRACKET RBRACKET DOT
%token COMMA COLON DCOLON
%token ARROW PIPE

/* Operators */

%token EQUAL
%token LT GT LE GE
%token PLUS MINUS TIMES DIV

/* Keywords */

%token LET NODE STATIC OPEN FST SND
%token FBY IF THEN ELSE
%token WHERE REC AND
%token WHEN SPLIT MERGE
%token ON BASE
%token VAL IN IS WITH END
%token TYPE BY
%token BUFFER
%token VALOF
%token COND
%token UNSPEC

%token BOOL_TY INT_TY FLOAT_TY DYNAMIC_TY STATIC_TY TOP_TY (* BOT_TY *)

%token<bool> DOM                        (* true for parallelism *)

/* Identifiers and constants */

%token<string> IDENT
%token<string> UIDENT
%token<string> OP
%token<int> STVAR
(* %token<int> TYVAR *)

%token<bool> BOOL
%token<Int.t> INT
%token<float> FLOAT
%token<Int.t list> WORD

/* Misc */

%token BEGIN_PRAGMA END_PRAGMA
%token<string> PRAGMA_KEY
%token<string> PRAGMA_VAL

%token EOF

/* Disambiguation tokens */

%token APP

/* Precedence and associativity */

%left EQUAL

%left WHERE
%left IF
// %left SPLIT
%left WHEN
%right APP
%nonassoc BUFFER
%left LE GE LT GT
%left PLUS MINUS
%left TIMES DIV
%nonassoc FST SND
%right FBY
%nonassoc IDENT
%nonassoc OP

/* Start of the grammar */

%start source_file
%type<unit Acids_parsetree.file> source_file

%%

%inline with_loc(X):
 | x = X { x, Parser_utils.make_loc $startpos $endpos }

%inline parens(X):
| LPAREN x = X RPAREN { x }

%inline chevrons(X):
| LT x = X GT { x }

%inline brackets(X):
| LBRACKET x = X RBRACKET { x }

simple_ptree(X, Y):
| x = X { Ast_misc.Leaf x }
| t = simple_ptree(X, Y) CARET y = Y { Ast_misc.Power (t, y) }
| LBRACE t = ptree(X, Y) RBRACE { t }

%inline ptree(X, Y):
| pt = nonempty_list(simple_ptree(X, Y)) { make_concat pt }

%inline upword_desc(X, Y, Z):
| v = Z(ptree(X, Y)) { (Ast_misc.Concat [], v) }
| u = ptree(X, Y) v = Z(ptree(X, Y)) { (u, v) }

%inline upword(X, Y, Z):
| w = upword_desc(X, Y, Z) { make_pword w }

tuple(ty):
| ty = ty { fun (_, mk_scal) -> mk_scal ty }
| ty_l = parens(separated_nonempty_list(TIMES, tuple(ty)))
          { fun (mk_prod, mk_scal) ->
            mk_prod (List.map (fun f -> f (mk_prod, mk_scal)) ty_l) }

signature(ty):
| left = tuple(ty) ARROW right = tuple(ty)
        { fun mk_sig mk -> mk_sig (left mk) (right mk) }

%inline name:
| s = IDENT { s }
| s = OP { string_of_op s }

op:
| OP { $1 }
| PLUS { "+" }
| MINUS { "-" }
| TIMES { "*" }
| DIV { "/" }
| LE { "<=" }
| LT { "<" }
| GE { ">=" }
| GT { ">" }
| EQUAL { "=" }

%inline nodename:
| s = IDENT | s = parens(op) { s }

%inline longname:
| n = name { Initial.make_longname n }
| modn = UIDENT DOT n = name { Initial.make_longname ~modn n }

static:
| { false }
| STATIC { true }

%inline interval_desc:
| l = INT COMMA u = INT { l, u }

interval:
| i = brackets(interval_desc) { Interval.make (fst i) (snd i) }

////////////////////////////////////////////////////////////////////////////////
// Source files
////////////////////////////////////////////////////////////////////////////////

// Definitions

econstr:
| BOOL { Ast_misc.Ec_bool $1 }
| INT { Ast_misc.Ec_int $1 }
| UIDENT { Ast_misc.Ec_constr (Initial.make_longname $1) }

const:
| econstr { Ast_misc.Cconstr $1 }
| FLOAT { Ast_misc.Cfloat $1 }

clock_exp_desc:
| v = IDENT { Acids_parsetree.Ce_condvar v }
| ce = clock_exp EQUAL se = static_exp { Acids_parsetree.Ce_equal (ce, se) }
| pt = upword(static_exp, static_exp, parens) { Acids_parsetree.Ce_pword pt }

%inline clock_exp:
| ced = with_loc(clock_exp_desc) { make_located make_clock_exp ced }

%inline static_exp:
| sed = with_loc(static_exp_desc) { make_located make_static_exp sed }

%inline static_exp_desc:
| v = IDENT { Acids_parsetree.Info.Se_var v }
| ec = econstr { Acids_parsetree.Info.Se_econstr ec }
| w = WORD { Acids_parsetree.Info.Se_fword w }

simple_exp_desc:
| c = const { Acids_parsetree.E_const c }
| v = IDENT { Acids_parsetree.E_var v }
| ed = parens(exp_desc) { ed }
| LPAREN e = exp DCOLON ck = clock_annot RPAREN
                        { Acids_parsetree.E_clock_annot (e, ck) }
| LPAREN e = exp COLON ty = data_ty RPAREN
                        { Acids_parsetree.E_type_annot (e, ty) }
| LPAREN e = exp IN s = spec RPAREN
                        { Acids_parsetree.E_spec_annot (e, s) }

%inline simple_exp:
| ed = with_loc(simple_exp_desc) { make_located make_exp ed }

exp_desc:
| ed = simple_exp_desc { ed }

| FST e = exp { Acids_parsetree.E_fst e }
| SND e = exp { Acids_parsetree.E_snd e }

| LPAREN RPAREN { Acids_parsetree.E_tuple [] }
| LPAREN e = exp COMMA e_l = separated_nonempty_list(COMMA, exp) RPAREN
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

| e = exp WHEN ce = clock_exp { Acids_parsetree.E_when (e, ce) }
| MERGE ce = clock_exp e1 = simple_exp e2 = simple_exp
            { Acids_parsetree.E_bmerge (ce, e1, e2) }
| MERGE ce = clock_exp WITH c_l = nonempty_list(merge_clause) END
            { Acids_parsetree.E_merge (ce, c_l) }
| SPLIT e = exp
  WITH ce = clock_exp BY c_l = parens(separated_nonempty_list(COMMA, econstr))
            { Acids_parsetree.E_split (ce, e, c_l) }

| VALOF ce = clock_exp { Acids_parsetree.E_valof ce }

| e = exp WHERE REC b = block { Acids_parsetree.E_where (e, b) }
| par = DOM e = simple_exp ba = option(base_annot)
                              { make_domain par ba e }
| BUFFER e = exp { Acids_parsetree.E_buffer e }

%inline exp:
| ed = with_loc(exp_desc) { make_located make_exp ed }

merge_clause_desc:
| PIPE ec = econstr ARROW e = exp { (ec, e) }

merge_clause:
| mc = with_loc(merge_clause_desc) { make_clause mc }

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
| v = STVAR { Acids_parsetree.Ca_var v }
| cka = clock_annot ON ce = clock_exp { Acids_parsetree.Ca_on (cka, ce) }

%inline tuple_pat:
| { [] }
| p = pat COMMA p_l = separated_nonempty_list(COMMA, pat) { p :: p_l }

pat_desc:
| id = IDENT { Acids_parsetree.P_var id }
| COND id = IDENT { Acids_parsetree.P_condvar id }
| p_l = parens(tuple_pat) { Acids_parsetree.P_tuple p_l }
| pt = chevrons(upword(pat, static_exp, parens))
   { Acids_parsetree.P_split pt }
| LPAREN p = pat DCOLON ck = clock_annot RPAREN
   { Acids_parsetree.P_clock_annot (p, ck) }
| LPAREN p = pat COLON tya = data_ty RPAREN
   { Acids_parsetree.P_type_annot (p, tya) }
| LPAREN p = pat IN s = spec RPAREN
   { Acids_parsetree.P_spec_annot (p, s) }

%inline general_pat(PD):
| pd = with_loc(PD) { make_located make_pat pd }

pat:
| p = general_pat(pat_desc) { p }

spec:
| UNSPEC { Acids_parsetree.Unspec }
| p = upword(static_exp, static_exp, parens) { Acids_parsetree.Word p }
| LBRACKET l = static_exp COMMA u = static_exp RBRACKET { Acids_parsetree.Interval (l, u) }

pragma_desc:
| key = PRAGMA_KEY COLON value = PRAGMA_VAL { (key, value) }

pragma:
| pd = with_loc(pragma_desc) { make_located Pragma.make_command pd }

pragma_node:
| { [] }
| BEGIN_PRAGMA p_l = separated_list(COMMA, pragma) END_PRAGMA { p_l }

node_desc:
| pr = pragma_node LET s = static NODE n = nodename p = pat EQUAL e = exp
          { (s, n, p, e, pr) }

node:
| nd = with_loc(node_desc) { make_located make_node_def nd }

// Declarations

data_ty_scal:
| BOOL_TY { Data_types.Tys_bool }
| INT_TY { Data_types.Tys_int }
| FLOAT_TY { Data_types.Tys_float }
| ln = longname { Data_types.Tys_user ln }

data_ty:
| tys = data_ty_scal { Data_types.Ty_scal tys }
| ty_l = parens(separated_list(COMMA, data_ty)) { Data_types.Ty_prod ty_l }

data_ty_signature:
| inp = data_ty ARROW out = data_ty { make_ty_sig inp out }

econstr_singleton:
| econstr { [$1] }

clock_exp_ty:
| id = IDENT IN it = interval { Clock_types.Ce_var (sig_scope_ident id, it) }
| w = upword(econstr_singleton, INT, parens) { Clock_types.Ce_pword w }
| ce = clock_exp_ty EQUAL ec = econstr { Clock_types.Ce_equal (ce, ec) }

clock_ty:
| STVAR { Clock_types.St_var $1 }
| ck = clock_ty ON ce = clock_exp_ty { Clock_types.St_on (ck, ce) }

static_ty:
| STATIC_TY { Static_types.S_static }
| DYNAMIC_TY { Static_types.S_dynamic }

interval_ty:
| TOP_TY { Interval_types.Is_top }
| i = interval { Interval_types.Is_inter i }

placeholder_sig_init:
| { sig_scope_reinitialize () }

node_decl_desc:
| placeholder_sig_init
  VAL nn = nodename
  COLON ty_sig = data_ty_signature
  DCOLON ck_sig = signature(clock_ty)
  IS static_sig = signature(static_ty)
  IN interval_sig = signature(interval_ty)
        {
           (nn,
            ty_sig,
            make_static_sig static_sig,
            make_interval_sig interval_sig,
            make_clock_sig ck_sig)
        }

node_decl:
| nd = with_loc(node_decl_desc) { make_located make_node_decl nd }

type_def_desc:
| TYPE nn = IDENT EQUAL c_l = separated_nonempty_list(PIPE, UIDENT) { nn, c_l }

type_def:
| d = with_loc(type_def_desc) { make_type_def d }

import:
| OPEN UIDENT { $2 }

phrase:
| nd = node { Acids_parsetree.Phr_node_def nd }
| decl = node_decl { Acids_parsetree.Phr_node_decl decl }
| td = type_def { Acids_parsetree.Phr_type_def td }

source_file:
| imports = list(import) body = list(phrase) EOF { make_file imports body }
| error { Parser_utils.parse_error $startpos $endpos }
