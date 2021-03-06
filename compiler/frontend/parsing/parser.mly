/* Copyright (C) Adrien Guatto <adrien.guatto@laposte.net> 2013-2014-2014
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
    | _ :: _ -> Tree_word.Concat l

  let make_pword (u, v) = { Tree_word.u = u; Tree_word.v = v; }

  let make_econstr n =
    Ast_misc.Ec_constr (Initial.make_longname n, Int.of_int (- 1))

  let make_clock_exp (ced, loc) =
    {
      Acids_parsetree.ce_desc = ced;
      Acids_parsetree.ce_loc = loc;
      Acids_parsetree.ce_info = ();
    }

  let make_const_exp (sed, loc) =
    {
      Acids_parsetree.se_desc = sed;
      Acids_parsetree.se_loc = loc;
      Acids_parsetree.se_info = ();
    }

  let make_const_exp_econstr (ec, loc) =
    make_const_exp (Acids_parsetree.Info.Se_econstr ec, loc)

  let make_const_exp_fword (i_l, loc) =
    make_const_exp (Acids_parsetree.Info.Se_fword i_l, loc)

  let make_domain par base e =
    let d =
      {
        Acids_parsetree.d_base_clock = base;
        Acids_parsetree.d_par = par;
        Acids_parsetree.d_info = ();
      }
    in
    Acids_parsetree.E_dom (e, d)

  let make_buffer () =
    {
      Acids_parsetree.bu_info = ();
    }

  let make_spec (sd, loc) =
    {
      Acids_parsetree.s_desc = sd;
      Acids_parsetree.s_loc = loc;
    }

  let make_exp (ed, loc) =
    {
      Acids_parsetree.e_desc = ed;
      Acids_parsetree.e_loc = loc;
      Acids_parsetree.e_info = ();
    }

  let make_app e (ln, ln_loc) =
    let app =
      {
        Acids_parsetree.a_op = ln;
        Acids_parsetree.a_info = ();
        Acids_parsetree.a_loc = ln_loc;
      }
    in
    Acids_parsetree.E_app (app, e)

  let make_tuple (e_l, loc) = make_exp (Acids_parsetree.E_tuple e_l, loc)

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
    Acids_parsetree.E_app (app, make_tuple ([e1; e2], loc))

  let make_pat (pd, loc) =
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

  let make_eq (desc, loc) =
    {
      Acids_parsetree.eq_desc = desc;
      Acids_parsetree.eq_loc = loc;
      Acids_parsetree.eq_info = ();
    }

  let make_block (eqs, loc) =
    {
      Acids_parsetree.b_body = eqs;
      Acids_parsetree.b_loc = loc;
      Acids_parsetree.b_info = ();
    }

  let make_pragma ((k, v), loc) =
    {
      Pragma.loc = loc;
      Pragma.key = k;
      Pragma.value = v;
    }

  let make_node_def ((s, n, p, e, pr), loc) =
    {
      Acids_parsetree.n_name = n;
      Acids_parsetree.n_input = p;
      Acids_parsetree.n_body = e;
      Acids_parsetree.n_pragma = pr;
      Acids_parsetree.n_const = s;
      Acids_parsetree.n_loc = loc;
      Acids_parsetree.n_info = ();
    }

  let make_node_decl ((name, data, const, clock), loc) =
    {
      Acids_parsetree.decl_name = name;
      Acids_parsetree.decl_data = data;
      Acids_parsetree.decl_const = const;
      Acids_parsetree.decl_clock = clock;
      Acids_parsetree.decl_loc = loc;
    }

  let make_ty_sig inp out =
    {
      Data_types.data_sig_input = inp;
      Data_types.data_sig_output = out;
    }

  let make_const_sig inp out =
    {
      Const_types.input = inp;
      Const_types.output = out;
      Const_types.const =
        if Const_types.is_const inp
        then Const_types.S_const
        else Const_types.S_nonconst;
    }

  let make_clock_sig inp out =
    {
      Clock_types.ct_sig_input = inp;
      Clock_types.ct_sig_output = out;
      Clock_types.ct_constraints = [];
    }

  let make_type_def ((n, c_l), loc) =
    {
      Ast_misc.ty_name = n;
      Ast_misc.ty_body = c_l;
      Ast_misc.ty_loc = loc;
    }

  let make_file imports body =
    {
      Acids_parsetree.f_name =
        Interface.get_current_module_name ();
      Acids_parsetree.f_imports =
        if !Compiler_options.no_pervasives
        then imports
        else "Pervasives" :: imports;
      Acids_parsetree.f_info = ();
      Acids_parsetree.f_body = body;
    }

  let make_const_def ((name, body), loc) =
    {
      Acids_parsetree.sd_name = name;
      Acids_parsetree.sd_body = body;
      Acids_parsetree.sd_loc = loc;
    }

  let make_pword_def ((name, body), loc) =
    {
      Acids_parsetree.pd_name = name;
      Acids_parsetree.pd_body = body;
      Acids_parsetree.pd_loc = loc;
    }

  (* Ugly: some scoping is performed at parsing time using the following
     hash-table. *)
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

  let make_ce_var id specs =
    let cev =
      {
        Clock_types.cecv_name = sig_scope_ident id;
        Clock_types.cecv_bounds = Interval.singleton Int.zero;
        Clock_types.cecv_specs = specs;
      }
    in
    Clock_types.Ce_condvar cev
%}

/* Punctuation */

%token LPAREN RPAREN CARET LBRACE RBRACE LBRACKET RBRACKET DOT
%token COMMA COLON DCOLON
%token ARROW PIPE

/* Operators */

%token EQUAL
%token LT GT LE GE
%token PLUS MINUS TIMES DIV
%token PLUSF MINUSF TIMESF DIVF

/* Keywords */

%token LET NODE CONST PWORD OPEN FST SND
%token FBY IF THEN ELSE
%token WHERE REC AND
%token WHEN SPLIT MERGE
%token ON BASE
%token VAL IN IS WITH END
%token TYPE BY
%token BUFFER
%token VALOF
%token COND
%token BOXED
%token UNSPEC

%token BOOL_TY INT_TY FLOAT_TY NONCONST_TY CONST_TY (* TOP_TY BOT_TY *)

%token<bool> DOM                        (* true for parallelism *)

/* Identifiers and constants */

%token<string> IDENT
%token<string> UIDENT
%token<string> PRAGMAKEY
%token<string> OP
%token<int> STVAR
%token<int> CONSTVAR
%token<int> TYVAR

%token<bool> BOOL
%token<Int.t> INT
%token<float> FLOAT
%token<Int.t list> FWORD

/* Misc */

%token EOF

/* Disambiguation tokens */

%token APP

/* Precedence and associativity */

%left WHERE
%left EQUAL
%left IF
// %left SPLIT
%nonassoc OP
%left LE GE LT GT
%left PLUS MINUS PLUSF MINUSF
%left TIMES DIV TIMESF DIVF
%right APP
%left WHEN
%nonassoc BUFFER
%nonassoc FST SND
%right FBY
%nonassoc IDENT

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

%inline braces(X):
| LBRACE x = X RBRACE { x }

simple_ptree(X, Y):
| x = X { Tree_word.Leaf x }
| t = simple_ptree(X, Y) CARET y = Y { Tree_word.Power (t, y) }
| t = brackets(ptree(X, Y)) { t }

%inline ptree(X, Y):
| pt = nonempty_list(simple_ptree(X, Y)) { make_concat pt }

%inline upword_desc(X, Y, Z):
| v = Z(ptree(X, Y)) { (Tree_word.Concat [], v) }
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
| PLUS   { Parser_utils.plus   }
| MINUS  { Parser_utils.minus  }
| TIMES  { Parser_utils.times  }
| DIV    { Parser_utils.div    }
| PLUSF  { Parser_utils.plusf  }
| MINUSF { Parser_utils.minusf }
| TIMESF { Parser_utils.timesf }
| DIVF   { Parser_utils.divf   }
| LE     { Parser_utils.le     }
| LT     { Parser_utils.lt     }
| GE     { Parser_utils.ge     }
| GT     { Parser_utils.gt     }
| EQUAL  { Parser_utils.eq     }

%inline nodename:
| s = IDENT { s }
| s = parens(op) { "(" ^ s ^ ")" }

%inline qualified_longname:
| modn = UIDENT DOT n = name { Initial.make_longname ~modn n }

%inline longname:
| n = name { Initial.make_longname n }
| ln = qualified_longname { ln }

is_const:
| { false }
| CONST { true }

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
| UIDENT { make_econstr $1 }

const:
| econstr { Ast_misc.Cconstr $1 }
| FLOAT { Ast_misc.Cfloat $1 }

const_pword:
| pw = upword(const_exp_root_fword, const_exp_root, parens) { pw }

clock_exp_desc:
| v = IDENT
   { Acids_parsetree.Ce_condvar v }
| ce = clock_exp EQUAL se = const_exp
   { Acids_parsetree.Ce_equal (ce, se) }
| pw = const_pword
   { Acids_parsetree.Ce_pword (Acids_parsetree.Pd_lit pw) }
| ln = qualified_longname
   { Acids_parsetree.Ce_pword (Acids_parsetree.Pd_global ln) }

clock_exp:
| ced = with_loc(clock_exp_desc) { make_clock_exp ced }
| ce = parens(clock_exp) { ce }

(******************** CONST EXPS ********************)

const_exp_desc:
| ec = econstr { Acids_parsetree.Info.Se_econstr ec }
| v = IDENT { Acids_parsetree.Info.Se_var v }
| ln = qualified_longname { Acids_parsetree.Info.Se_global ln }
| se1 = const_exp PLUS se2 = const_exp
   { Acids_parsetree.Info.Se_binop ("(+)", se1, se2) }
| se1 = const_exp MINUS se2 = const_exp
   { Acids_parsetree.Info.Se_binop ("(-)", se1, se2) }
| se1 = const_exp TIMES se2 = const_exp
   { Acids_parsetree.Info.Se_binop ("(*)", se1, se2) }
| se1 = const_exp DIV se2 = const_exp
   { Acids_parsetree.Info.Se_binop ("(/)", se1, se2) }

const_exp:
| sed = with_loc(const_exp_desc) { make_const_exp sed }
| se = parens(const_exp) { se }

const_exp_root:
| ec = with_loc(econstr) { make_const_exp_econstr ec }
| se = braces(const_exp) { se }

const_exp_root_fword:
| wl = with_loc(FWORD) { make_const_exp_fword wl }
| se = const_exp_root { se }

(******************** END CONST EXPS ********************)

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
| ed = with_loc(simple_exp_desc) { make_exp ed }

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
| e1 = exp PLUSF e2 = exp
            { make_bin_op $startpos $endpos Parser_utils.plusf e1 e2 }
| e1 = exp MINUSF e2 = exp
            { make_bin_op $startpos $endpos Parser_utils.minusf e1 e2 }
| e1 = exp TIMESF e2 = exp
            { make_bin_op $startpos $endpos Parser_utils.timesf e1 e2 }
| e1 = exp DIVF e2 = exp
            { make_bin_op $startpos $endpos Parser_utils.divf e1 e2 }
| e1 = exp LE e2 = exp
            { make_bin_op $startpos $endpos Parser_utils.le e1 e2 }
| e1 = exp GE e2 = exp
            { make_bin_op $startpos $endpos Parser_utils.ge e1 e2 }
| e1 = exp LT e2 = exp
            { make_bin_op $startpos $endpos Parser_utils.lt e1 e2 }
| e1 = exp GT e2 = exp
            { make_bin_op $startpos $endpos Parser_utils.gt e1 e2 }
| e1 = exp EQUAL e2 = exp
            { make_bin_op $startpos $endpos Parser_utils.eq e1 e2 }
| e1 = exp s = OP e2 = exp
            { make_bin_op $startpos $endpos s e1 e2 }

| ln = with_loc(longname) e = exp %prec APP { make_app e ln }

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
| BUFFER e = exp { Acids_parsetree.E_buffer (e, make_buffer ()) }

%inline exp:
| ed = with_loc(exp_desc) { make_exp ed }

merge_clause_desc:
| PIPE ec = econstr ARROW e = exp { (ec, e) }

merge_clause:
| mc = with_loc(merge_clause_desc) { make_clause mc }

base_annot:
| BASE clock_annot { $2 }

eq_desc:
| p = pat EQUAL e = exp
   { Acids_parsetree.Eq_plain (p, e) }
| COND id = IDENT specs = list(spec_ann) EQUAL e = exp
   { Acids_parsetree.Eq_condvar (id, specs, e) }

eq:
| eqd = with_loc(eq_desc) { make_eq eqd }

block_desc:
| separated_nonempty_list(AND, eq) { $1 }

block:
| b = with_loc(block_desc) { make_block b }

clock_annot:
| v = STVAR { Acids_parsetree.Ca_var v }
| cka = clock_annot ON ce = clock_exp { Acids_parsetree.Ca_on (cka, ce) }

%inline tuple_pat:
| { [] }
| p = pat COMMA p_l = separated_nonempty_list(COMMA, pat) { p :: p_l }

spec_ann:
| IN s = spec { s }

pat_desc:
| id = IDENT { Acids_parsetree.P_var id }
| p_l = parens(tuple_pat) { Acids_parsetree.P_tuple p_l }
| pt = chevrons(upword(pat, const_exp_root, parens))
   { Acids_parsetree.P_split pt }
| LPAREN p = pat DCOLON ck = clock_annot RPAREN
   { Acids_parsetree.P_clock_annot (p, ck) }
| LPAREN p = pat COLON tya = data_ty RPAREN
   { Acids_parsetree.P_type_annot (p, tya) }
| LPAREN p = pat IN s = spec RPAREN
   { Acids_parsetree.P_spec_annot (p, s) }

pat:
| pd = with_loc(pat_desc) { make_pat pd }

spec_desc:
| UNSPEC { Acids_parsetree.Unspec }
| p = upword(const_exp_root_fword, const_exp_root, parens)
   { Acids_parsetree.Word p }
| LBRACKET l = const_exp COMMA u = const_exp RBRACKET
   { Acids_parsetree.Interval (l, u) }

spec:
| sdl = with_loc(spec_desc) { make_spec sdl }

%inline pragma_val:
| ec = econstr { Pragma.Econstr ec }
| v_l = parens(separated_list(COMMA, pragma_val)) { Pragma.Tuple v_l }

%inline pragma_desc:
| key = PRAGMAKEY value = braces(pragma_val) { (key, value) }

%inline pragma:
| pd = with_loc(pragma_desc) { make_pragma pd }

%inline pragma_node:
| p_l = list(pragma) { p_l }

node_def_desc:
| pr = pragma_node LET s = is_const NODE n = nodename p = pat EQUAL e = exp
   { (s, n, p, e, pr) }

node_def:
| nd = with_loc(node_def_desc) { make_node_def nd }

// Declarations

data_ty_scal:
| BOOL_TY { Data_types.Tys_bool }
| INT_TY { Data_types.Tys_int }
| FLOAT_TY { Data_types.Tys_float }
| ln = longname { Data_types.Tys_user ln }

data_ty:
| tys = data_ty_scal { Data_types.Ty_scal tys }
| tyv = TYVAR { Data_types.Ty_var tyv }
| ty_l = parens(separated_list(TIMES, data_ty)) { Data_types.Ty_prod ty_l }
| ty = data_ty BOXED { Data_types.Ty_boxed ty }

data_ty_signature:
| inp = data_ty ARROW out = data_ty { make_ty_sig inp out }

const_ty_scal:
| CONST_TY { Const_types.S_const }
| NONCONST_TY { Const_types.S_nonconst }

const_ty:
| tys = const_ty_scal { Const_types.Sy_scal tys }
| tyv = CONSTVAR { Const_types.Sy_var tyv }
| ty_l = parens(separated_list(TIMES, const_ty)) { Const_types.Sy_prod ty_l }

const_ty_signature:
| inp = const_ty ARROW out = const_ty { make_const_sig inp out }

concrete_spec:
| UNSPEC { Ast_misc.Unspec }
| it = interval { Ast_misc.Interval it }
| p = upword(INT, INT, parens) { Ast_misc.Word p }

concrete_spec_ann:
| IN s = concrete_spec { s }

clock_exp_ty:
| id = IDENT specs = list(concrete_spec_ann) { make_ce_var id specs }
| w = upword(econstr, INT, parens) { Clock_types.Ce_pword w }
| ce = clock_exp_ty EQUAL ec = econstr { Clock_types.Ce_equal (ce, ec) }

stream_ty:
| stv = STVAR { Clock_types.St_var stv }
| st = stream_ty ON ce = clock_exp_ty { Clock_types.St_on (st, ce) }

clock_ty:
| st = stream_ty { Clock_types.Ct_stream st }
| ct_l = parens(separated_list(TIMES, clock_ty)) { Clock_types.Ct_prod ct_l }

clock_ty_signature:
| inp = clock_ty ARROW out = clock_ty { make_clock_sig inp out }

placeholder_sig_init:
| { sig_scope_reinitialize () }

node_decl_desc:
| placeholder_sig_init
  VAL nn = nodename
  COLON ty_sig = data_ty_signature
  IS const_sig = const_ty_signature
  DCOLON ck_sig = clock_ty_signature
   { (nn, ty_sig, const_sig, ck_sig) }

node_decl:
| nd = with_loc(node_decl_desc) { make_node_decl nd }

type_def_desc:
| TYPE nn = IDENT EQUAL c_l = separated_nonempty_list(PIPE, UIDENT) { nn, c_l }

type_def:
| d = with_loc(type_def_desc) { make_type_def d }

const_def_desc:
| pragma_node LET CONST s = IDENT EQUAL e = exp { (s, e) }

const_def:
| sdl = with_loc(const_def_desc) { make_const_def sdl }

pword_def_desc:
| pragma_node LET PWORD s = IDENT EQUAL pw = const_pword { (s, pw) }

pword_def:
| pdl = with_loc(pword_def_desc) { make_pword_def pdl }

import:
| OPEN UIDENT { $2 }

phrase:
| nd = node_def { Acids_parsetree.Phr_node_def nd }
| decl = node_decl { Acids_parsetree.Phr_node_decl decl }
| td = type_def { Acids_parsetree.Phr_type_def td }
| sd = const_def { Acids_parsetree.Phr_const_def sd }
| pd = pword_def { Acids_parsetree.Phr_pword_def pd }

source_file:
| imports = list(import) body = list(phrase) EOF { make_file imports body }
| error { Parser_utils.parse_error $startpos $endpos }
