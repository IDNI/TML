# TML grammar definition file.
#
# This grammar requires the following builtins map to be passed to the parser:
#
#    auto eof = char_traits<char32_t>::eof();
#    earley_t::char_builtins_map bltnmap{
#        { U"space",         [](const char32_t& c)->bool {
#            return c < 256 && isspace(c); } },
#        { U"digit",         [](const char32_t& c)->bool {
#            return c < 256 && isdigit(c); } },
#        { U"alpha",     [&eof](const char32_t& c)->bool {
#            return c != eof && (c > 160 || isalpha(c)); } },
#        { U"alnum",     [&eof](const char32_t& c)->bool {
#            return c != eof && (c > 160 || isalnum(c)); } },
#        { U"printable", [&eof](const char32_t& c)->bool {
#            return c != eof && (c > 160 || isprint(c)); } },
#        { U"eof",       [&eof](const char32_t& c)->bool {
#            return c == eof; } }
#    };

#
## whitespace
#
eol             => '\r' | '\n' | eof.
ws_comment      => '#' eol | '#' printable_chars eol.
ws_required     => space ws | ws_comment ws.
ws              => ws_required | null.

# Important notice: ws between statements is already covered.
# Starting or/and ending a production rule with "ws" can cause ambiguity!

#
## character groups and definitions
#
hex_digit       => digit | 'A' | 'B' | 'C' | 'D' | 'E' | 'F' |
                           'a' | 'b' | 'c' | 'd' | 'e' | 'f'.
hex_escape      => "\\x" hex_digit hex_digit.
unicode_escape  => "\\u" hex_digit hex_digit hex_digit hex_digit.
char_escape_encode => hex_escape | unicode_escape.

# defining char/string/qstring as all chars but its wrapping character enables
# using TAB and new lines in char(')/string(")/quotestring(`) sequences
char0           => alnum | space | char_escape_encode |
                   '!' | '#' | '$' | '%' | '&' | '(' | ')' | '*' | '+' | ',' |
                   '-' | '.' | '/' | ':' | ';' | '<' | '=' | '>' | '?' | '@' |
                   '[' | '\\'| ']' | '^' | '_' | '{' | '|' | '}' | '~'.
char            => char0 | '\\' '\'' |      '"'  |      '`'.
string_char     => char0 |      '\'' | '\\' '"'  |      '`'.
quote_string_char=>char0 |      '\'' |      '"'  | '\\' '`'.

# sequence of one or more string characters
string_chars    => string_char string_chars1.
string_chars1   => string_char string_chars1 | null.

# sequence of one or more quote characters
quote_string_chars   => quote_string_char quote_string_chars1.
quote_string_chars1  => quote_string_char quote_string_chars1 | null.

# sequence of one or more printable characters
printable_chars => printable printable_chars_rest.
printable_chars_rest =>
                   printable printable_chars_rest | null.

# alphanumeric names which cannot begin with a numeric character
chars           => alpha chars1 | '_' chars1.
chars1          => alnum chars1 | '_' chars1 | null.

#
## numeric groups and definitions
#
integer         => digit+.

#
## elements
#
sym             => chars.
var             => '?' chars.
number          => integer.

quoted_char     => "'" char "'" | "'" char_escape_encode "'" |
                   quoted_char_esc | empty_char.
empty_char      => "''".
quoted_char_esc => "'\\" printable "'".

string          => '"' string_chars '"' | empty_string.
empty_string    => '"' '"'.

quote_string    => '`' quote_string_chars '`' | empty_quote_string.
empty_quote_string => '`' '`'.

#
## term
#
term            => negative_term | positive_term.
negative_term   => '~' ws positive_term.
positive_term   => relname args | relname.
args            => ws '(' ws elems ws ')' | ws '(' ws ')'.
elems           => elem | elem ws_required elems_rest |
                   relname args | relname args ws elems_rest.
elems_rest      => elem | elem args | elem ws_required elems_rest | args.
elem            => sym | var | number | quoted_char | string | char_builtin.
relname         => sym.

#
## builtins
#
builtin_expr    => builtin_term | builtin_prefixes ws builtin_term.
builtin_prefixes=> builtin_prefix | builtin_prefix ws builtin_prefixes.
builtin_prefix  => renew_prefix | forget_prefix.
renew_prefix    => "renew".
forget_prefix   => "forget".
builtin_term    => builtin args | builtin.
builtin         => "halt" | "error" | "false" | "forget" | "rnd" | "count" | 
                   "bw_and" | "bw_or" | "bw_xor" | "bw_not" |
                   "pw_add" | "pw_mult" |
                   "leq" |
                   "print" | "println" | "println_to" | "print_to" |
                   "print_delim" | "println_delim" |  "print_to_delim" |
                   "println_to_delim" | 
                   "js_eval".
char_builtin    => "alpha" | "alnum" | "digit" | "space" | "printable" | "eof".

#
## arithmetic expression
#
arith_expr      => arith_op_expr | arith_waux_expr.
arith_op_expr   => elem ws arith_op ws elem.
arith_waux_expr => elem ws arith_aux_op ws elem ws arith_op ws elem.
arith_waux_expr => elem ws arith_aux_op ws elem ws arith_op ws elem ws elem.
arith_op        => '=' | "==" | "!=" | "<=" | ">=" | '>' | '<'.
arith_aux_op    => '+' | '-' | '*' | '|' | '&' | '^' | ">>" | "<<".

#
# STATEMENTS
#

# rule and fact statements
rule            => preds ws ":-" ws preds ws '.'.
fact            => pred ws '.'.

preds           => pred preds_rest.
preds_rest      => ',' ws pred preds_rest | null.
pred            => builtin_expr | arith_expr | term.

# nested block statement
block           => '{' prog ws '}'.

# query statement
query           => '!' ws term ws '.' | "!!" ws term ws '.'.

# macro statement
macro           => positive_term ws ":=" ws preds ws '.'.

# grammar production statements
production      => relname ws "=>" ws alts constraints ws '.'.
alts            => alt alts_rest.
alts_rest       => ws alt_separator ws alt alts_rest | null.
alt_separator   => '|'.

# to allow char and string literals having no space in-between
# example: node => 'n''o'"de".
# nt means nonterminal
# t means not nonterminal (terminals, parenthesis/brackets/ +/*)
# alt ending with nonterminal and alt begining with nonterminal requires ws.
# nt_t means starting with nonterminal ending with not nonterminal.
alt             => nt_nt_alt | nt_t_alt | t_nt_alt | t_t_alt.

t_t_alt         => t_t_factor  | t_t_factor ws t_t_alt  | t_t_factor ws nt_t_alt.
t_nt_alt        => t_t_factor ws t_nt_alt | t_t_factor ws nt_nt_alt.
nt_t_alt        => nt_t_factor | nt_nt_factor ws_required nt_t_alt |
			nt_nt_factor ws t_t_alt |
			nt_t_factor ws nt_t_alt |
			nt_t_factor ws t_t_alt.
nt_nt_alt       => nt_nt_factor | nt_nt_factor ws_required nt_nt_alt |
			nt_nt_factor ws t_nt_alt |
			nt_t_factor ws nt_nt_alt |
			nt_t_factor ws t_nt_alt.

t_t_factor      => terminal | terminal ws unot |
			'(' ws alt ws ')' |
			'(' ws alt ws ')' ws unot |
			'{' ws alt ws '}' | '[' ws alt ws ']'.
nt_t_factor     => nonterminal ws unot.
nt_nt_factor    => nonterminal.

unot            => '*' | '+'.
terminal        => quoted_char | string.
nonterminal     => relname.

constraints     => ws ',' ws constraint constraints | null.

constraint      => constraint_elem ws arith_op ws constraint_elem |
			constraint_elem ws arith_aux_op ws constraint_elem ws arith_op ws constraint_elem.
constraint_elem => elem | constraint_builtin.
constraint_builtin => constraint_builtin_name ws '(' ws constraint_arg ws ')'.
constraint_arg  => integer.
constraint_builtin_name => "len" | "substr".

# directive statement
directive       => string_drctv | stdout_drctv | trace_drctv | internal_drctv |
                   domain_drctv | eval_drctv | quote_drctv | codec_drctv |
                   bwd_drctv.
string_drctv    => "@string"   ws_required strdir                       ws '.'.
stdout_drctv    => "@stdout"   ws_required positive_term                ws '.'.
trace_drctv     => "@trace"    ws_required relname                      ws '.'.
internal_drctv  => "@internal" ws_required positive_term                ws '.'.
domain_drctv    => "@domain"   ws_required sym ws integer ws integer    ws '.'.
eval_drctv      => "@eval"     ws_required sym ws sym ws sym ws integer ws '.'.
quote_drctv     => "@quote"    ws_required sym ws sym ws quote_string   ws '.'.
codec_drctv     => "@codec"    ws_required sym ws sym ws sym ws integer ws '.'.
bwd_drctv       => "@bwd"                                               ws '.'.
strdir          => relname ws fname | relname ws string | relname ws cmdline |
                   relname ws cmdlinefile | relname ws positive_term.
fname           => '<' printable_chars '>'.
cmdline         => '$' integer.
cmdlinefile     => '<' '$' integer '>'.

# type definition statement
typedef         => predtypedef | structypedef.
predtypedef     => "predtype" ws_required relname ws predtypedef_args ws '.'.
predtypedef_args=> '('ws')' | '(' ws type ws var (ws ',' ws type ws var)* ws')'.
structypedef    => "struct" ws structypename ws
                   '{' ws membdecl (ws membdecl)* ws '}'.
structypename   => relname.
structype       => relname.
membdecl        => type ws var (ws ',' ws var)* ws '.'.
type            => primtype | structype.
primtype        => simple_type | bitsz_type.
simple_type     => int_type | char_type | sym_type.
int_type        => "int".
char_type       => "char".
sym_type        => "sym".
bitsz_type      => "int:" ws bitsz.
bitsz           => integer.

# state block statement
state_block     => '[' sb_header sb_statements ws ']'.
sb_header       => sb_flipping | sb_nonflipping.
sb_flipping     => sb_label "~:".
sb_nonflipping  => sb_label  ':'.
sb_label        => relname.
sb_statements   => ws sb_statement sb_statements_rest.
sb_statements_rest
                => ws sb_statement sb_statements_rest | null.
sb_statement    => state_block | fact | rule | fof.

# FO formula statement
fof             => preds ws ":-" ws form ws '.'.
form            => form1  (ws causal_op ws form1)*.
form1           => matrix (ws junct_op ws matrix)*.
causal_op       => implies | coimplies.
junct_op        => and | or.
and             => "&&".
or              => "||".
implies         => "->".
coimplies       => "<->".

matrix          => neg_matrix | matrix_block | prefix_decl |
			positive_term |	arith_expr.
neg_matrix      => '~' matrix.
matrix_block    => '{' ws form ws '}'.
prefix_decl     => prefix ws prefix_arg | prefix ws prefix_arg ws form.
prefix          => "forall" | "exists" | "unique".
prefix_arg      => var | relname.

# guard statement
guard_statement => if_then_else | if_then | while_do.
if_then         => "if" ws condition ws "then" ws gs_prog.
if_then_else    => if_then ws "else" ws gs_prog.
while_do        => "while" ws condition ws "do" ws gs_prog.
condition       => form.
gs_prog         => prog | statement | statement0.
statement0      => rule0 | fact0 | fof0.  # statement not terminated by .
rule0           => preds ws ":-" ws preds.
fact0           => pred.
fof0            => preds ws ":-" ws form.

#
# PROGRAM
#
prog            => statements.
statements      => ws statement statements | null.
statement       => block | state_block | directive | query | guard_statement |
                   typedef | fact | rule | production | macro | fof.

#
# start with prog
#
start           => prog ws.

# TODO: negation not supported yet but should be possible to not complete 
# relname if it is a builtin or if it is a simple_type. Something like:
#     relname => ~builtin | ~simple_type.
