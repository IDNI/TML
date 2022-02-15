@string str <$1>.

#
## whitespace
#
eol             => '\r' | '\n'. # TODO: include EOF
ws_comment      => '#' eol | '#' printable_chars eol .
ws_required     => space ws | ws_comment ws.
ws              => ws_required | null.

# Important notice: ws between statements is already covered.
# Starting or/and ending a production rule with "ws" can cause ambiguity!

#
## character groups and definitions
#
hex_digit       => digit | 'A' | 'B' | 'C' | 'D' | 'E' | 'F' |
                           'a' | 'b' | 'c' | 'd' | 'e' | 'f'.
hex_escape      => "\x" hex_digit hex_digit.
unicode_escape  => "\u" hex_digit hex_digit hex_digit hex_digit.
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

quoted_char     => "'"   char "'" | quoted_char_esc | empty_char.
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
positive_term   => relname args.
negative_term   => '~' ws relname args.
args_required   => ws '(' ws elems ws ')' | ws '(' ws ')'.
args            => ws '(' ws elems ws ')' | ws '(' ws ')' | null.
elems           => elem | elem ws_required elems_rest |
                   relname args_required | relname args_required ws elems_rest.
elems_rest      => elem args | elem ws_required elems_rest | args.
elem            => sym | var | number | quoted_char | string | char_builtin.
relname         => sym.

#
## builtins
#
builtin_expr    => builtin_prefixes ws builtin_term.
builtin_prefixes=> builtin_prefix | builtin_prefix ws builtin_prefixes.
builtin_prefix  => "renew" | "forget".
builtin_term    => builtin args.
builtin         => "halt" | "error" | "false" | "forget" | "rnd" | "count" | 
                   "bw_and" | "bw_or" | "bw_xor" | "bw_not" |
		   "pw_add" | "pw_mult" |
		   "leq" |
                   "print" | "println" | "println_to" | "print_to" |
		   "print_delim" | "println_delim" |  "print_to_delim" |
		   "println_to_delim" | 
		   "js_eval".
char_builtin    => "alpha" | "alnum" | "digit" | "space" | "printable".

#
## arithmetic expression
#
arith_expr      => arith_expr1 ws arith_eq_op ws elem arith_ext.
arith_expr1     => '~' ws elem |
                          elem |
                   '~' ws elem ws arith_op ws arith_expr1 |
                          elem ws arith_op ws arith_expr1.
arith_eq_op     => '=' | "==" | "!=" | "<=" | ">=" | '>' | '<'.
arith_op        => '+' | '-' | '*' | '|' | '&' | '^' | ">>" | "<<".
arith_ext       => ws elem | null.

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
alts_rest       => ws '|' ws alt ws alts_rest | null.
alt             => factor | factor ws factors_rest.
factors_rest    => factor | factor ws factors_rest.
factor          => factor_unot | factor_nonunot.
factor_unot     => factor_unotable ws unot.
factor_unotable => terminal | nonterminal | '(' ws alts ws ')'.
factor_nonunot  => factor_unotable |        '{' ws alts ws '}' |
                                            '[' ws alts ws ']'.
unot            => '*' | '+'.
terminal        => quoted_char | string.
nonterminal     => relname.

constraints     => ws ',' ws constraint constraints | null.

constraint      => constraint1 ws arith_eq_op ws constraint_expr.
constraint1     => constraint_expr | constraint_expr ws arith_op ws constraint1.
constraint_expr => elem | constraint_fn.
constraint_fn   => constraint_fn_name ws '(' ws constraint_arg ws ')'.
constraint_arg  => integer.
constraint_fn_name => "len" | "substr".

# directive statement
directive       => "@string"   ws_required strdir                       ws '.' |
                   "@stdout"   ws_required positive_term                ws '.' |
                   "@trace"    ws_required relname                      ws '.' |
		   "@internal" ws_required positive_term                ws '.' |
		   "@domain"   ws_required sym ws integer ws integer    ws '.' |
		   "@eval"     ws_required sym ws sym ws sym ws integer ws '.' |
		   "@quote"    ws_required sym ws sym ws quote_string   ws '.' |
		   "@codec"    ws_required sym ws sym ws sym ws integer ws '.' |
                   "@bwd"                                               ws '.'.
strdir          => relname ws fname | relname ws string | relname ws cmdline |
                   relname ws positive_term.
fname           => '<' printable_chars '>'.
cmdline         => '$' integer.

# type definition statement
typedef         => predtypedef | structypedef.
predtypedef     => "predtype" ws_required relname ws predtypedef_args ws '.'.
predtypedef_args=> '(' ws ')' | '(' ws type ws var (ws ',' ws type ws var)* ws ')'.
structypedef    => "struct" ws structype ws
                   '{' ws typevardecl (ws typevardecl)* ws '}'.
structype       => relname.
typevardecl     => type ws var (ws ',' ws var)* ws '.'.
type            => primtype | structype.
primtype        => "int:" ws bitsz | "int" | "char" | "sym".
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
fof             => preds ws ":-" ws form0 ws '.'.
form0           => form01 | form1 ws bop ws form.
form01          => matrix_block | matrix ws bop1 ws form1.
form            => form1 | form1 ws bop ws form.
form1           => matrix | matrix ws bop1 ws form1. 
bop             => '|'  | "&".
bop1            => "->" | "<->" | logic_op.
matrix          => term | arith_expr | logic_expr | var | matrix_block.
matrix_block    => '~' ws '{' ws form ws '}' |
                          '{' ws form ws '}' |
                   '~' ws prefixdecl ws '{' ws form ws '}' |
                          prefixdecl ws '{' ws form ws '}'.
prefixdecl      => prefix ws prefixarg ws prefixdecl | prefix ws prefixarg.
prefixarg       => var | sym.
prefix          => "forall" | "exists" | "unique".
logic_expr      => elem ws logic_op ws logic_expr1.
logic_expr1     => elem | logic_expr.
logic_op        => "||" | "&&".

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
fof0            => preds ws ":-" ws form0.

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
