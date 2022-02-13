@string str <tml_earley.g>.  
# workarounds for space, digit, alpha, alnum and printable char builtins
wa_space        => ' ' | '\t' | '\r' | '\n'.
wa_digit        => '0' | '1' | '2' | '3' | '4' | '5' | '6' | '7' | '8' | '9'.
wa_alpha        => 'A' | 'a' | 'B' | 'b' | 'C' | 'c' | 'D' | 'd' | 'E' | 'e' |
                   'F' | 'f' | 'G' | 'g' | 'H' | 'h' | 'I' | 'i' | 'J' | 'j' |
                   'K' | 'k' | 'L' | 'l' | 'M' | 'm' | 'N' | 'n' | 'O' | 'o' |
                   'P' | 'p' | 'Q' | 'q' | 'R' | 'r' | 'S' | 's' | 'T' | 't' |
                   'U' | 'u' | 'V' | 'v' | 'W' | 'w' | 'X' | 'x' | 'Y' | 'y' |
                   'Z' | 'z'.
wa_alnum        => wa_digit | wa_alpha.
wa_printable    => wa_alnum  | ' ' | '!' | '"' | '#' | '$'  | '%' | '&' | '\'' |
                   '(' | ')' | '*' | '+' | ',' | '-' | '.'  | '/' | ':' | ';'  |
                   '<' | '=' | '>' | '?' | '@' | '[' | '\\' | ']' | '^' | '_'  |
                   '`' | '{' | '|' | '}' | '~'.
#
# whitespace
eol             => '\r' | '\n'.    # TODO: include EOF too
ws_comment      => '#' eol | '#' printable_chars eol .
ws_required     => wa_space ws | ws_comment ws.
ws              => ws_required | null.
#
# Important notice: ws between statements is already covered.
# Starting or/and ending a production rule with "ws" can cause ambiguity!
#
#
# common elements
#
chars           => wa_alpha | wa_alpha chars1 | '_' chars1.
chars1          => wa_alnum | wa_alnum chars1 | '_' chars1.
printable_chars => wa_printable printable_chars_rest.
printable_chars_rest =>
                   wa_printable printable_chars_rest | null.
integer         => wa_digit+.
#
# elements
sym             => chars.
var             => '?' chars.
number          => integer.
# quoted char should allow all values, not just wa_printable.
quoted_char     => "'"   wa_printable "'" | quoted_char_esc | empty_char.
quoted_char_esc => "'\\" wa_printable "'".
empty_char      => "''".  # I don't think we support this in TML at the moment.
#
string          => '"' printable_chars '"' | empty_string.
empty_string    => '"' '"'.
#
# term
term            => relname args.
negative_term   => '~' ws term.
args            => ws '(' elems ws ')' | ws '(' ws ')' | null.
elems           => elem | elem ws_required elems_rest.
elems_rest      => elem | elem ws_required elems_rest | args.
elem            => sym | var | number | quoted_char | string.
relname         => sym.
#
#
# STATEMENTS
#
#
# rule and fact statements
rule            => preds ws ":-" ws preds ws '.'.
fact            => pred ws '.'.
#
preds           => pred preds_rest.
preds_rest      => ',' ws pred preds_rest | null.
pred            => term | negative_term.
#
# nested block statement
block           => '{' prog ws '}'.
#
# query statement
query           => '!' ws term | "!!" ws term.
#
# macro statement
macro           => term ws ":=" ws preds ws '.'.
#
# grammar production statements
production      => relname ws "=>" ws alts ws '.'.
alts            => alt alts_rest.
alts_rest       => ws '|' ws alt ws alts_rest | null.
alt             => factor factors_rest.
factors_rest    => ws_required factor factors_rest | null.
factor          => factor_unot | factor_nonunot.
factor_unot     => factor_unotable ws unot.
factor_unotable => terminal | nonterminal | '(' ws alts ws ')'.
factor_nonunot  => factor_unotable |        '{' ws alts ws '}' |
                                            '[' ws alts ws ']'.
unot            => '*' | '+'.
terminal        => quoted_char | string.
nonterminal     => relname.
#
# directive statement
directive       => "@string" ws_required strdir  ws '.' |
                   "@stdout" ws_required term    ws '.' |
                   "@trace"  ws_required relname ws '.' |
                   "@bwd"    ws '.'.
strdir          => relname ws fname | relname ws string | relname ws cmdline |
                   relname ws term.
fname           => '<' printable_chars '>'.
cmdline         => '$' integer.
#
# type definition statement
typedef         => predtypedef | structypedef.
predtypedef     => "predtype" relname '('  type var (',' type var)* ')'.
structypedef    => "struct" structtype '{' typevardecl ('.' typevardecl)* '}'.
structype       => relname.
typevardecl     => type var (',' var)* '.'.
type            => primtype | structype.
primtype        => "int" | "int:" bitsz | "char" | "symb".
bitsz           => integer.
#
# state block statement
state_block     => '[' sb_header sb_statements ws ']'.
sb_header       => sb_flipping | sb_nonflipping.
sb_flipping     => sb_label "~:".
sb_nonflipping  => sb_label  ':'.
sb_label        => relname.
sb_statements   => ws sb_statement sb_statements_rest.
sb_statements_rest
                => ws sb_statement sb_statements_rest | null.
sb_statement    => query | directive | rule | fact | fof | production |
                   typedef | macro | sb.
#
# FO formula statement
fof             => term ws ":=" ws form ws '.'.
form            => form1 | form1 bop form.
form1           => matrix | matrix bop1 form1. 
bop             => '|'  | '&'.
bop1            => "->" | "<->".
matrix          => term | '~' term | '{' form '}' | '~' '{' form '}' |
                   prefixdecl '{' form '}' | '~' prefixdecl '{' form '}'.
prefixdecl      => prefix ws identifier ws prefixdecl | prefix ws identifier.
prefix          => "forall" | "exists" | "unique".
#
# guard statement
guard_statement => if_then_else | if_then | while_do.
if_then         => "if" ws condition ws "then" ws prog.
if_then_else    => if_then ws "else" ws prog.
while_do        => "while" ws condition ws "do" ws prog.
condition       => form.
#
#
# PROGRAM
#
#
prog            => statements.
statements      => ws statement statements | null.
statement       => directive | block | query | fact | rule | production | macro.
#
#
# start with prog
#
start           => prog ws.
