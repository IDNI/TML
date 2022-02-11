# parsing not ok:
#@string str <../intro/03_RELATIONS.tml>.# killed but w/ less comments parses ok

# parsing ok:
#@string str <../intro/01_intro.tml>.
#@string str <../intro/02_FACTS.tml>.
#@string str <../intro/04_ARITY.tml>.
#@string str <../intro/05_RULES.tml>.
#@string str <../intro/06_VARIABLES.tml>.
#@string str <../intro/07_AND_OR.tml>.
#@string str <../intro/08_RECURSION.tml>.
#@string str <../intro/09_TRANSITIVE_CLOSURE.tml>.
#@string str <../intro/10_NEGATION.tml>.
#@string str <../intro/11_DELETION.tml>.
#@string str <../intro/12_family.tml>.
#@string str <../intro/13_armageddon.tml>.
#@string str <../intro/14_UNSAT.tml>.
@string str <../intro/15_DYCKs_LANGUAGE.tml>.

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

# whitespace
eol             => '\r' | '\n'.    # TODO: include EOF too
ws_comment      => '#' eol | '#' printable_chars eol.
ws_required     => wa_space ws | ws_comment ws.
ws              => ws_required | null.

# Important notice: ws between statements is already covered.
# Starting or/and ending a production rule with "ws" can cause ambiguity!

#
# common elements
#
chars           => wa_alpha | wa_alpha chars1 | '_' chars1.
chars1          => wa_alnum | wa_alnum chars1 | '_' chars1.
printable_chars => wa_printable printable_chars_rest.
printable_chars_rest =>
                   wa_printable printable_chars_rest | null.
integer         => wa_digit+.

# elements
sym             => chars.
var             => '?' chars.
number          => integer.
# quoted char should allow all values, not just wa_printable.
quoted_char     => "'"   wa_printable "'" | quoted_char_esc | empty_char.
quoted_char_esc => "'\\" wa_printable "'".
empty_char      => "''".  # I don't think we support this in TML at the moment.

string          => '"' printable_chars '"' | empty_string.
empty_string    => '"' '"'.

# term
term            => relname args.
negative_term   => '~' ws term.
args            => ws '(' elems ws ')' | ws '(' ws ')' | null.
elems           => elem | elem ws_required elems_rest.
elems_rest      => elem | elem ws_required elems_rest | args.
elem            => sym | var | number | quoted_char | string.
relname         => sym.

#
# STATEMENTS
#

# rule and fact statements
rule            => preds ws ":-" ws preds ws '.'.
fact            => pred ws '.'.

preds           => pred preds_rest.
preds_rest      => ',' ws pred preds_rest | null.
pred            => term | negative_term.

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

# directive
directive       => "@string" ws_required strdir  ws '.' |
                   "@stdout" ws_required term    ws '.' |
                   "@trace"  ws_required relname ws '.' |
                   "@bwd"    ws '.'.
strdir          => relname ws fname | relname ws string | relname ws cmdline |
                   relname ws term.
fname           => '<' printable_chars '>'.
cmdline         => '$' wa_digits.

#
# PROGRAM
#

prog            => statements.
statements      => ws statement statements | null.
statement       => directive | fact | rule | production.

#
# start with prog
#
start           => prog ws.
