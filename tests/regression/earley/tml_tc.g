@string str <../intro/09_TRANSITIVE_CLOSURE.tml>.

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
quoted_char     => '\'' wa_printable '\'' | "'\\" wa_printable '\'' | "''".
string          => '"' printable_chars '"'.

# term
term            => relname args.
negative_term   => '~' ws term.
args            => '(' ws args1 ws ')' | null.
args1           => elem ws args1 | args.
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

#
# PROGRAM
#

prog            => statements.
statements      => ws statement statements | null.
statement       => fact | rule.

#
# start with prog
#
start           => prog ws.
