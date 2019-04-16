{
@string str <tml.g>.
eol => '\r' | '\n' | ''.
printable_chars => printable printable_chars | null.
ws =>	space ws | ws '#' printable_chars eol ws | null.
	#eol | ws "/*" ws printable_chars ws "*/" ws | null.
chars => alpha chars1 | '_' chars1.
chars1=> alnum chars1 | '_' chars1 | null.
identifier => sym | var.
var => '?' chars.
sym => chars.
relname => sym.
quoted_char => 	'\'' printable '\'' | "'\\r'" | "'\\n'"
		| "'\\t'" | "'\\''" | "''".
fname => '<' printable_chars '>' ws.
string => '"' printable_chars '"' ws.
}
{
#"p(?x ?y) :=forall ?x (exists ?y (unique ?z ((e(?x ?y) and e(?y ?z)) or e(?x ?z)))).  S => S | null.  ".
#@bwd.

args => identifier ws args | null.
terminal => quoted_char | string.
nonterminal => relname.
cmdline => '$' digits ws.
query => '!' ws term | "!!" ws term.

term => relname args.
pred => term | '~' ws term ws.
args => ws '(' ws args1 ws ')' ws | null.
args1 => identifier ws args1 ws | args | null.

directive =>	ws "@string" space ws strdir ws '.' ws |
		ws "@stdout" space ws term ws '.' ws |
		ws "@trace" space ws relname ws '.' ws |
		ws "@bwd" ws '.' ws.
strdir => relname ws fname | relname ws string | relname ws cmdline | relname ws term.

production => relname ws "=>" ws alt ws alts ws '.' ws.
alt =>	terminal ws alt ws | nonterminal ws alt ws | null.
alts => null | '|' ws alt ws alts ws.

fact => pred '.' ws.
preds => ws pred preds_rest.
preds_rest => ws ',' ws pred ws preds_rest | null.
rule => ws preds ws ":-" ws preds ws '.' ws.

fof => term ws ':' '=' ws form ws '.' ws.
form => term |
	ws prefix ws var ws '(' ws form ws ')' ws |
	ws '(' ws form ws ')' ws "and" ws '(' ws form ws ')' ws |
	ws '(' ws form ws ')' ws "or" ws '(' ws form ws ')' ws |
	ws "not" '(' ws form ws ')' ws |
	ws term ws "and" ws '(' ws form ws ')' ws |
	ws term ws "or" ws '(' ws form ws ')' ws |
	ws "not" '(' ws form ws ')' ws |
	ws term ws "and" ws term ws |
	ws term ws "or" ws term ws |
	ws "not" term ws |
	ws '(' ws form ws ')' ws "and" ws term ws |
	ws '(' ws form ws ')' ws "or" ws term ws.
prefix => "forall" | "exists" | "unique".

prog => directive S | rule S | production S | fof S | query S | null.
S => ws '{' ws prog ws '}' ws S | ws prog ws | null.

#!! S(0 ?x).
}
{
	~S(?x?x):-S(?x?x).
	~prog(?x?x):-prog(?x?x).
}
