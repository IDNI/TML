{
@string progs <tml.g>.
@trace W.

S => ws '{' ws prog ws '}' ws S | null.
prog => directive prog | production prog | rule prog | fof prog | query prog | null.
directive =>	"@string" space ws strdir ws '.' ws |
		"@stdout" space ws term ws '.' ws |
		"@trace" space ws relname ws '.' ws.
production => relname ws "=>" ws alt alts ws '.' ws.
alt =>	ws terminal ws alt | ws nonterminal ws alt | null.
alts => null | ws '|' ws alt ws alts.
terminal => '\'' printable '\'' | "'\\''" | string.
nonterminal => relname.
fact => term ws '.' ws.
terms => ws term terms_rest.
terms_rest => ws ',' ws term ws terms_rest | null.
rule => ws terms ws ":-" ws terms ws '.' ws.
strdir => relname ws fname | relname ws string | relname ws cmdline | relname ws term.
query => '!' ws term | "!!" ws term.
fname => '<' printable_chars '>' ws.
string => '"' printable_chars '"' ws.
printable_chars => printable printable_chars | null.
cmdline => '$' digits ws.
term => ws relname ws args.
args => ws '(' ws args1 ws ')' ws | null.
args1 => args_var | args_sym | args.
args_sym => sym | sym args | sym args_sym1.
args_sym1 => 	space ws sym |
		space ws sym args |
		space ws sym args_var |
		space ws sym args_sym1 | null.
args_var => 	var |
		var ws args_var |
		var ws args |
		var args_sym1.

fof => ws pred ws ":=" ws form ws '.' ws.
pred => chars ws '(' ws args ws ')' ws.
identifier => chars | var.
args => identifier ws args | null.
var => '?' chars.
sym => chars.
relname => sym.
chars => alpha chars1 | '_' chars1.
chars1=> alnum chars1 | '_' chars1 | null.
ws => space ws | '#' printable_chars eol | null.
eol => '\r' | '\n' | ''.
form => ws prefix ws var ws '(' ws form ws ')' ws |
	ws '(' ws form ws ')' ws "and" ws '(' ws form ws ')' ws |
	ws '(' ws form ws ')' ws "or" ws '(' ws form ws ')' ws |
	ws "not" '(' ws form ws ')' ws |
	ws pred ws "and" ws '(' ws form ws ')' ws |
	ws pred ws "or" ws '(' ws form ws ')' ws |
	ws "not" '(' ws form ws ')' ws |
	ws pred ws "and" ws pred ws |
	ws pred ws "or" ws pred ws |
	ws "not" pred ws |
	ws '(' ws form ws ')' ws "and" ws pred ws |
	ws '(' ws form ws ')' ws "or" ws pred ws |
	pred.
prefix => "forall" | "exists" | "unique".
}
{
	~S(?x ?x) :- S(?x ?x).
	~chars1(?x ?x) :- chars1(?x ?x).
}
