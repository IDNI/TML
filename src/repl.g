@string str "s 1
".

printable_chars => printable printable_chars | printable.
num             => digit num | digit.
ws              => space ws | space | null.
eol             => '\n' | '\r'.

cmd_no_arg      => '?' | 'h' | 'i' | 'p' | 'l' | 'r' | 'c' | 's' | 'd' |
	           "dict" | "gc" | "cu" | "ps" | "pu" | "ar" | "ap" | "ai" |
		   "ils" | 'b' | "reparse" | "restart" | "reset" | "quit".
cmd_num_arg     => 'l' | 's' | 'b'.

command         => cmd_num_arg ws num ws eol | cmd_no_arg ws eol.

repl_input      => command. # | <tml_rule.g>.
