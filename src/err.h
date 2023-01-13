// LICENSE
// This software is free for use and redistribution while including this
// license notice, unless:
// 1. is used for commercial or non-personal purposes, or
// 2. used for a product which includes or associated with a blockchain or other
// decentralized database technology, or
// 3. used for a product which includes or associated with the issuance or use
// of cryptographic or electronic currencies/coins/tokens.
// On all of the mentioned cases, an explicit and written permission is required
// from the Author (Ohad Asor).
// Contact ohad@idni.org for requesting a permission. This license may be
// modified over time by the Author.
#ifndef __IDNI__ERR_H__
#define __IDNI__ERR_H__

namespace idni {

#ifdef WITH_EXCEPTIONS
struct parse_error_exception : public virtual std::runtime_error {
	using std::runtime_error::runtime_error;
};

struct runtime_error_exception : public virtual std::runtime_error {
	using std::runtime_error::runtime_error;
};
#endif

const char dot_expected[] = "'.' expected.";
const char sep_expected[] = "Term or ':-' or '.' expected.";
const char unmatched_quotes[] = "Unmatched \"";
const char err_inrel[] = "Unable to read the input relation symbol.";
const char err_src[] = "Unable to read src file.";
const char err_dst[] = "Unable to read dst file.";
const char err_quotes[] = "Expected \".";
const char err_dots[] = "Two consecutive dots, or dot in beginning of document.";
const char err_quote[] = "' should come before and after a single character only.";
const char err_fname[] = "Malformed filename.";
const char err_directive_arg[] = "Invalid directive argument.";
const char err_escape[] = "Invalid escaped character";
const char err_int[] = "Malformed int.";
const char err_lex[] = "Lexer error (please report as a bug).";
const char err_parse[] = "Parser error (please report as a bug).";
const char err_chr[] = "Unexpected character.";
const char err_body[] = "Rule's body expected.";
const char err_prod[] = "Production's body expected.";
const char err_empty_prod[] = "Empty production.";
const char err_constraint_syntax[] = "Constraint Syntax not supported.";
const char err_start_sym[] = "Expected a term to be fed to the start symbol.";
const char err_term_or_dot[] = "Term or dot expected.";
const char err_close_curly[] = "'}' expected.";
const char err_fnf[] = "File not found.";
const char err_rule_dir_prod_expected[] = "Rule or production or directive expected.";
const char err_paren[] = "Unbalanced parenthesis.";
const char err_relsym_expected[] = "Expected relation name in beginning of term.";
const char err_paren_expected[] = "Expected parenthesis after a nonzero arity relation symbol.";
const char err_head[] = "Expected 'else' or dot or comma or update operator.";
const char err_digit[] = "Symbol name cannot begin with a digit.";
const char err_var_relsym[] = "Relation symbol cannot be a variable.";
const char err_proof[] = "Proof extraction yet unsupported for programs with negation or deletion.";
const char err_directive_elem[] = "Universe element in directive not appearing in program.";
const char err_goalsym[] = "Goal symbol not appearing in program.";
const char err_goalarity[] = "Goal arity larger than the program's.";
const char err_num_cmdline[] = "Program expects more command line arguments.";
const char err_one_input[] = "Only one input string allowed given grammar.";
const char err_str_defined[] = "String already defined.";
const char warning_empty_domain[] = "Warning: empty domain, adding dummy element.";
const char err_trace_rel[] = "Trace directive has to be followed by a relation symbol.";
const char err_directive[] = "Directives can be @string or @stdout or @trace.";
const char err_stdout[] = "Expected term after @stdout.";
const char err_rel_expected[] = "Expected relation symbol.";
const char err_len[] = "Taking the length of an unknown string.";
const char err_comment[] = "Unfinished comment.";
const char err_eof[] = "Unexpected end of file.";
const char err_eq_expected[] = "Expected =/!= in the middle of term.";
const char err_leq_expected[] = "Expected <=/> in the middle of term.";
const char err_3_els_expected[] = "Expected 3 elements in the term.";
const char err_builtin_expected[] = "Expected builtin name in the beginning of term.";
const char err_contradiction[] = "unsat (contradiction).";
const char err_infloop[] = "unsat (infinite loop).";
const char err_domain_sym[] = "Expected symbol denoting the relation associated with a domain.";
const char err_limit_num[] = "Expected number denoting tuple element domain size.";
const char err_arity_num[] = "Expected number denoting maximum tuple length.";
const char err_eval_sym[] = "Expected symbol denoting the relation associated with an interpreter.";
const char err_quote_sym[] = "Expected symbol denoting the relation associated with a quotation.";
const char err_timeout_num[] = "Expected number denoting number of program steps to simulate.";
const char err_quote_str[] = "Expected quotation containing a TML program.";
const char err_codec_sym[] = "Expected symbol denoting the relation associated with a codec.";
const char err_internal_term[] = "Expected term whose relation is to be marked as internal.";
const char err_x_escape[] = "Wrong \\x character escape. Use values between: \\x00 and \\xFF.";
const char err_u_escape[] = "Wrong \\u character escape. Use values between: \\u0000 and \\uFFFF.";
const char err_neg_fact[] = "Facts cannot be negated.";

} // idni namespace
#endif // __IDNI__ERR_H__
