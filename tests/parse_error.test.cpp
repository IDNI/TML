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
#include <sstream>

#include "../src/driver.h"
#include "../src/err.h"

#include "simple_test.h"

using namespace std;

// parse error test factory
//	prog      - input program
//	err       - expected parse error
//	line, chr - expected error position
//	to        - expected "close to"
test pe(std::string prog, std::string err, long line, long chr, std::string to) {
	std::stringstream ss; ss << "Parse error: \"" << err
		<< "\" at " << line << ':' << chr;
	if (to != "") ss << " close to \"" << to << "\"";
	std::string expected = ss.str();
	auto got_output = [] () {
		syschar_t t[256];
		istringstream_t is(::outputs::get("error")->read());
		is.getline(t, 256);
		return ws2s(t);
	};
	return [expected, &got_output, prog] () -> int {
		string got, prg(prog);
		outputs *oldoo = outputs::in_use();
		outputs oo; oo.use(); oo.init_defaults();
		inputs ii;
		try {
			driver d(prog, ::options(strings{ "--error", "@buffer",
			"--no-output", "--no-debug", "--no-info" }, &ii, &oo));
		} catch (std::exception& e) {
			return fail(e.what());
		}
		syschar_t t[256];
		istringstream_t is(oo.get("error")->read());
		is.getline(t, 256);
		got = ws2s(t);
		oldoo->use();
		if (got.length() > 0) {
			if (got.compare(expected)) {
				size_t p = 0;
				while ((p=prg.find("\n", p)) != string::npos) {
					prg.replace(p, 1, "\\n");
					p += 2;
				}
				ostringstream os;
				os << "parse error fail (#" << n << ")\n"
					<< "\tprog: '" << prog     << "'\n"
					<< "\tgot:  '" << got      << "'\n"
					<< "\texp:  '" << expected << "'\n";
				return fail(os.str());
			} //else COUT << "ok " << n << "\n";
		} else return fail("no error", n);
		return ok();
	};
}

int main() {
	setlocale(LC_ALL, "");
	outputs oo;
	vector<test> tests = {
		pe("a\n. /* aaa",       err_comment,          2,  3, ""),
		pe("\"",                unmatched_quotes,     1,  1, "\""),
		pe("\"\\'\"",           err_escape,           1,  3, "'\""),
		pe("<",                 err_eof,              1,  2, "<"),
		pe("'\\0'",             err_escape,           1,  3, "0'"),
	//  5
		pe("\n'c.",             err_quote,            2,  3, "."),
		pe("a",                 err_eof,              1,  2, "a"),
		pe("\na\n(.",           err_paren,            3,  1, "."),
		pe("@trace 1",          err_trace_rel,        1,  8, "1"),
		pe("@trace r a",        dot_expected,         1, 10, "a"),
	// 10
		pe("@bwd a",            dot_expected,         1,  6, "a"),
		pe("@stdout.",          err_stdout,           1,  8, "."),
		pe("@stdout str1(),",   dot_expected,         1, 15, ","),
		pe("@dummy.",           err_directive,        1,  2, "dummy."),
		pe("@string 5",         err_rel_expected,     1,  9, "5"),
	// 15
		pe("@string s <a> 6",   dot_expected,         1, 12, "<a> 6"),
		pe("@string s ;",       err_directive_arg,    1, 11, ";"),
		pe("@string s stdin  ", dot_expected,         1, 16, "stdin  "),
		pe("a",                 err_eof,              1,  2, "a"),
		pe("1.",                err_relsym_expected,  1,  1, "1."),
	// 20
		pe("a 3 f.",            err_paren_expected,   1,  6, "."),
		pe("a(.",               err_paren,            1,  2, "."),
		pe("a((((()(()())))).", err_paren,            1,  1, "a((((()(()()))))."),
		pe("a;",                err_head,             1,  2, ";"),
		pe("a:-.",              err_body,             1,  4, "."),
	// 25
		pe("b;",                err_head,             1,  2, ";"),
		pe("a => e1 e2",        err_prod,             1,  6, "e1 e2"),
		pe(":-a.",        err_rule_dir_prod_expected, 1,  1, ":-a."),
		pe("{ a(). ",           err_close_curly,      1,  7, ". "),
		pe(":a",                err_chr,              1,  2, "a"),
	// 30
		pe("1a",                err_int,              1,  1, "1a"),
		pe("?(",                err_chr,              1,  2, "("),
		pe("{{",                err_parse,            1,  2, "{"),
		pe("b:-a",              err_eof,              1,  5, "a")
		// TODO: pe("",         err_term_or_dot,      1,  1, ""),
	};
	return run(tests, "parse errors");
}
