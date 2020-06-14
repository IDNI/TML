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
test pe(wstring prog, wstring err, long line, long chr, wstring to) {
	std::wstringstream ws; ws << L"Parse error: \"" << err
		<< L"\" at " << line << L':' << chr;
	if (to != L"") ws << " close to \"" << to << "\"";
	std::wstring expected = ws.str();
	auto got_output = [] () {
		wchar_t t[256];
		wistringstream is(::outputs::get(L"error")->read());
		is.getline(t, 256);
		return wstring(t);
	};
	return [expected, &got_output, prog] () -> int {
		wstring got, prg(prog);
		outputs *oldoo = outputs::in_use();
		outputs oo; oo.use(); oo.init_defaults();
		driver d(prog, ::options({ "--error", "@buffer",
			"--no-output", "--no-debug", "--no-info" }, &oo));
		wchar_t t[256];
		wistringstream is(oo.get(L"error")->read());
		is.getline(t, 256);
		got = wstring(t);
		oldoo->use();
		if (got.length() > 0) {
			if (got.compare(expected)) {
				size_t p = 0;
				while ((p=prg.find(L"\n",p)) != wstring::npos) {
					prg.replace(p, 1, L"\\n");
					p += 2;
				}
				wostringstream os;
				os << L"parse error fail (#" << n << ")\n"
					<< L"\tprog: '" << prog     << L"'\n"
					<< L"\tgot:  '" << got      << L"'\n"
					<< L"\texp:  '" << expected << L"'\n";
				return fail(os.str());
			} // else wcout << L"ok " << n << L"\n";
		} else return fail(L"no error", n);
		return ok();
	};
}

int main() {
	setlocale(LC_ALL, "");
	outputs oo;
	vector<test> tests = {
		pe(L"a\n. /* aaa",       err_comment,          2,  3, L""),
		pe(L"\"",                unmatched_quotes,     1,  1, L"\""),
		pe(L"\"\\'\"",           err_escape,           1,  3, L"'\""),
		pe(L"<",                 err_eof,              1,  2, L"<"),
		pe(L"'\\0'",             err_escape,           1,  3, L"0'"),
	//  5
		pe(L"\n'c.",             err_quote,            2,  3, L"."),
		pe(L"a",                 err_eof,              1,  2, L"a"),
		pe(L"\na\n(.",           err_paren,            3,  1, L"."),
		pe(L"@trace 1",          err_trace_rel,        1,  8, L"1"),
		pe(L"@trace r a",        dot_expected,         1, 10, L"a"),
	// 10
		pe(L"@bwd a",            dot_expected,         1,  6, L"a"),
		pe(L"@stdout.",          err_stdout,           1,  8, L"."),
		pe(L"@stdout str1(),",   dot_expected,         1, 15, L","),
		pe(L"@dummy.",           err_directive,        1,  2, L"dummy"),
		pe(L"@string 5",         err_rel_expected,     1,  9, L"5"),
	// 15
		pe(L"@string s <a> 6",   dot_expected,         1, 12, L"<"),
		pe(L"@string s ;",       err_directive_arg,    1, 11, L";"),
		pe(L"@string s stdin  ", dot_expected,         1, 16, L"stdin"),
		pe(L"a",                 err_eof,              1,  2, L"a"),
		pe(L"1.",                err_relsym_expected,  1,  1, L"1"),
	// 20
		pe(L"a 3 f.",            err_paren_expected,   1,  6, L"."),
		pe(L"a(.",               err_paren,            1,  2, L"."),
		pe(L"a((((()(()())))).", err_paren,            1,  1, L"a"),
		pe(L"a;",                err_head,             1,  2, L";"),
		pe(L"a:-.",              err_body,             1,  4, L"."),
	// 25
		pe(L"b;",                err_head,             1,  2, L";"),
		pe(L"a => e1 e2",        err_prod,             1,  6, L"e1"),
		pe(L":-a.",        err_rule_dir_prod_expected, 1,  1, L":-"),
		pe(L"{ a(). ",           err_close_curly,      1,  7, L"."),
		pe(L":a",                err_chr,              1,  2, L"a"),
	// 30
		pe(L"1a",                err_int,              1,  1, L"1a"),
		pe(L"?(",                err_chr,              1,  2, L"("),
		pe(L"{{",                err_parse,            1,  2, L"{" )
		// TODO: pe(L"",         err_term_or_dot,      1,  1, L""),
	};
	return run(tests, L"parse errors");
}
