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

using namespace std;

size_t f = 0; // fails
size_t n = 0; // current test no.

struct pe { // parse error test
	wstring prog;   // input program
	wstring err;    // parse error
	long line, chr; // error position
	wstring to;     // close to
	wstring expected() const {
		std::wstringstream ws; ws << L"Parse error: \"" << err
			<< L"\" at " << line << L':' << chr;
		if (to != L"") ws << " close to \"" << to << "\"";
		return ws.str();
	}
	wstring got_output() const {
		wchar_t t[256];
		wistringstream is(::output::read(L"error"));
		is.getline(t, 256);
		return wstring(t);
	}
	void run() {
		++n;
		wstring got, exp = expected();
		driver d(prog, ::options(vector<string>{ "--error", "@buffer",
				"--no-output", "--no-debug", "--no-info" }));
		got = got_output();
		if (got.length() > 0) {
			if (got.compare(exp)) {
				size_t p = 0;
				while ((p=prog.find(L"\n",p)) != wstring::npos){
					prog.replace(p, 1, L"\\n");
					p += 2;
				}
				wcout << L"FAIL (#" << n << ")"  << endl;
				wcout << L"\tprog: '" << prog << L"'" << endl;
				wcout << L"\texp:  '" << exp  << L"'" << endl;
				wcout << L"\tgot:  '" << got  << L"'" << endl;
				f++;
			} else {
				wcout << L"OK (#" << n << ")"  << endl;
			}
		} else {
			wcout << L"no error (#" << n << ")" << endl;
		}
	}
};

vector<pe> tests = {
	pe{ L"a\n. /* aaa",       err_comment,                2,  3, L"" },
	pe{ L"\"",                unmatched_quotes,           1,  1, L"\"" },
	pe{ L"\"\\'\"",           err_escape,                 1,  3, L"'\"" },
	pe{ L"<",                 err_fname,                  1,  1, L"<" },
	pe{ L"'\\0'",             err_escape,                 1,  3, L"0'" },
//  5
	pe{ L"\n'c.",             err_quote,                  2,  3, L"." },
	pe{ L"a",                 err_eof,                    1,  2, L"a" },
	pe{ L"\na\n(.",           err_paren,                  3,  1, L"." },
	pe{ L"@trace 1",          err_trace_rel,              1,  8, L"1" },
	pe{ L"@trace r a",        dot_expected,               1, 10, L"a" },
// 10
	pe{ L"@bwd a",            dot_expected,               1,  6, L"a" },
	pe{ L"@stdout.",          err_stdout,                 1,  8, L"." },
	pe{ L"@stdout str1(),",   dot_expected,               1, 15, L"," },
	pe{ L"@dummy.",           err_directive,              1,  2, L"dummy" },
	pe{ L"@string 5",         err_rel_expected,           1,  9, L"5" },
// 15
	pe{ L"@string s <a> 6",   dot_expected,               1, 14, L"<a>" },
	pe{ L"@string s ;",       err_directive_arg,          1, 11, L";" },
	pe{ L"@string s stdin  ", dot_expected,               1, 16, L"stdin" },
	pe{ L"a",                 err_eof,                    1,  2, L"a" },
	pe{ L"1.",                err_relsym_expected,        1,  1, L"1" },
// 20
	pe{ L"a 3 f.",            err_paren_expected,         1,  6, L"." },
	pe{ L"a(.",               err_paren,                  1,  2, L"." },
	pe{ L"a((((()(()())))).", err_paren,                  1,  1, L"a" },
	pe{ L"a;",                err_head,                   1,  2, L";" },
	pe{ L"a:-.",              err_body,                   1,  4, L"." },
// 25
	pe{ L"b;",                err_head,                   1,  2, L";" },
	pe{ L"a => e1 e2",        err_prod,                   1,  6, L"e1" },
	pe{ L":-a.",              err_rule_dir_prod_expected, 1, 1, L":-" },
	pe{ L"{ a(). ",           err_close_curly,            1,  7, L"." },
	pe{ L":a",                err_chr,                    1,  2, L"a" },
// 26
	pe{ L"1a",                err_int,                    1,  1, L"1a" },
	pe{ L"?(",                err_chr,                    1,  2, L"(" },

	//TODO: pe{ L"",          err_term_or_dot,            1,  1, L"" },
	//pe{ L"", L"no error", 1, 1, L"" },

	// TODO
	pe{ L"{{",                err_parse,                  1,  2, L"{" }

};

int main() {
	setlocale(LC_ALL, "");
	bdd::init();
	driver::init();
	try {
		for (auto t : tests) t.run();
		wcout << endl << n-f << L'/' << n << L" ok." << endl
			<< f << L'/' << n << " failed." << endl << endl;
	} catch (std::exception& e) { wcerr << s2ws(e.what()) << endl; }
	return f > 0 ? 1 : 0;
}
