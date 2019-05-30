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
#include <forward_list>
#include "driver.h"
#include "ast.h"

using namespace std;

map<ast::type, std::wstring> ast::names = {
	{SYM, L"symbol"}, {NUM, L"number"}, {CHR, L"char"}, {VAR, L"variable"},
	{OPENP, L"open_paren"}, {CLOSEP, L"close_paren"}, {ALT, L"alt"},
	{STR, L"string"}, {REL, L"relation"}, {NEG, L"negative"},
	{POS, L"positive"}, {TERM, L"term"}, {HEAD ,L"head"}, {BODY, L"body"},
	{DOT, L"dot"}, {DELIM, L"delimiter"}, {NOT, L"not"}, {AND, L"and"},
	{OR, L"or"}, {GOAL, L"goal"}, {TREE, L"tree"}, {FACT, L"fact"},
	{RULE, L"rule"}, {PROD, L"production"}, {DIR, L"directive"},
	{DIRNAME, L"directive_name"}, {OPENC, L"open_curly"},
	{CLOSEC, L"close_curly"}, {PROG, L"program"}, {PROGS, L"programs"}
};
set<ast> ast::nodes;

wostream& driver::print_ast(wostream& os) const {
	cws s = 0;
	for (auto n : ast::nodes) {
		if (!s) s = n.r[0];
		os << ast::name(n) << L'(' <<
			(n.r[0]-s) << L' ' << (n.r[1]-s) << L")." << endl;
	}
	return os.flush();
}

wostream& driver::print_ast_json(wostream& os) const {
	cws s = 0;
	os << L"{ \"AST\": [";
	for (auto n : ast::nodes) {
		if (!s) s = n.r[0];
		else os << L",";
		os << endl << L"\t{ \"node\": \"" << ast::name(n) <<
			L"\", \"from\": " << (n.r[0]-s) << L", \"to\": " <<
			(n.r[1]-s) << L" }";
	}
	os << endl << L"] }" << endl;
	return os.flush();
}

wostream& driver::print_ast_xml(wostream& os) const {
	long p = 0;
	forward_list<wstring> stk;
	forward_list<long> cls;
	auto nit = ast::nodes.begin();
	ast n = *nit;
	cws s = n.r[0], r = n.r[1];
	for (cws c = s; c != r; ++c, ++p) {
		while (nit != ast::nodes.end() && (n.r[0] - s) < p) n = *++nit;
		while (!cls.empty() && cls.front() == p)
			os << L"</" << stk.front() << L'>',
			cls.pop_front(), stk.pop_front();
		while (nit != ast::nodes.end() && (n.r[0] - s) == p)
			os << L'<' << ast::name(n) << L'>',
			stk.push_front(ast::name(n)), cls.push_front(n.r[1]-s),
			n = *++nit;
		os << *c;
	}
	while (!cls.empty()) os << L"</" << stk.front() << L'>',
		cls.pop_front(), stk.pop_front();
	return (os<<endl).flush();
}

wostream& driver::print_ast_html(wostream& os) const {
	long p = 0;
	forward_list<long> cls;
	auto nit = ast::nodes.begin();
	ast n = *nit;
	cws s = n.r[0], r = n.r[1];
	for (cws c = s; c != r; ++c, ++p) {
		while (nit != ast::nodes.end() && (n.r[0] - s) < p) n = *++nit;
		while (!cls.empty() && cls.front() == p)
			os<<L"</span>",
			cls.pop_front();
		while (nit != ast::nodes.end() && (n.r[0] - s) == p)
			os<<L"<span class=\""<<ast::name(n)<<L"\">",
			cls.push_front(n.r[1]-s),
			n = *++nit;
		os << *c;
	}
	while (!cls.empty()) os << L"</span>", cls.pop_front();
	return (os<<endl).flush();
}
