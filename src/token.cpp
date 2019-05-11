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
#include <stack>
#include "driver.h"
#include "token.h"

using namespace std;

const wstring token_names[] = {
	L"symbol",
	L"number", L"char", L"variable", L"open_paren", L"close_paren",
	L"alt", L"string", L"relation", L"negative", L"positive",
	L"term", L"head", L"body", L"dot", L"delimiter",
	L"not", L"and", L"or", L"goal", L"tree",
	L"fact", L"rule", L"production", L"directive", L"open_curly",
	L"close_curly", L"program", L"programs"
};
vector<wstring> token::names(token_names, end(token_names));
set<token> token::tokens;

wostream& driver::print_tokens(wostream& os) const {
	cws s = nullptr;
	for (auto t : token::tokens) {
		if (s == nullptr) s = t.e[0];
		os << L"token(" << token::name(t.type) << L' ' <<
			(t.e[0]-s) << L' ' << (t.e[1]-s) << L")." << endl;
	}
	return os;
}

wostream& driver::print_tokens_json(wostream& os) const {
	cws s = nullptr;
	os << L"{ \"tokens\": [";
	for (auto t : token::tokens) {
		if (s == nullptr) s = t.e[0];
		else os << L",";
		os << endl << L"\t{ \"token\": \"" << token::name(t.type) <<
			L"\", \"from\": " << (t.e[0]-s) << L", \"to\": " <<
			(t.e[1]-s) << L" }";
	}
	return os << endl << L"] }" << endl;
}

wostream& driver::print_tokens_xml(wostream& os) const {
	long n = 0;
	stack<wstring> stk;
	stack<long> cls;
	auto tit = token::tokens.begin();
	token t = *tit;
	cws s = t.e[0], e = t.e[1];
	for (cws c = s ; c != e; ++c, ++n) {
		while (!cls.empty() && cls.top() == n) os << L"</" <<
			stk.top() << L'>', cls.pop(), stk.pop();
		while ((t.e[0] - s) < n) t = *++tit;
		while ((t.e[0] - s) == n) os << L'<' <<
			token::name(t.type) << L'>',
			stk.push(token::name(t.type)),
			cls.push(t.e[1]-s),
			t = *++tit;
		os << *c;
		while (!cls.empty() && cls.top() == n) os << L"</" <<
			stk.top() << L'>', cls.pop(), stk.pop();
	}
	while (!cls.empty()) os << L"</" << stk.top() << L'>',
		cls.pop(), stk.pop();
	return os;
}

wostream& driver::print_tokens_html(wostream& os) const {
	long n = 0;
	stack<long> cls;
	auto tit = token::tokens.begin();
	token t = *tit;
	cws s = t.e[0], e = t.e[1];
	for (cws c = s ; c != e; ++c, ++n) {
		while (!cls.empty() && cls.top() == n)
			os << L"</span>", cls.pop();
		while ((t.e[0] - s) < n) t = *++tit;
		while ((t.e[0] - s) == n) os << L"<span class=\"" <<
			token::name(t.type) << L"\">",
			cls.push(t.e[1]-s),
			t = *++tit;
		os << *c;
		while (!cls.empty() && cls.top() == n)
			os << L"</span>", cls.pop();
	}
	while (!cls.empty()) os << L"</span>", cls.pop();
	return os;
}
