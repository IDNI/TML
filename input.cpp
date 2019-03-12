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
#include <string>
#include <cstring>
#include <sstream>
#include <iostream>
#include <vector>
#include "input.h"
using namespace std;

wstring file_read_text(FILE *f);
wstring file_read_text(wstring fname);

wostream& operator<<(wostream& os, const lexeme& l) {
	for (cws s = l[0]; s != l[1]; ++s) os << *s;
	return os;
}

lexeme lex(pcws s) {
	while (iswspace(**s)) ++*s;
	if (!**s) return { 0, 0 };
	cws t = *s;
	if (**s == L'"') {
		while (*++*s != L'"')
			if (!**s) er(unmatched_quotes);
			else if (**s == L'\'' && !wcschr(L"\\\"", *++*s))
				er(err_escape);
		return { t, ++*s };
	}
	if (**s == L'<') {
		while (*++*s != L'>') if (!**s) er(err_fname);
		return { t, ++*s };
	}
	if (**s == L'\'') {
		if (*(*s + 2) != L'\'') er(err_quote);
		return { t, ++++++*s };
	}
	if (**s == L':') {
		if (*++*s == L'-') return ++*s, lexeme{ *s-2, *s };
		else er(err_chr);
	}
	if (wcschr(L".,{}@", **s)) return ++*s, lexeme{ *s-1, *s };
	if (**s == L'?' || **s == L'-') ++*s;
	while (iswalnum(**s)) ++*s;
	return { t, *s };
}

lexemes prog_lex(cws s) {
	lexeme l;
	lexemes r;
	do {
		if ((l = lex(&s)) != lexeme{0, 0}) r.push_back(l);
	} while (*s);
	return r;
}

struct directive {
	lexeme rel, arg;
	bool fname;
	bool parse(const lexemes& l, size_t& pos) {
		if (*l[pos][0] != '@') return false;
		rel = l[++pos];
		if (*l[pos++][0] == L'<') fname = true;
		else if (*l[pos][0] == L'"') fname = false;
		else er(err_directive_arg);
		arg = l[pos++];
		if (*l[pos++][0] != '.') er(dot_expected);
		return true;
	}
};

wostream& operator<<(wostream& os, const directive& d) {
	return os << d.rel << ' ' << d.arg;
}

int_t get_int_t(cws from, cws to) {
	int_t r = 0;
	bool neg = false;
	if (*from == L'-') neg = true, ++from;
	for (cws s = from; s != to; ++s) if (!iswdigit(*s)) er(err_int);
	wstring s(from, to - from);
	try { r = stoll((const char*)s.c_str()); }
	catch (...) { er(err_int); }
	return neg ? -r : r;
}

struct elem {
	enum etype { SYM, NUM, CHR, VAR } type;
	int_t num;
	lexeme e;
	bool parse(const lexemes& l, size_t& pos) {
		if (!iswalnum(*l[pos][0]) && !wcschr(L"'-?", *l[pos][0]))
			return false;
		e = l[pos];
		if (*l[pos][0] == L'\'') {
			if (l[pos][1]-l[pos][0] != 3 || *(l[pos][1]-1)!=L'\'')
				er(err_quote);
			type = CHR;
			e = { l[pos][0] + 1, l[pos][1]-1 };
		} //else if (l[pos][1] - l[pos][0] != 1) er(err_lex);
		else if (*l[pos][0] == L'?') type = VAR;
		else if (iswalpha(*l[pos][0])) type = SYM;
		else type = NUM, num = get_int_t(l[pos][0], l[pos][1]);
		return ++pos, true;
	}
};

wostream& operator<<(wostream& os, const elem& e) {
	if (e.type == elem::CHR) return os << '\'' << *e.e[0] << '\'';
	return e.type == elem::NUM ? os << e.num : (os << e.e);
}

struct raw_term {
	vector<elem> e;
	bool parse(const lexemes& l, size_t& pos) {
		while (!wcschr(L".:,", *l[pos][0])) {
			elem m;
			if (!m.parse(l, pos)) return false;
			e.push_back(m);
		}
		return true;
	}
};

wostream& operator<<(wostream& os, const raw_term& t) {
	for (auto x : t.e) os << x << L' ';
	return os;
}

struct raw_rule {
	raw_term h;
	vector<raw_term> b;
	bool parse(const lexemes& l, size_t& pos) {
		if (!h.parse(l, pos)) return false;
		if (*l[pos][0] == '.') return ++pos, true;
		if (*l[pos++][0] != ':') er(err_chr);
		raw_term t;
		while (t.parse(l, pos)) {
			b.push_back(t);
			if (*l[pos][0] == '.') return ++pos, true;
			if (*l[pos][0] != ',') er(err_term_or_dot);
			++pos;
		}
		er(err_body);
	}
};

wostream& operator<<(wostream& os, const raw_rule& r) {
	os << r.h << L" :- ";
	for (auto x : r.b) os << x << L',';
	return os << L'.';
}

struct raw_prog {
	vector<directive> d;
	vector<raw_rule> r;
	bool parse(const lexemes& l, size_t& pos) {
		while (pos < l.size()) {
			directive x;
			raw_rule y;
			if (x.parse(l, pos)) d.push_back(x);
			else if (y.parse(l, pos)) r.push_back(y);
			else return false;
		}
		if (pos < l.size()) er(err_parse);
		return true;
	}
};

wostream& operator<<(wostream& os, const raw_prog& p) {
	for (auto x : p.d) os << x << endl;
	for (auto x : p.r) os << x << endl;
	return os;
}

void parser_test() {
	setlocale(LC_ALL, "");
	wstring s = file_read_text(stdin);
	size_t pos = 0;
	raw_prog p;
	wcout << p.parse(prog_lex(s.c_str()), pos) << endl << p << endl;
}
