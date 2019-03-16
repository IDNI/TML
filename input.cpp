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
#include <vector>
#include "input.h"
using namespace std;

#define dot_expected "'.' expected.\n"
#define sep_expected "Term or ':-' or '.' expected.\n"
#define unmatched_quotes "Unmatched \"\n"
#define err_inrel "Unable to read the input relation symbol.\n"
#define err_src "Unable to read src file.\n"
#define err_dst "Unable to read dst file.\n"
#define err_quotes "expected \".\n"
#define err_dots "two consecutive dots, or dot in beginning of document.\n"
#define err_quote "' should come before and after a single character only.\n"
#define err_fname "malformed filename.\n"
#define err_directive_arg "invalid directive argument.\n"
#define err_escape "invalid escaped character\n"
#define err_int "malformed int.\n"
#define err_lex "lexer error (please report as a bug).\n"
#define err_parse "parser error (please report as a bug).\n"
#define err_chr "unexpected character.\n"
#define err_body "rules' body expected.\n"
#define err_term_or_dot "term or dot expected.\n"
#define err_close_curly "'}' expected.\n"
#define err_fnf "file not found.\n"

lexeme lex(pcws s) {
	while (iswspace(**s)) ++*s;
	if (!**s) return { 0, 0 };
	cws t = *s;
	if (**s == L'"') {
		while (*++*s != L'"')
			if (!**s) er(unmatched_quotes);
			else if (**s == L'\\' && !wcschr(L"\\\"", *++*s))
				er(err_escape);
		return { t, (*s)++ };
	}
	if (**s == L'<') {
		while (*++*s != L'>') if (!**s) er(err_fname);
		return { t, (*s)++ };
	}
	if (**s == L'\'') {
		if (*(*s + 2) != L'\'') er(err_quote);
		return { t, ++++++*s };
	}
	if (**s == L':') {
		if (*++*s == L'-') return ++*s, lexeme{ *s-2, *s };
		else er(err_chr);
	}
	if (**s == L'!' && *(*s + 1) == L'!') return *s+=2, lexeme{ *s-2, *s };
	if (wcschr(L"!~.,{}@", **s)) return ++*s, lexeme{ *s-1, *s };
	if (wcschr(L"?-", **s)) ++*s;
	while (iswalnum(**s)) ++*s;
	return { t, *s };
}

lexemes prog_lex(cws s) {
	lexeme l;
	lexemes r;
	do { if ((l = lex(&s)) != lexeme{0, 0}) r.push_back(l); } while (*s);
	return r;
}

bool directive::parse(const lexemes& l, size_t& pos) {
	if (*l[pos][0] != '@') return false;
	if (rel = l[++pos], *l[++pos][0] == L'<') fname = true;
	else if (*l[pos][0] == L'"') fname = false;
	else er(err_directive_arg);
	if (arg = l[pos++], *l[pos++][0] != '.') er(dot_expected);
	return true;
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

bool elem::parse(const lexemes& l, size_t& pos) {
	if (!iswalnum(*l[pos][0]) && !wcschr(L"'-?", *l[pos][0])) return false;
	if (e = l[pos], *l[pos][0] == L'\'') {
		if (l[pos][1]-l[pos][0]!=3||*(l[pos][1]-1)!=L'\'')er(err_quote);
		type = CHR, e = { l[pos][0] + 1, l[pos][1]-1 };
	} else if (*l[pos][0] == L'?') type = VAR;
	else if (iswalpha(*l[pos][0])) type = SYM;
	else type = NUM, num = get_int_t(l[pos][0], l[pos][1]);
	return ++pos, true;
}

bool raw_term::parse(const lexemes& l, size_t& pos) {
	if ((neg = *l[pos][0] == L'~')) ++pos;
	while (!wcschr(L".:,", *l[pos][0])) {
		elem m;
		if (!m.parse(l, pos)) return false;
		e.push_back(m);
	}
	return true;
}

bool raw_rule::parse(const lexemes& l, size_t& pos) {
	if ((goal = *l[pos][0] == L'!'))
		if ((pgoal = *l[++pos][0] == L'!'))
			++pos;
	if (!h.parse(l, pos)) return false;
	if (*l[pos][0] == '.') return ++pos, true;
	if (*l[pos++][0] != ':') er(err_chr);
	raw_term t;
	while (t.parse(l, pos)) {
		if (b.push_back(t), *l[pos][0] == '.') return ++pos, true;
		if (*l[pos][0] != ',') er(err_term_or_dot);
		++pos, t.e.clear();
	}
	er(err_body);
}

bool raw_prog::parse(const lexemes& l, size_t& pos) {
	while (pos < l.size() && *l[pos][0] != L'}') {
		directive x;
		raw_rule y;
		if (x.parse(l, pos)) d.push_back(x);
		else if (y.parse(l, pos)) r.push_back(y);
		else return false;
	}
	return true;
}

raw_progs::raw_progs(FILE* f) : raw_progs(file_read_text(f)) {}

raw_progs::raw_progs(const std::wstring& s) {
	size_t pos = 0;
	lexemes l = prog_lex(wcsdup(s.c_str()));
	if (*l[pos][0] != L'{') {
		raw_prog x;
		if (!x.parse(l, pos)) er(err_parse);
		p.push_back(x);
	} else do {
		raw_prog x;
		if (++pos, !x.parse(l, pos)) er(err_parse);
		if (p.push_back(x), *l[pos++][0] != L'}') er(err_close_curly);
	} while (pos < l.size());
}

wostream& operator<<(wostream& os, const lexeme& l) {
	for (cws s = l[0]; s != l[1]; ++s) os << *s;
	return os;
}

wostream& operator<<(wostream& os, const directive& d) {
	return os << d.rel << ' ' << d.arg;
}

wostream& operator<<(wostream& os, const elem& e) {
	if (e.type == elem::CHR) return os << '\'' << *e.e[0] << '\'';
	return e.type == elem::NUM ? os << e.num : (os << e.e);
}

wostream& operator<<(wostream& os, const raw_term& t) {
	if (t.neg) os << L'~';
	for (auto x : t.e) os << x << L' ';
	return os;
}

wostream& operator<<(wostream& os, const raw_rule& r) {
	os << r.h << L" :- ";
	for (auto x : r.b) os << x << L',';
	return os << L'.';
}

wostream& operator<<(wostream& os, const raw_prog& p) {
	for (auto x : p.d) os << x << endl;
	for (auto x : p.r) os << x << endl;
	return os;
}

wostream& operator<<(wostream& os, const raw_progs& p) {
	if (p.p.size() == 1) os << p.p[0];
	else for (auto x : p.p) os << L'{' << endl << x << L'}' << endl;
	return os;
}

off_t fsize(const char *fname) {
	struct stat s;
	return stat(fname, &s) ? 0 : s.st_size;
}

wstring file_read_text(FILE *f) {
	wstringstream ss;
	wchar_t buf[32], n, l, skip = 0;
	wint_t c;
	*buf = 0;
next:	for (n = l = 0; n != 31; ++n)
		if (WEOF == (c = getwc(f))) { skip = 0; break; }
		else if (c == L'#') skip = 1;
		else if (c == L'\r' || c == L'\n') skip = 0, buf[l++] = c;
		else if (!skip) buf[l++] = c;
	if (n) {
		buf[l] = 0, ss << buf;
		goto next;
	} else if (skip) goto next;
	return ss.str();
}

wstring file_read_text(wstring wfname) {
	string fname(wfname.begin(), wfname.end());
	FILE *f = fopen(fname.c_str(), "r");
	if (!f) er(err_fnf);
	wstring r = file_read_text(f);
	fclose(f);
	return r;
}

void parser_test() {
	setlocale(LC_ALL, "");
	wcout<<raw_progs(stdin);
	exit(0);
}
