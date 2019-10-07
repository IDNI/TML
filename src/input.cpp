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
#include <fstream>
#include <vector>
#include "input.h"
#include "err.h"
#include "output.h"
using namespace std;

cws_range input::source{0,0};

lexeme lex(pcws s) {
	while (iswspace(**s)) ++*s;
	if (!**s) return { 0, 0 };
	cws t = *s;
	if (!wcsncmp(*s, L"/*", 2)) {
		while (wcsncmp(++*s, L"*/", 2))
			if (!**s) parse_error(t, err_comment, 0);
		return ++++*s, lex(s);
	}
	if (**s == L'#') {
		while (*++*s != L'\r' && **s != L'\n' && **s);
		return lex(s);
	}
	if (**s == L'"') {
		while (*++*s != L'"')
			if (!**s) parse_error(t, unmatched_quotes);
			else if (**s == L'\\' && !wcschr(L"\\\"", *++*s))
				parse_error(*s, err_escape);
		return { t, ++(*s) };
	}
	// LEQ: put this in front if '<file>' below (as that'll eat us + error out)
	if (**s == L'<' && *(*s + 1) == L'=') {
		return *s += 2, lexeme{ *s - 2, *s };
	}
	if (**s == L'>') return ++ * s, lexeme{ *s - 1, *s };
	if (**s == L'<') {
		while (*++*s != L'>') if (!**s) parse_error(t, err_fname);
		return { t, ++(*s) };
	}
	if (**s == L'\'') {
		if (*(*s + 1) == L'\'') return { t, ++++*s };
		if (*(*s + 1) == L'\\') {
//			if ((*(*s+2)!=L'\''&&*(*s+2)!=L'\\')
			if (!wcschr(L"\\'rnt",*(*s+2)) ||*(*s+3)!=L'\'')
				parse_error((*s+2), err_escape);
			return { t, ++++++++*s };
		}
		if (*(*s + 2) != L'\'') parse_error(*s+2, err_quote);
		return { t, ++++++*s };
	}
	if (**s == L':') {
		if (*++*s==L'-' || **s==L'=') return ++*s, lexeme{ *s-2, *s };
		else parse_error(*s, err_chr);
	}
	// NEQ: make sure we don't turn off directives (single '!'). limits?
	if (**s == L'!' && *(*s + 1) == L'=') {
		return *s += 2, lexeme{ *s - 2, *s };
	}
	// TODO: single = instead of == recheck if we're not messing up something?
	if (**s == L'=') return ++*s, lexeme{ *s-1, *s };
	//if (**s == L'=' && *(*s + 1) == L'=') {
	//	return *s += 2, lexeme{ *s - 2, *s };
	//}
	if (wcschr(L"!~.,;(){}$@=<>|", **s)) return ++*s, lexeme{ *s-1, *s };
	if (wcschr(L"?-", **s)) ++*s;
	if (!iswalnum(**s) && **s != L'_') parse_error(*s, err_chr);
	while (**s && (iswalnum(**s) || **s == L'_')) ++*s;
	return { t, *s };
}

lexemes prog_lex(cws s) {
	lexeme l;
	lexemes r;
	input::source[0] = s;
	do { if ((l = lex(&s)) != lexeme{0, 0}) r.push_back(l); } while (*s);
	input::source[1] = s;
	return r;
}

int_t get_int_t(cws from, cws to) {
	int_t r = 0;
	bool neg = false;
	if (*from == L'-') neg = true, ++from;
	for (cws s = from; s != to; ++s) if (!iswdigit(*s))
		parse_error(from, err_int);
	wstring s(from, to - from);
	try { r = stoll(s); }
	catch (...) { parse_error(from, err_int); }
	return neg ? -r : r;
}

bool directive::parse(const lexemes& l, size_t& pos) {
	if (*l[pos][0] != '@') return false;
	if (l[++pos] == L"trace") {
		type = TRACE;
		if (!rel.parse(l, ++pos) || rel.type != elem::SYM)
			parse_error(l[pos-1][0], err_trace_rel, l[pos-1]);
		if (*l[pos++][0] != '.')
			parse_error(l[pos-1][0], dot_expected, l[pos-1]);
		return true;
	}
	if (l[pos] == L"bwd") {
		type = BWD;
		if (*l[++pos][0] != '.')
			parse_error(l[pos][0], dot_expected, l[pos]);
		return ++pos, true;
	}
	if (l[pos] == L"stdout") {
		type = STDOUT;
		if (!t.parse(l, ++pos))
			parse_error(l[pos][0], err_stdout, l[pos]);
		if (*l[pos++][0] != '.')
			parse_error(l[pos-1][0], dot_expected, l[pos-1]);
		return true;
	}
	if (!(l[pos] == L"string"))
		parse_error(l[pos][0], err_directive, l[pos]);
	if (!rel.parse(l, ++pos) || rel.type != elem::SYM)
		parse_error(l[pos-1][0], err_rel_expected, l[pos-1]);
	size_t curr2 = pos;
	if (*l[pos][0] == L'<') type = FNAME, arg = l[pos++];
	else if (*l[pos][0] == L'"') type = STR, arg = l[pos++];
	else if (*l[pos][0] == L'$')
		type=CMDLINE, ++pos, n = get_int_t(l[pos][0], l[pos][1]), ++pos;
	else if (l[pos] == L"stdin") type = STDIN;
	else if (t.parse(l, pos)) {
		type = TREE;
		if (*l[pos++][0]!='.')
			parse_error(l[pos][0], dot_expected, l[pos]);
		return true;
	} else parse_error(l[pos][0], err_directive_arg, l[pos]);
	if (*l[pos++][0]!='.')
		parse_error(l[curr2][1], dot_expected, l[curr2]);
	return true;
}

bool elem::parse(const lexemes& l, size_t& pos) {
	if (L'|' == *l[pos][0]) return e = l[pos++],type=ALT,   true;
	if (L'(' == *l[pos][0]) return e = l[pos++],type=OPENP, true;
	if (L')' == *l[pos][0]) return e = l[pos++],type=CLOSEP,true;
	// NEQ: should we check for any limits here?
	if (L'!' == l[pos][0][0] &&
		L'=' == l[pos][0][1]) {
		return e = l[pos++], type = NEQ, true;
	}
	// LEQ: recheck if '<' is going to make any issues (order is important)
	if (L'<' == l[pos][0][0] &&
		L'=' == l[pos][0][1]) {
		return e = l[pos++], type = LEQ, true;
	}
	if (L'>' == l[pos][0][0]) {
		return e = l[pos++], type = GT, true;
	}
	// TODO: single = instead of == recheck if we're not messing up something?
	if (L'=' == l[pos][0][0]) {
		if (pos + 1 < l.size() && L'>' == l[pos+1][0][0]) return false;
		return e = l[pos++], type = EQ, true;
	}
	//if (L'=' == l[pos][0][0] &&
	//	L'=' == l[pos][0][1]) {
	//	return e = l[pos++], type = EQ, true;
	//}
	if (!iswalnum(*l[pos][0]) && !wcschr(L"\"'-?", *l[pos][0])) return false;
	if (e = l[pos], *l[pos][0] == L'\'') {
		type = CHR, e = { 0, 0 };
		if (l[pos][0][1] == L'\'') ch = 0;
		else if (l[pos][0][1] != L'\\') ch = l[pos][0][1];
		else if (l[pos][0][2] == L'r') ch = L'\r';
		else if (l[pos][0][2] == L'n') ch = L'\n';
		else if (l[pos][0][2] == L't') ch = L'\t';
		else if (l[pos][0][2] == L'\\') ch = L'\\';
		else if (l[pos][0][2] == L'\'') ch = L'\'';
		else throw 0;
	}
	else if (*l[pos][0] == L'?') type = VAR;
	else if (iswalpha(*l[pos][0])) type = SYM;
	else if (*l[pos][0] == L'"') type = STR;
	else type = NUM, num = get_int_t(l[pos][0], l[pos][1]);
	return ++pos, true;
}

bool raw_term::parse(const lexemes& l, size_t& pos) {
	size_t curr = pos;
	lexeme s = l[pos];
	if ((neg = *l[pos][0] == L'~')) ++pos;
	bool rel = false, noteq = false, eq = false, leq = false, gt = false;
	while (!wcschr(L".:,;{}", *l[pos][0])) {
		if (e.emplace_back(), !e.back().parse(l, pos)) return false;
		else if (pos == l.size())
			parse_error(input::source[1], err_eof, s[0]);
		switch (e.back().type) {
			case elem::EQ: eq = true; break;
			case elem::NEQ: noteq = true; break;
			case elem::LEQ: leq = true; break;
			case elem::GT: gt = true; break;
			default: break;
		}
		if (!rel) rel = true;
	}
	if (e.empty()) return false;
	// TODO: provide specific error messages. Also, something better to group?
	if (noteq || eq) {
		if (e.size() < 3)
			parse_error(l[pos][0], err_term_or_dot, l[pos]);
		// only supporting smth != smthelse (3-parts) and negation in front ().
		if (e[1].type != elem::NEQ && e[1].type != elem::EQ)
			parse_error(l[pos][0], err_term_or_dot, l[pos]);
		if (noteq)
			neg = !neg; // flip the neg as we have NEQ, don't do it for EQ ofc
		iseq = true;
		return calc_arity(), true;
	}
	if (leq || gt) {
		if (e.size() < 3)
			parse_error(l[pos][0], err_term_or_dot, l[pos]);
		// only supporting smth != smthelse (3-parts) and negation in front ().
		if (e[1].type != elem::LEQ && e[1].type != elem::GT)
			parse_error(l[pos][0], err_term_or_dot, l[pos]);
		if (gt) neg = !neg;
		isleq = true;
		return calc_arity(), true;
	}
	if (e[0].type != elem::SYM)
		parse_error(l[curr][0], err_relsym_expected, l[curr]);
	if (e.size() == 1) return calc_arity(), true;
	if (e[1].type != elem::OPENP)
		parse_error(l[pos][0], err_paren_expected, l[pos]);
	if (e.back().type != elem::CLOSEP)
		parse_error(e.back().e[0], err_paren, l[pos]);
	return calc_arity(), true;
}

void raw_term::insert_parens(lexeme op, lexeme cl) {
	elem o = elem(elem::OPENP, op), c = elem(elem::CLOSEP, cl);
	e.insert(e.begin() + 1, o), e.push_back(c);
	for (size_t n = 0, k = 2; n != arity.size(); ++n)
		if (arity[n] == -1) e.insert(e.begin() + k++, o);
		else if (arity[n] == -2) e.insert(e.begin() + k++, c);
		else k += arity[n];
}

void raw_term::calc_arity() {
	size_t dep = 0;
	arity = {0};
	if (iseq || isleq) {
		arity = { 2 };
		return;
	}
	if (e.size() == 1) return;
	for (size_t n = 2; n < e.size()-1; ++n)
		if (e[n].type == elem::OPENP) ++dep, arity.push_back(-1);
		else if (e[n].type != elem::CLOSEP) {
			if (arity.back() < 0) arity.push_back(1);
			else ++arity.back();
		} else if (!dep--) parse_error(e[n].e[0], err_paren, e[n].e);
		else arity.push_back(-2);
	if (dep) parse_error(e[0].e[0], err_paren, e[0].e);
}

bool raw_rule::parse(const lexemes& l, size_t& pos) {
	size_t curr = pos;
	if (*l[pos][0] == L'!') {
		if (*l[++pos][0] == L'!') ++pos, type = TREE;
		else type = GOAL;
	}
head:	h.emplace_back();
	if (!h.back().parse(l, pos)) return pos = curr, false;
	if (*l[pos][0] == '.') return ++pos, true;
	if (*l[pos][0] == ',') { ++pos; goto head; }
	if (*l[pos][0] != ':' || l[pos][0][1] != L'-')
		parse_error(l[pos][0], err_head, l[pos]);
	++pos; b.emplace_back();
	for (	b.back().emplace_back(); b.back().back().parse(l, pos);
		b.back().emplace_back(), ++pos) {
		if (*l[pos][0] == '.') return ++pos, true;
		else if (*l[pos][0] == L';') b.emplace_back();
		else if (*l[pos][0] != ',')
			parse_error(l[pos][0], err_term_or_dot,l[pos]);
	}
	parse_error(l[pos][0], err_body, l[pos]);
	return false;
}

bool production::parse(const lexemes& l, size_t& pos) {
	size_t curr2, curr = pos;
	elem e;
	if (!e.parse(l, pos) || l.size() <= pos+1) goto fail;
/*	if (*l[pos++][0] == L'<') {
		if (l[pos++][0][0] != L'=') goto fail;
		start = true;
		if (!t.parse(l, pos)) parse_error(err_start_sym, l[pos]);
		if (*l[pos++][0] != '.') parse_error(dot_expected, l[pos]);
		return true;
	}*/
	if (*l[pos++][0] != '=' || l[pos++][0][0] != L'>') goto fail;
	curr2 = pos;
	for (p.push_back(e);;) {
		elem e;
		if (pos == l.size()) break;
		if (*l[pos][0] == '.') return ++pos, true;
		if (!e.parse(l, pos)) goto fail;
		p.push_back(e);
	}
	parse_error(l[curr2][0], err_prod, l[curr2]);
fail:	return pos = curr, false;
}

bool raw_prog::parse(const lexemes& l, size_t& pos) {
	while (pos < l.size() && *l[pos][0] != L'}') {
		directive x;
		raw_rule y;
		production p;
		if (x.parse(l, pos)) d.push_back(x);
		else if (y.parse(l, pos)) r.push_back(y);
		else if (p.parse(l, pos)) g.push_back(p);
		else return false;
	}
	return true;
}

raw_progs::raw_progs(FILE* f) : raw_progs(file_read_text(f)) {}

raw_progs::raw_progs(const std::wstring& s) {
	try {
		size_t pos = 0;
		lexemes l = prog_lex(wcsdup(s.c_str()));
		if (!l.size()) return;
		if (*l[pos][0] != L'{') {
			raw_prog x;
			if (!x.parse(l, pos))
				parse_error(l[pos][0],
					err_rule_dir_prod_expected, l[pos]);
			p.push_back(x);
		} else do {
			raw_prog x;
			if (++pos, !x.parse(l, pos))
				parse_error(l[pos][0], err_parse, l[pos]);
			if (p.push_back(x), pos==l.size() || *l[pos++][0]!=L'}')
				parse_error(l[pos-1][1],
					err_close_curly, l[pos-1]);
		} while (pos < l.size());
	} catch (std::exception &e) {
		output::to(L"error") << s2ws(e.what()) << std::endl;
	}
}

bool operator==(const lexeme& x, const lexeme& y) {
	return x[1]-x[0] == y[1]-y[0] && !wcsncmp(x[0],y[0],x[1]-x[0]);
}

bool operator<(const raw_term& x, const raw_term& y) {
	if (x.neg != y.neg) return x.neg < y.neg;
	if (x.iseq != y.iseq) return x.iseq < y.iseq;
	if (x.isleq != y.isleq) return x.isleq < y.isleq;
	if (x.e != y.e) return x.e < y.e;
	if (x.arity != y.arity) return x.arity < y.arity;
	return false;
}

//bool operator==(const raw_term& x, const raw_term& y) {
//	return x.neg == y.neg && x.e == y.e && x.arity == y.arity;
//}

bool operator<(const raw_rule& x, const raw_rule& y) {
	if (x.h != y.h) return x.h < y.h;
	if (x.b != y.b) return x.b < y.b;
/*	if (x.h.size() != y.h.size())
		return x.heads().size() < y.heads().size();
	if (x.bodies().size() != y.bodies().size())
		return x.bodies().size() < y.bodies().size();
	for (size_t n = 0; n != x.h.size(); ++n)
		if (!(x.head(n) == y.h[n])) return x.head(n) < y.head(n);
	for (size_t n = 0; n != x.bodies().size(); ++n)
		if (!(x.body(n) == y.body(n))) return x.body(n) < y.body(n);*/
	return false;
}

bool operator==(const lexeme& l, const wstring& s) {
	if ((size_t)(l[1]-l[0]) != s.size()) return false;
	return !wcsncmp(l[0], s.c_str(), l[1]-l[0]);
}

bool operator==(const lexeme& l, cws s) {
	size_t n = wcslen(s);
	return (size_t)(l[1] - l[0]) != n ? false : !wcsncmp(l[0], s, n);
}

bool lexcmp::operator()(const lexeme& x, const lexeme& y) const {
	if (x[1]-x[0] != y[1]-y[0]) return x[1]-x[0] < y[1]-y[0];
	for (size_t n = 0; n != (size_t)(x[1]-x[0]); ++n)
		if (x[0][n] != y[0][n]) return x[0][n] < y[0][n];
	return false;
	// the following causes valgrind to complain about __wcsncmp_avx2:
//	return	x[1]-x[0] != y[1]-y[0] ? x[1]-x[0] < y[1]-y[0]
//		: (wcsncmp(x[0], y[0], x[1]-x[0]) < 0);
}

bool operator==(const std::vector<raw_term>& x, const std::vector<raw_term>& y){
	if (x.size() != y.size()) return false;
	for (size_t n = 0; n != x.size(); ++n) if (!(x[n]==y[n])) return false;
	return true;
}

off_t fsize(const char *fname) {
	struct stat s;
	return stat(fname, &s) ? 0 : s.st_size;
}

off_t fsize(cws s, size_t len) { return fsize(ws2s(wstring(s, len)).c_str()); }

wstring file_read(wstring fname) {
	wifstream s(ws2s(fname));
	wstringstream ss;
	return (ss << s.rdbuf()), ss.str();
}

wstring file_read_text(FILE *f) {
	wstringstream ss;
	wchar_t buf[32], n, l, skip = 0;
	wint_t c;
	*buf = 0;
next:	for (n = l = 0; n != 31; ++n)
		if (WEOF == (c = getwc(f))) { skip = 0; break; }
//		else if (c == L'#') skip = 1;
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
	if (!f) parse_error(err_fnf, wfname);
	wstring r = file_read_text(f);
	fclose(f);
	return r;
}

void parse_error(cws o, std::wstring e) { parse_error(o, e, o); }
void parse_error(wstring e, lexeme l) { parse_error(0, e, l); }
void parse_error(std::wstring e, std::wstring s) { parse_error(0, e, s); }

void parse_error(cws o, std::wstring e, std::wstring s) {
	parse_error(o, e, s.c_str());
}

void parse_error(cws o, std::wstring e, cws s, size_t len) {
	parse_error(o, e, wstring(s, len).c_str());
}

void parse_error(cws o, wstring e, lexeme l) {
	parse_error(o, e, wstring(l[0], l[1]-l[0]).c_str());
}

void count_pos(const cws& s, const cws& o, long& l, long& ch) {
	l = 1;
	cws c = s, n = c - 1;
	while (c < o) {
		if (*c && *c == L'\n') { n = c; ++l; }
		++c;
	}
	ch = o-n;
}

void parse_error(cws o, std::wstring e, cws s) {
	std::wstringstream msg; msg << L"Parse error: \"" << e << L'"';
	cws p = s;
	while (p && *p && *p != L'\n') ++p;
	if (o != 0) {
		long l, ch; count_pos(input::source[0], o, l, ch);
		msg << L" at " << l << L':' << ch;
	}
	if (s) msg << L" close to \"" << std::wstring(s, p-s) << L'"';
	throw parse_error_exception(ws2s(msg.str()));
}
