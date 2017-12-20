#include "tml.h"

dict_t dict;

dict_t::dict_t() {
	if ((*this)[L"="] != 1) { wcerr<<L"dict error"; throw L""; }
}

int32_t dict_t::operator[](const wstring &s) {
	map<wstring, size_t>::const_iterator it = m.find(s);
	if (it != m.end()) return it->second;
	strings.push_back(s);
	int32_t i = strings.size();
	return m[s] = (s[0] == L'?' ? -i : i);
}

wstring dict_t::operator[](int32_t i) const { return strings[abs(i) - 1]; }

void parse_error(const wchar_t *s, size_t pos, const wchar_t *err) {
	wstring t(pos, L' ');
	wcerr << s << endl << t << L"^ " << err;
	throw runtime_error("");
}
void parse_error(const strbuf &s, intptr_t p, const wchar_t *err) {
	parse_error(s.s, size_t(p), err);
}

bool part_of_word(wchar_t c) {
	return iswalnum(c) || wcschr(L"?!=+*/_:;~`'[]{}", c);
}

bool word_read(strbuf& in, int32_t &t, bool &neg) {
	wstring r;
//	bool quote;
	const strbuf _s(in.s);
	// TODO: handle literal strings
	while (iswspace(*in)) ++in;
	if (*in == L'?') (r += *in), ++in;
//	do {	quote = false;
//		if (quote) {
//			if (wcschr(L"()->=\\\"", *in)) quote = false, r += *in;
//			else parse_error(_s, in - _s, err_misquote);
//		}
		while (part_of_word(*in)) (r += *in), ++in;
//		if (*in == L'\\') quote = true;
//	} while (quote);
	while (iswspace(*in)) ++in;
	if ((neg = r[0] == L'!')) r.erase(r.begin());
	return r.size() ? t = dict[r], true : false;
}

bool literal_read(strbuf &in, clause &c, bool body) {
	bool triple, neg;
	const strbuf _s(in.s);
	int32_t w;
	literal l;
	if (!word_read(in, w, neg)) return false;
	while (iswspace(*in)) ++in;
	if ((triple = *in != L'(')) {
		int32_t _w = w;
		bool _neg;
		if (!word_read(in, w, _neg))
		if (_neg) parse_error(_s, in - _s, err_neg);
		l.push_back(w), l.push_back(_w); // pred is second
		while (word_read(in, w, _neg))
			if (_neg) parse_error(_s, in - _s, err_neg);
			else l.push_back(w);
		if (neg) l.flip();
		if (body) l.flip();
	} else {
		if (w < 0) parse_error(_s, in - _s, err_relvars);
		++in, l.push_back(w);
		if (neg) l.flip();
		if (body) l.flip();
		do {
			if (!word_read(in, w, neg))
				parse_error(_s, in - _s, err_expected1);
			if (neg) parse_error(_s, in - _s, err_neg);
			l.push_back(w);
			while (iswspace(*in)) ++in;
			if (*in == L',') ++in;
			else if (!part_of_word(*in) && *in != L')')
				parse_error(_s, in-_s, err_expected2);
		} while (*in != L')');
	}
	l.rehash();
	if (*in == L')') ++in;
	return c += l, true;
}

clause* clause::clause_read(strbuf &in) {
	clause c;
	const strbuf _s(in.s);
	while (iswspace(*in)) ++in;
	if (!*in) return 0;
	while (literal_read(in, c, true));
	if (*in == L'.') c.flip();
	else if (in.adv() != L'-' || in.adv() != L'>')
		parse_error(_s, in - _s, err_expected3);
	else while (*in != L'.' && literal_read(in, c, 0));
//		if (!c.lastrel()) parse_error(_s, in - _s, err_eq_in_head);
	if (in.adv() != L'.') parse_error(_s, in - _s, err_expected4);
	clause *r = new clause(c);
	return r->rehash(), c.clear(), r;
}

void dlp::program_read(strbuf &in) { clause *c; while ((c=clause::clause_read(in))) *this+=c; }

clause* clause::clause_read(wistream &is) {
	wstring s, r;
	while (std::getline(is, s))
		if (s == L"fin.") break;
		else if (s[0] != L'#') r += s;
	strbuf b(r.c_str());
	return clause_read(b);
//	DEBUG(L"finished reading program: " << endl << *this);
}
void dlp::program_read(wistream &is) {
	wstring s, r;
	while (std::getline(is, s)) 
		if (s == L"fin.") break; 
		else if (s[0] != L'#') r += s;
	strbuf b(r.c_str());
	program_read(b);
//	DEBUG(L"finished reading program: " << endl << *this);
}
