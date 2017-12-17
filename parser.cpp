#include "tml.h"

dict_t dict;

const wchar_t err_misquote[]  = L"The only quotable chars are ()->=\\\"";
const wchar_t err_relvars[]   = L"Relation variables are not allowed";
const wchar_t err_eq_in_head[]= L"Equality not allowed in head";
const wchar_t err_expected1[] = L"Expected ( or =";
const wchar_t err_expected2[] = L"Unexpected character";
const wchar_t err_expected3[] = L"Expected . or ->";
const wchar_t err_expected4[] = L"Expected '.'";

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

bool dlp::word_read(int32_t &t) {
	wstring r;
	bool quote;
	const wchar_t *_s = in;
	// TODO: handle literal strings
	while (iswspace(*in)) ++in;
	if (*in == L'?') r += *in++;
	do {	quote = false;
		if (quote) {
			if (wcschr(L"()->=\\\"", *in)) quote = false, r += *in;
			else parse_error(_s, in-_s, err_misquote);
		}
		while (iswalnum(*in)) r += *in++;
		if (*in == L'\\') quote = true;
	} while (quote);
	while (iswspace(*in)) ++in;
	return r.size() ? t = dict[r], true : false;
}

bool dlp::literal_read(clause &c, bool negate) {
	bool eq;
	const wchar_t *_s = in;
	int32_t w;
	literal l(1);
	if (!word_read(l[0])) return false;
	if (l[0] < 0) parse_error(_s, in - _s, err_relvars);
	if (negate) l[0] = -l[0];
	while (iswspace(*in)) ++in;
	if (!(eq = *in==L'=')&&*in!=L'(') parse_error(_s, in-_s, err_expected1);
	++in;
	if (eq) {
		l.resize(3), l[1] = l[0], l[0] = 0;
		while (iswspace(*in)) ++in;
		if (!word_read(l[2])) return false;
	} else do {
		while (iswspace(*in)) ++in;
		if (word_read(w)) {
			l.push_back(w);
			while (iswspace(*in)) ++in;
			if (*in == L',') ++in;
			else if (!iswalnum(*in) && *in != L')')
				parse_error(_s, in-_s, err_expected2);
		}
	} while (*in != L')');
	return c += l, ++in, true;
}

bool dlp::clause_read() {
	clause c;
	const wchar_t *_s = in;
	while (iswspace(*in)) ++in;
	if (!*in) return false;
	while (literal_read(c, true));
	if (*in == L'.') for (literal *l : c) (*l)[0] = -(*l)[0];
	else if (*in++!=L'-'||*in++!=L'>')parse_error(_s, in-_s, err_expected3);
	else while (*in != L'.' && literal_read(c, false))
		if (!(*c.back())[0]) parse_error(_s, in - _s, err_eq_in_head);
	if (*in++ != L'.') parse_error(_s, in-_s, err_expected4);
	return (*this += new clause(c)), c.clear(), true;
}

void dlp::program_read() { while (clause_read()); }

void dlp::program_read(wistream &is) {
	wstring s, r;
	while (std::getline(is, s)) if (s == L"fin.") break; else r += s;
	in = r.c_str(), program_read(), in = 0;
//	DEBUG(L"finished reading program: " << endl << *this);
}
