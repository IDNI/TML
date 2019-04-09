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
#include "driver.h"
#include "err.h"
using namespace std;

lexeme driver::get_char_lexeme(wchar_t c) {
	wstring s;
	return dict.get_lexeme(s += c);
}

lexeme driver::get_num_lexeme(int_t n) { return dict.get_lexeme(to_wstring(n));}

lexeme driver::get_var_lexeme(int_t i) {
	wstring s = L"?v";
	return dict.get_lexeme(s += to_wstring(i));
}

bool operator==(const lexeme& l, cws s) {
	size_t n = wcslen(s);
	return (size_t)(l[1] - l[0]) != n ? false : !wcsncmp(l[0], s, n);
}

/*struct lexemecmp {
	bool operator()(const lexeme& x, const lexeme& y) const {
		return	x[1]-x[0] != y[1]-y[0] ? x[1]-x[0] < y[1]-y[0] :
			(wcsncmp(x[0], y[0], x[1]-x[0]) < 0);
	}
};*/

raw_term driver::from_grammar_elem(const elem& v, int_t v1, int_t v2) {
	return { false, {v,
		{elem::OPENP, 0, dict.get_lexeme(L"(")},
		{elem::VAR, 0, get_var_lexeme(v1)},
		{elem::VAR, 0, get_var_lexeme(v2)},
		{elem::CLOSEP, 0, dict.get_lexeme(L")")}}, {2}};
}

raw_term driver::from_grammar_elem_nt(const lexeme& r, const elem& c,
	int_t v1, int_t v2) {
	raw_term t{ false, {
		{elem::SYM, 0, r},
		{elem::OPENP, 0, dict.get_lexeme(L"(")},
		{elem::OPENP, 0, dict.get_lexeme(L"(")},
		{elem::OPENP, 0, dict.get_lexeme(L"(")},
		{elem::VAR, 0, get_var_lexeme(v1)},
		{elem::CLOSEP, 0, dict.get_lexeme(L")")},
		{elem::CLOSEP, 0, dict.get_lexeme(L")")},
		{elem::OPENP, 0, dict.get_lexeme(L"(")},
		c,
		{elem::CLOSEP, 0, dict.get_lexeme(L")")},
		{elem::OPENP, 0, dict.get_lexeme(L"(")},
		{elem::OPENP, 0, dict.get_lexeme(L"(")},
		{elem::VAR, 0, get_var_lexeme(v2)},
		{elem::CLOSEP, 0, dict.get_lexeme(L")")},
		{elem::CLOSEP, 0, dict.get_lexeme(L")")},
		{elem::CLOSEP, 0, dict.get_lexeme(L")")}
	}, {}};
	return t.calc_arity(), t;
}

raw_term driver::from_grammar_elem_builtin(const lexeme& r, const wstring& b,
	int_t v){
	return { false, {
		{elem::SYM, 0, r},
		{elem::OPENP, 0, dict.get_lexeme(L"(")},
		{elem::SYM, 0, dict.get_lexeme(b)},
		{elem::VAR, 0, get_var_lexeme(v)},
		{elem::VAR, 0, get_var_lexeme(v+1)},
		{elem::CLOSEP, 0, dict.get_lexeme(L")")}}, {3}};
}

#define from_string_lex(rel, lex, n) raw_rule({ false, { \
		{elem::SYM, 0, rel}, {elem::SYM, 0, dict.get_lexeme(lex)}, \
		{elem::NUM, n, get_num_lexeme(n)}, \
		{elem::NUM, n+1, get_num_lexeme(n+1)}},{3}})

void driver::transform_string(const wstring& s, raw_prog& r, int_t rel){
	for (int_t n = 0; n < (int_t)s.size(); ++n) {
		r.r.push_back(raw_rule(raw_term{
			false, {
			{elem::SYM, 0, dict.get_rel(rel)},
			{elem::OPENP, 0, dict.get_lexeme(L"(")},
			{elem::OPENP, 0, dict.get_lexeme(L"(")},
			{elem::OPENP, 0, dict.get_lexeme(L"(")},
			{elem::NUM, n, get_num_lexeme(n)},
			{elem::CLOSEP, 0, dict.get_lexeme(L")")},
			{elem::CLOSEP, 0, dict.get_lexeme(L")")},
			{elem::OPENP, 0, dict.get_lexeme(L"(")},
			{elem::CHR, 0, get_char_lexeme(s[n])},
			{elem::CLOSEP, 0, dict.get_lexeme(L")")},
			{elem::OPENP, 0, dict.get_lexeme(L"(")},
			{elem::OPENP, 0, dict.get_lexeme(L"(")},
			{elem::NUM, n+1, get_num_lexeme(n+1)},
			{elem::CLOSEP, 0, dict.get_lexeme(L")")},
			{elem::CLOSEP, 0, dict.get_lexeme(L")")},
			{elem::CLOSEP, 0, dict.get_lexeme(L")")}},{}}));
		r.r.back().head(0).calc_arity();
		if (iswspace(s[n]))
			r.r.push_back(from_string_lex(
					dict.get_rel(rel), L"space", n));
		if (iswdigit(s[n]))
			r.r.push_back(from_string_lex(
					dict.get_rel(rel), L"digit", n));
		if (iswalpha(s[n]))
			r.r.push_back(from_string_lex(
					dict.get_rel(rel), L"alpha", n));
		if (iswalnum(s[n]))
			r.r.push_back(from_string_lex(
					dict.get_rel(rel), L"alnum", n));
	}
}

#define lexeme2str(l) wstring((l)[0], (l)[1]-(l)[0])
#define append_sym_elem(x, s) (x).push_back({elem::SYM, 0, s})
#define append_openp(x) (x).push_back({elem::OPENP, 0, dict.get_lexeme(L"(")})
#define append_closep(x) (x).push_back({elem::CLOSEP, 0, dict.get_lexeme(L")")})
#define cat(x, y) x.insert(x.end(), y.begin(), y.end())
#define cat_in_brackets(x, y) \
	append_openp((x).e), cat((x).e, (y).e), append_closep((x).e)
#define cat_relsym_openp(x, r) append_sym_elem((x).e, r), append_openp((x).e)
#define term_close(x) append_closep((x).e), (x).calc_arity()

void driver::transform_grammar(raw_prog& r, prog_data& pd) {
//	directive d, vector<production> g, const wstring& s) {
	static const set<wstring> b = { L"alpha", L"alnum", L"digit", L"space"};
	transform_string(pd.strs.begin()->second, r, pd.strs.begin()->first);
	for (const production& p : r.g) {
		if (p.p.size() < 2) parse_error(err_empty_prod, p.p[0].e);
		raw_rule l;
		if (p.p.size() == 2 && p.p[1].e == L"null") {
			raw_term t = from_grammar_elem(p.p[0], 1, 1);
			l.add_head(t);
			elem e = {elem::VAR,0,get_var_lexeme(2)};
			l.add_body(from_grammar_elem_nt(r.d[0].rel,e,1,3));
			r.r.push_back(l), l.clear(), l.add_head(t);
			l.add_body(from_grammar_elem_nt(r.d[0].rel,e,3,1));
//			_r.r.push_back({{t, t}});
//			_r.r.back().b[0].neg = true;
		} else {
			size_t v = p.p.size();
			l.add_head(from_grammar_elem(p.p[0], 1, p.p.size()));
			for (size_t n = 1; n < p.p.size(); ++n)
				if (b.find(lexeme2str(p.p[n].e)) != b.end())
					++v,
					l.add_body(from_grammar_elem_builtin(
						r.d[0].rel,
						lexeme2str(p.p[n].e),n));
				else if (p.p[n].type == elem::CHR)
					l.add_body(from_grammar_elem_nt(
						r.d[0].rel, p.p[n], n, n+1));
				else l.add_body(
					from_grammar_elem(p.p[n],n,n+1));
		}
		r.r.push_back(l);
	}
//	raw_term t;
//	append_sym_elem(t.e, L"S"), append_openp(t.e),
//	t.e.push_back({elem::NUM, 0, get_num_lexeme(0)}),
//	t.e.push_back({elem::VAR, 0, get_var_lexeme(1)}),
//	append_closep(t.e), r = transform_bwd(r, {t});
//	r.delrel = dict_get_rel(L"try");
//	return transform_string(s, r, d.rel), array<raw_prog, 2>{ r, _r };
}

/*void driver::insert_goals(raw_prog& r, const std::vector<raw_rule>& g) {
	for (const raw_rule& t : g) {
		raw_term gg;
		cat_relsym_openp(gg, L"G"), cat(gg.e, t.head(0).e),
		term_close(gg), r.r.emplace_back(gg, t.head(0));
	}
}

array<raw_prog, 2> driver::transform_proofs(const vector<raw_prog> rp,
	const std::vector<raw_rule>& g) {
	raw_prog r, _r;
	for (const raw_prog p : rp)
		for (const raw_rule& x : p.r) transform_proofs(x, r, _r);
	insert_goals(r, g);
	return { r, _r };
}*/

#define surround_term(x, y, z) \
	append_sym_elem(x.e, y), cat_in_brackets(x, z), x.calc_arity()

raw_prog driver::transform_bwd(const raw_prog& p,const std::vector<raw_term>&g){
	raw_prog r;
	for (const raw_term& t : g) { // try(goal)
		raw_term x;
		surround_term(x, L"try", t), r.r.push_back(raw_rule(x));
	}
	for (const raw_rule& x : p.r) {
		for (const raw_term& h : x.heads()) { // h :- ..., try(h)
			raw_rule y(h);
			for (const raw_term& b : x.bodies()) y.add_body(b);
			raw_term t;
			surround_term(t, L"try", h), y.add_body(t),
			r.r.push_back(y), y.clear(), y.add_body(t);
			for (const raw_term& b : x.bodies()) { // try(b):-try(h)
				raw_term w;
				surround_term(w, L"try", b), y.add_head(w);
			}
			r.r.push_back(y);
		}
	}
	return r;
}

void driver::transform_proofs(const raw_rule& x, raw_prog& r,const lexeme& rel){
	if (!x.nbodies()) return;
	size_t n = 0;
nxthead:const raw_term &head = x.head(n);
	raw_rule y; // W((h)(b1)(b2)...):-h,b1,b2...
	y.add_body(head);
	for (const raw_term& t : x.bodies()) y.add_body(t);
	y.add_head({}), cat_relsym_openp(y.head(0), rel);
	cat_in_brackets(y.head(0), head);
	for (const raw_term& t : x.bodies()) cat_in_brackets(y.head(0), t);
	term_close(y.head(0)), r.r.push_back(y);
	raw_term gh;
	cat_relsym_openp(gh, L"G"), cat(gh.e, head.e), term_close(gh);
	r.r.push_back(gh);
	if (++n < x.nheads()) goto nxthead;
}
