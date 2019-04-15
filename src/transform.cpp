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
		elem(elem::OPENP, dict.get_lexeme(L"(")),
		elem(elem::VAR, get_var_lexeme(v1)),
		elem(elem::VAR, get_var_lexeme(v2)),
		elem(elem::CLOSEP, dict.get_lexeme(L")"))}, {2}};
}

raw_term driver::from_grammar_elem_nt(const lexeme& r, const elem& c,
	int_t v1, int_t v2) {
	raw_term t{ false, {
		elem(elem::SYM, r),
		elem(elem::OPENP, dict.get_lexeme(L"(")),
		elem(elem::OPENP, dict.get_lexeme(L"(")),
		elem(elem::OPENP, dict.get_lexeme(L"(")),
		elem(elem::VAR, get_var_lexeme(v1)),
		elem(elem::CLOSEP, dict.get_lexeme(L")")),
		elem(elem::CLOSEP, dict.get_lexeme(L")")),
		elem(elem::OPENP, dict.get_lexeme(L"(")),
		c,
		elem(elem::CLOSEP, dict.get_lexeme(L")")),
		elem(elem::OPENP, dict.get_lexeme(L"(")),
		elem(elem::OPENP, dict.get_lexeme(L"(")),
		elem(elem::VAR, get_var_lexeme(v2)),
		elem(elem::CLOSEP, dict.get_lexeme(L")")),
		elem(elem::CLOSEP, dict.get_lexeme(L")")),
		elem(elem::CLOSEP, dict.get_lexeme(L")"))
	}, {}};
	return t.calc_arity(), t;
}

raw_term driver::from_grammar_elem_builtin(const lexeme& r, const wstring& b,
	int_t v){
	return { false, {
		elem(elem::SYM, r),
		elem(elem::OPENP, dict.get_lexeme(L"(")),
		elem(elem::SYM, dict.get_lexeme(b)),
		elem(elem::VAR, get_var_lexeme(v)),
		elem(elem::VAR, get_var_lexeme(v+1)),
		elem(elem::CLOSEP, dict.get_lexeme(L")"))}, {3}};
}

#define from_string_lex(rel, lex, n) raw_rule({ false, { \
		elem(elem::SYM, rel), elem(elem::SYM, dict.get_lexeme(lex)), \
		elem(n), elem(n+1)},{3}})

void driver::transform_string(const wstring& s, raw_prog& r, int_t rel) {
	for (int_t n = 0; n < (int_t)s.size(); ++n) {
		r.r.push_back(raw_rule(raw_term{
			false, {
			elem(elem::SYM, dict.get_rel(rel)),
			elem(elem::OPENP, dict.get_lexeme(L"(")),
			elem(elem::OPENP, dict.get_lexeme(L"(")),
			elem(elem::OPENP, dict.get_lexeme(L"(")),
			elem(n),
			elem(elem::CLOSEP, dict.get_lexeme(L")")),
			elem(elem::CLOSEP, dict.get_lexeme(L")")),
			elem(elem::OPENP, dict.get_lexeme(L"(")),
			elem(s[n]),
			elem(elem::CLOSEP, dict.get_lexeme(L")")),
			elem(elem::OPENP, dict.get_lexeme(L"(")),
			elem(elem::OPENP, dict.get_lexeme(L"(")),
			elem(n+1),
			elem(elem::CLOSEP, dict.get_lexeme(L")")),
			elem(elem::CLOSEP, dict.get_lexeme(L")")),
			elem(elem::CLOSEP, dict.get_lexeme(L")"))},{}}));
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
		if (iswprint(s[n]))
			r.r.push_back(from_string_lex(
					dict.get_rel(rel), L"printable", n));
	}
}

#define append_sym_elem(x, s) (x).push_back(elem(elem::SYM, s))
#define append_openp(x) (x).push_back(elem(elem::OPENP, dict.get_lexeme(L"(")))
#define append_closep(x) (x).push_back(elem(elem::CLOSEP, dict.get_lexeme(L")")))
#define cat(x, y) x.insert(x.end(), y.begin(), y.end())
#define cat_in_brackets(x, y) \
	append_openp((x).e), cat((x).e, (y).e), append_closep((x).e)
#define cat_relsym_openp(x, r) append_sym_elem((x).e, r), append_openp((x).e)
#define term_close(x) append_closep((x).e), (x).calc_arity()

void elim_nullables(set<production>& s) {
	set<elem> nullables;
loop1:	size_t sz = nullables.size();
	for (const production& p : s) {
		bool null = true;
		if (p.p.size() != 2 || !(p.p[1].e == L"null"))
			for (size_t n = 1; null && n != p.p.size(); ++n)
				null &= has(nullables, p.p[n]);
		if (null) nullables.insert(p.p[0]);
	}
	if (sz != nullables.size()) goto loop1;
	set<production> t;
	for (auto p : s)
		if (p.p.size() == 2 && p.p[1].e == L"null")
			t.insert(p);
	for (auto x : t) s.erase(x);
	t.clear();
loop2:	sz = s.size();
	for (auto p : s)
		for (size_t n = 1; n != p.p.size(); ++n)
			if (has(nullables, p.p[n])) {
				production q = p;
				q.p.erase(q.p.begin() + n),
				t.insert(q);
//					r.g.push_back(q);
			}
	for (auto x : t) s.insert(x);
	t.clear();
	if (sz != s.size()) goto loop2;
}

//#define BWD_GRAMMAR
//#define ELIM_NULLS

void driver::transform_grammar(raw_prog& r, size_t len) {
	if (r.g.empty()) return;
	static const set<wstring> b =
		{ L"alpha", L"alnum", L"digit", L"space", L"printable"};
	for (size_t k = 0; k != r.g.size();) {
		if (r.g[k].p.size()<2)parse_error(err_empty_prod,r.g[k].p[0].e);
		size_t n = 0;
		while (n<r.g[k].p.size() && r.g[k].p[n].type != elem::ALT) ++n;
		if (n == r.g[k].p.size()) { ++k; continue; }
		r.g.push_back(
			{vector<elem>(r.g[k].p.begin(), r.g[k].p.begin() + n)});
		r.g.push_back(
			{vector<elem>(r.g[k].p.begin()+n+1, r.g[k].p.end())});
		r.g.back().p.insert(r.g.back().p.begin(), r.g[k].p[0]);
		r.g.erase(r.g.begin() + k);
	}
	for (production& p : r.g) {
		for (size_t n = 0; n < p.p.size(); ++n)
			if (p.p[n].type == elem::STR) {
				lexeme l = p.p[n].e;
				p.p.erase(p.p.begin() + n);
				bool esc = false;
				for (cws s = l[0]+1; s != l[1]; ++s)
					if (*s == L'\\' && !esc) esc=true;
					else p.p.insert(p.p.begin()+n++,
						elem(*s)),esc=false;
			}
	}
#ifdef ELIM_NULLS
	set<production> s;
	for (auto x : r.g) s.insert(x);
	elim_nullables(s), r.g.clear(), r.g.reserve(s.size());
	for (auto x : s) r.g.push_back(x);
	s.clear();
#endif
	raw_rule l;
/*	raw_term m;
	m = fro_grammar_elem({elem::SYM,0,dict.get_lexeme(L"null")},1,1);
	l.add_head(m);
	l.add_body(from_grammar_elem_nt(r.d[0].rel.e,
				{elem::VAR,0,get_var_lexeme(2)},1,3));
	r.r.push_back(l), l.clear(), l.add_head(m);
	l.add_body(from_grammar_elem_nt(r.d[0].rel.e,
				{elem::VAR,0,get_var_lexeme(2)},3,1));
	r.r.push_back(l);*/
	for (production& p : r.g) {
		if (p.p.size() < 2) continue;
		l.clear();
		if (p.p.size() == 2 && p.p[1].e == L"null") {
#ifndef ELIM_NULLS			
			raw_term t = from_grammar_elem(p.p[0], 1, 1);
			l.add_head(t);
			elem e = elem(elem::VAR, get_var_lexeme(2));
			l.add_body(from_grammar_elem_nt(r.d[0].rel.e,e,1,3));
			r.r.push_back(l), l.clear(), l.add_head(t);
			l.add_body(from_grammar_elem_nt(r.d[0].rel.e,e,3,1));
#endif			
//			_r.r.push_back({{t, t}});
//			_r.r.back().b[0].neg = true;
		} else {
//			wcout << p << endl;
			size_t v = p.p.size();
			l.add_head(from_grammar_elem(p.p[0], 1, p.p.size()));
			for (size_t n = 1; n < p.p.size(); ++n) {
				if (p.p[n].type == elem::CHR) {
					l.add_body(from_grammar_elem_nt(
						r.d[0].rel.e, p.p[n], n, n+1));
					continue;
				}
				wstring str = lexeme2str(p.p[n].e);
				if (has(b, str))
					l.add_body(from_grammar_elem_builtin(
						r.d[0].rel.e, str,n)), ++v;
				else l.add_body(
					from_grammar_elem(p.p[n],n,n+1));
			}
		}
		r.r.push_back(l);
	}
	raw_term t;
	append_sym_elem(t.e, dict.get_lexeme(L"S")), append_openp(t.e),
	t.e.push_back(elem((int_t)0)),
	t.e.push_back(elem((int_t)len)),
	append_closep(t.e), t.calc_arity();
#ifdef BWD_GRAMMAR
	transform_bwd(r, {t});
#endif	
//	r.delrel = dict_get_rel(L"try");
//	return transform_string(s, r, d.rel), array<raw_prog, 2>{ r, _r };
}

/*void driver::insert_goals(raw_prog& r, const std::vector<raw_rule>& g) {
	for (const raw_rule& t : g) {
		raw_term gg;
		cat_relsym_openp(gg, L"G"), cat(gg.e, t.head(0).e),
		term_close(gg), r.r.emplace_back(gg, t.head(0));
	}
}*/

void driver::transform_proofs(raw_prog& r, const lexeme& rel) {
	set<raw_rule> s;
	for (auto x : r.r) {
		if (!x.nbodies()) continue;
		size_t n = 0;
nexthead:	const raw_term &head = x.head(n);
		if (head.neg) parse_error(err_proof, head.e[0].e);
		raw_rule y; // W((h)(b1)(b2)...):-h,b1,b2...
		y.add_body(head);
		for (const raw_term& t : x.bodies())
			if (t.neg) parse_error(err_proof, t.e[0].e);
			else y.add_body(t);
		y.add_head({}), cat_relsym_openp(y.head(0), rel);
		cat_in_brackets(y.head(0), head);
		for (const raw_term& t:x.bodies()) cat_in_brackets(y.head(0),t);
		term_close(y.head(0)), s.insert(y);
		if (++n < x.nheads()) goto nexthead;
	}
	for (auto x : s) r.r.push_back(x);
}

#define surround_term(x, y, z) \
	append_sym_elem(x.e, y), cat_in_brackets(x, z), x.calc_arity()

void driver::transform_bwd(raw_prog& p,const std::vector<raw_term>&g){
	lexeme tr = dict.get_lexeme(L"try");
	set<raw_rule> s;
	for (const raw_term& t : g) { // try(goal)
		raw_term x;
		surround_term(x, tr, t), s.insert(raw_rule(x));
	}
	for (const raw_rule& x : p.r) {
		if (!x.nbodies()) s.insert(x);
		else for (const raw_term& h : x.heads()) { // h :- ..., try(h)
			raw_term t;
			surround_term(t, tr, h);
			raw_rule y(h, t);
			for (const raw_term& b : x.bodies()) y.add_body(b);
			s.insert(y), y.clear(), y.add_body(t);
			for (const raw_term& b : x.bodies()) { // try(b):-try(h)
				raw_term w;
				surround_term(w, tr, b), y.add_head(w);
			}
			s.insert(y);
		}
	}
	p.r.clear();
	for (auto x : s) p.r.push_back(x);
}
