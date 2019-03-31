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
#include <map>
#include <set>
#include <string>
#include <cstring>
#include <sstream>
#include <forward_list>
#include <functional>
#include <cctype>
#include "driver.h"
#include "rule.h"
using namespace std;

//#define err_null "'null' can appear only by itself on the rhs.\n"
//#define err_null_in_head 
//	"'null' not allowed to appear in the head of positive rules.\n"
#define err_proof	"proof extraction yet unsupported for programs "\
			"with negation or deletion."

wostream& operator<<(wostream& os, const pair<cws, size_t>& p);

bool operator==(const lexeme& l, const wstring& s) {
	if ((size_t)(l[1]-l[0]) != s.size()) return false;
	return !wcsncmp(l[0], s.c_str(), l[1]-l[0]);
}

term driver::get_term(const raw_term& r) {
	term t(r.neg, dict_get_rel(r.e[0].e), {}, r.arity);
	if (r.e[0].e == L"space") t.b = term::SPACE;
	else if (r.e[0].e == L"digit") t.b = term::DIGIT;
	else if (r.e[0].e == L"alpha") t.b = term::ALPHA;
	else if (r.e[0].e == L"alnum") t.b = term::ALNUM;
	else t.b = term::NONE;
	for (size_t n = 1; n < r.e.size(); ++n)
		if (r.e[n].type == elem::NUM)
			t.args.push_back(r.e[n].num + chars);
		else if (r.e[n].type == elem::CHR)
			t.args.push_back(*r.e[n].e[0]);
		else if (r.e[n].type!=elem::OPENP && r.e[n].type!=elem::CLOSEP)
			t.args.push_back(dict_get(r.e[n].e));
	if (t.b != term::NONE && t.arity != ints{1})
		parse_error(L"invalid arity for unary builtin", r.e[0].e);
	return t;
}

matrix driver::get_rule(const raw_rule& r) {
	matrix m;
	for (auto x : r.b) m.push_back(get_term(x));
//	if (m[0][0] > 0)
//		for (size_t i = 1; i < m[0].size(); ++i)
//			if (m[0][i] == null) er(err_null_in_head);
	return m;
}

struct lexcmp {
	bool operator()(const lexeme& x, const lexeme& y) const {
		return	x[1]-x[0] != y[1]-y[0] ? x[1]-x[0] < y[1]-y[0]
			: (wcsncmp(x[0], y[0], x[1]-x[0]) < 0);
	}
};

vector<strs_t> driver::get_dict_stats(
	const vector<pair<raw_prog, map<lexeme, wstring>>>& v) {
	set<lexeme, lexcmp> rels, syms;
	for (auto x : v) {
		const raw_prog& p = x.first;
		for (const directive& d : p.d)
			chars = max(chars, (int_t)256),
			rels.insert(d.rel),
			nums = max(nums, (!d.fname
				? (int_t)(d.arg[1]-d.arg[0])
				: (int_t)fsize(d.arg[0]+1,
					(size_t)(d.arg[1]-d.arg[0]-1)))+1);
		for (const raw_rule& r : p.r)
			for (const raw_term& t : r.b) {
				rels.insert(t.e[0].e);
				for (size_t n = 1; n < t.e.size(); ++n)
					if (t.e[n].type == elem::NUM)
						nums = max(nums, t.e[n].num+1);
					else if (t.e[n].type == elem::SYM)
						syms.insert(t.e[n].e);
		}
		for (auto y : x.second) rels.insert(y.first);
	}
	if (!syms.size() && !nums && !chars) {
		wcerr<<L"warning: empty domain, adding dummy element."<<endl;
		++nums;
	} else for (const lexeme l : syms) dict_get(l);
	for (const lexeme l : rels) dict_get_rel(l);
	vector<strs_t> r;
	for (auto x : v) {
		strs_t s;
		for (auto y : x.second)
			s[dict_get_rel(y.first)] = move(y.second);
		r.push_back(move(s));
	}
	relsyms = rels.size(), symbols = syms.size(), bits = msb(usz());
	return r;
}

wstring driver::directive_load(const directive& d) {
	wstring str(d.arg[0]+1, d.arg[1]-d.arg[0]-2);
	if (d.fname) return file_read(str);
	for (size_t i = 0; i != str.size(); ++i)
		if (str[i] == L'\\') str.erase(str.begin() + i);
	return str;
}

map<lexeme, wstring> driver::directives_load(const vector<directive>& ds) {
	map<lexeme, wstring> r;
	for (const directive& d : ds) r.emplace(d.rel, directive_load(d));
	return r;
}

lexeme driver::get_lexeme(const wstring& s) {
	auto it = strs_extra.find(s.c_str());
	cws r;
	if (it == strs_extra.end()) strs_extra.insert(r = wcsdup(s.c_str()));
	else r = *it;
	return { r, r + wcslen(r) };
}

lexeme driver::get_char_lexeme(wchar_t c) {
	wstring s;
	return get_lexeme(s += c);
}

lexeme driver::get_num_lexeme(int_t n) { return get_lexeme(to_wstring(n)); }

lexeme driver::get_var_lexeme(int_t i) {
	wstring s = L"?v";
	return get_lexeme(s += to_wstring(i));
}

#define from_grammar_elem(v, v1, v2) \
	raw_term{ false, {v, \
		{elem::OPENP, 0, get_lexeme(L"(")}, \
		{elem::VAR, 0, get_var_lexeme(v1)}, \
		{elem::VAR, 0, get_var_lexeme(v2)}, \
		{elem::CLOSEP, 0, get_lexeme(L")")}}, {2}}

#define from_grammar_elem_nt(r, c, v1, v2) \
	raw_term{ false, {\
		{elem::SYM, 0, r}, \
		{elem::OPENP, 0, get_lexeme(L"(")}, \
		c, \
		{elem::VAR, 0, get_var_lexeme(v1)}, \
		{elem::VAR, 0, get_var_lexeme(v2)}, \
		{elem::CLOSEP, 0, get_lexeme(L")")}}, {3}}

#define from_grammar_elem_builtin(r, b, v, v1, v2) \
	array<raw_term, 2>{raw_term{ false, {\
		{elem::SYM, 0, r}, \
		{elem::OPENP, 0, get_lexeme(L"(")}, \
		{elem::VAR, 0, get_var_lexeme(v)}, \
		{elem::VAR, 0, get_var_lexeme(v1)}, \
		{elem::VAR, 0, get_var_lexeme(v2)}, \
		{elem::CLOSEP, 0, get_lexeme(L")")}}, {3}}, \
		{raw_term{false, {\
		{elem::SYM, 0, b}, \
		{elem::OPENP, 0, get_lexeme(L"(")}, \
		{elem::VAR, 0, get_var_lexeme(v)}, \
		{elem::CLOSEP, 0, get_lexeme(L")")}}, {1}}}}

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

void driver::transform_string(const wstring& s, raw_prog& r, const lexeme& rel){
	for (int_t n = 0; n < (int_t)s.size(); ++n) {
		raw_rule l;
		l.goal = l.pgoal = false;
		l.b.push_back(raw_term{ false, {
			{elem::SYM, 0, rel},
			{elem::CHR, 0, get_char_lexeme(s[n])},
			{elem::NUM, n, get_num_lexeme(n)},
			{elem::NUM, n+1, get_num_lexeme(n+1)}},{3}});
		r.r.push_back(l);
	}
}

#define lexeme2str(l) wstring((l)[0], (l)[1]-(l)[0])

array<raw_prog, 2> driver::transform_grammar(
	const directive& d, const vector<production>& g, const wstring& s) {
	static set<wstring> b = { L"alpha", L"alnum", L"digit", L"space" };
	raw_prog r, _r;
	r.d.push_back(d);
	for (const production& p : g) {
		if (p.p.size() < 2)
			parse_error(L"empty production.\n", p.p[0].e);
		raw_rule l;
		if (p.p.size() == 2 && p.p[1].e == L"null") {
			raw_term t = from_grammar_elem(p.p[0], 1, 1);
			l.b.push_back(t);
			_r.r.push_back({{t, t}});
			_r.r.back().b[0].neg = true;
		} else {
			size_t v = p.p.size();
			l.b.push_back(from_grammar_elem(p.p[0], 1, p.p.size()));
			for (size_t n = 1; n < p.p.size(); ++n)
				if (b.find(lexeme2str(p.p[n].e)) != b.end()) {
					++v;
					auto x=from_grammar_elem_builtin(d.rel,
						p.p[n].e, v, n, n+1);
					l.b.push_back(x[0]),l.b.push_back(x[1]);
				}
				else if (p.p[n].type == elem::CHR)
					l.b.push_back(from_grammar_elem_nt(d.rel
						,p.p[n],n,n+1));
				else l.b.push_back(
					from_grammar_elem(p.p[n],n,n+1));
		}
		r.r.push_back(l);
	}
	return transform_string(s, r, d.rel), array<raw_prog, 2>{ r, _r };
}

#define append_sym_elem(x, s) (x).push_back({elem::SYM, 0, get_lexeme(s)})
#define append_openp(x) (x).push_back({elem::OPENP, 0, get_lexeme(L"(")})
#define append_closep(x) (x).push_back({elem::CLOSEP, 0, get_lexeme(L")")})
#define cat(x, y) x.insert(x.end(), y.begin(), y.end())

array<raw_prog, 2> driver::transform_proofs(const vector<raw_prog> rp,
	const std::vector<raw_rule>& g) {
	raw_prog r, _r;
	for (const raw_prog p : rp)
		for (const raw_rule& x : p.r)
			transform_proofs(x, r, _r, g);
	return { r, _r };
}

void driver::transform_proofs(const raw_rule& x, raw_prog &r, raw_prog &_r,
	const std::vector<raw_rule>& g) {
	assert(x.b.size());
	if (x.b.size() == 1) return;
	// W((h)(b1)(b2)...):-h,b1,b2...
	raw_rule y;
	y.b.push_back({}), y.b[0].neg = false,
	y.b.insert(y.b.begin() + 1, x.b.begin(), x.b.end()),
	append_sym_elem(y.b[0].e, L"W"), append_openp(y.b[0].e);
	for (const raw_term& t : x.b) 
		append_openp(y.b[0].e), cat(y.b[0].e, t.e),
		append_closep(y.b[0].e);
	append_closep(y.b[0].e), y.b[0].calc_arity(), r.r.push_back(y);
	// G(b1) :- G(h), W((h)(b1)...)
	raw_term gh;
	gh.neg = false, append_sym_elem(gh.e, L"G"), append_openp(gh.e),
	cat(gh.e, x.b[0].e), append_closep(gh.e), gh.calc_arity();
	for (const raw_rule& t : g) {
		raw_term gg;
		gg.neg = false, append_sym_elem(gg.e, L"G"),
		append_openp(gg.e), cat(gg.e, t.b[0].e), append_closep(gg.e),
		gg.calc_arity(), r.r.push_back({{gg, t.b[0]}, false, false});
	}
	raw_rule z;
	for (size_t n = 1; n != x.b.size(); ++n)
		z.b.push_back({}), z.b[0].neg = false,
		append_sym_elem(z.b[0].e, L"G"), append_openp(z.b[0].e),
		cat(z.b[0].e, x.b[n].e), append_closep(z.b[0].e),
		z.b.push_back(gh), z.b.push_back(y.b[0]), z.b[0].calc_arity(),
		r.r.push_back(z), y.b[0].neg = gh.neg = z.b[0].neg = true,
		// ~W((h)(b1)...) :- ~G(b1).
		_r.r.push_back({{y.b[0], gh}, false, false}),
		_r.r.push_back({{y.b[0], z.b[0]}, false, false}),
		y.b[0].neg = gh.neg = false, z.clear();
	// ~W((h)(b1)...) :- ~G(h).
	// ! W(...)
	y.b[0].neg = gh.neg = true, _r.r.push_back({{y.b[0], gh}, false,false}),
	_r.delrel = dict_get_rel(L"G");
}

vector<pair<raw_prog, map<lexeme, wstring>>> driver::transform(raw_prog p) {
	vector<pair<raw_prog, map<lexeme, wstring>>> r;
	//DBG(wcout << L"original program:"<<endl<<p;)
	auto s = directives_load(p.d);
	if (!p.g.empty()) {
		if (!p.d.size()) _er("grammar without input string.\n");
		if (p.d.size()>1)_er("only one string allowed given grammar.\n");
		auto x = transform_grammar(p.d[0], p.g, s.begin()->second);
		r.push_back({x[0],s}), r.push_back({x[1],{}}), p.g.clear(),
		p.d.erase(p.d.begin());
	} else for (auto x : s) transform_string(x.second, p, x.first);
	return r.push_back({p, s}), r;
}

void driver::prog_init(const raw_prog& p, strs_t s) {
	matrices m;
	matrix g, pg;
	for (const raw_rule& x : p.r)
		if (x.goal && !x.pgoal)
			assert(x.b.size() == 1), g.push_back(get_term(x.b[0]));
		else if (x.pgoal)
			assert(x.b.size() == 1), pg.push_back(get_term(x.b[0]));
		else m.insert(get_rule(x));
	prog = new lp(move(m), move(g), p.delrel, usz(), s, prog);
}

driver::driver(FILE *f, bool print_transformed) 
	: driver(move(raw_progs(f)), print_transformed) {}
driver::driver(wstring s, bool print_transformed) 
	: driver(move(raw_progs(s)), print_transformed) {}

driver::driver(raw_progs rp, bool print_transformed) {
	DBG(drv = this;)
	vector<pair<raw_prog, map<lexeme, wstring>>> v;
	for (size_t n = 0; n < rp.p.size(); ++n)
		for (auto x : transform(rp.p[n]))
			v.push_back({move(x.first), move(x.second)});
	vector<raw_rule> pg;
	for (auto x : v)
		for (const raw_rule& y : x.first.r)
			if (y.pgoal) pg.push_back(y);
	if (!pg.empty()) {
		vector<raw_prog> y;
		for (auto x : v) y.push_back(x.first);
		auto x = transform_proofs(y, pg);
		v.push_back({move(x[0]),{}}), v.push_back({move(x[1]),{}});
	}
	if (print_transformed)
		for (auto x : v)
			wcout << L'{' << endl << x.first << L'}' << endl;
	auto y = get_dict_stats(v);
	for (size_t n = 0; n != v.size(); ++n)
		prog_init(move(v[n].first), move(y[n]));
}

bool driver::pfp() { return prog->pfp() ? printdb(wcout, prog), true : false; }

matrix driver::from_bits(size_t x, ints art, int_t rel) const {
	size_t ar = arlen(art);
	vbools s = allsat(x, bits * ar);
	matrix r(s.size());
	for (term& v : r) v = term(false, rel, ints(ar, 0), art);
	size_t n = s.size(), i, b;
	while (n--)
		for (i = 0; i != ar; ++i)
			for (b = 0; b != bits; ++b)
				//if (s[n][i * bits + b])
				if (s[n][POS(b, bits, i, ar)])
					r[n].args[i] |= 1 << b;//(bits - b - 1);
	return r;
}

term driver::one_from_bits(size_t x, ints art, int_t rel) const {
	size_t ar = arlen(art);
	bools s(bits * ar, true);
	if (!bdd_onesat(x, bits * ar, s)) return term();
	term r(1, rel, ints(ar), art);
	for (size_t i = 0; i != ar; ++i)
		for (size_t b = 0; b != bits; ++b)
			//if (s[i * bits + b])
			if (s[POS(b, bits, i, ar)])
				r.args[i] |= 1 << (bits - b - 1);
	return r;
}

wostream& driver::printbdd(wostream& os, const matrices& t) const {
	for (auto m : t) printbdd(os, m) << endl;
	return os;
}

wostream& driver::print_term(wostream& os, const term& t) const {
	if (t.neg) os << L'~';
	os << dict_get(t.rel) << L'(';
	for (size_t ar = 0, n = 0; ar != t.arity.size();) {
		while (t.arity[ar] == -1) ++ar, os << L'(';
		for (int_t k = 0; k != t.arity[ar]; ++k) {
			if (t.args[n] < 0 || (size_t)t.args[n] < nsyms())
				os << dict_get(t.args[n]);
			else os << L'[' << t.args[n] << L']';
			if (++n != t.args.size()) os << L' ';
		}
		++ar;
		while (ar<t.arity.size()&&t.arity[ar] == -2) ++ar, os<<L')';
	}
	return os << L')';
}

wostream& driver::printbdd(wostream& os, const matrix& t) const {
	set<wstring> s;
	for (auto v : t) {
		wstringstream ss;
		print_term(ss, v);
		s.emplace(ss.str());
	}
	for (auto& x : s) os << x << endl;
	return os;
}

#ifdef DEBUG
driver* drv;
wostream& printdb(wostream& os, lp *p) { return drv->printdb(os, p); }
wostream& printdiff(wostream& os, const lp::diff_t& d) {
	return drv->printdiff(os, d);
}
wostream& printbdd(wostream& os, size_t t, ints ar, int_t rel){
	return drv->printbdd(os, t, ar, rel);
}
wostream& printbdd_one(wostream& os, size_t t, ints ar, int_t rel) {
	return drv->printbdd_one(os, t, ar, rel);
}
#endif

wostream& operator<<(wostream& os, const pair<cws, size_t>& p) {
	for (size_t n = 0; n != p.second; ++n) os << p.first[n];
	return os;
}

wostream& driver::printbdd(wostream& os, size_t t, ints ar, int_t rel) const {
	return printbdd(os, from_bits(t, ar, rel));
}

wostream& driver::printbdd_one(wostream& os, size_t t, ints ar, int_t rel)const{
	os << "one of " << bdd_count(t, bits * arlen(ar)) << " results: ";
	return print_term(os, one_from_bits(t, ar, rel));
}

wostream& driver::printdb(wostream& os, lp *p) const {
	for (auto x : p->db)
		if (builtin_rels.find(x.first.first) == builtin_rels.end()) {
//			for (int_t i : x.first.second) wcout << i << ' ';
//			wcout << endl;
			printbdd(os, from_bits(*x.second,
				x.first.second,x.first.first));
		}
	return os;
}

wostream& driver::printdiff(wostream& os, const lp::diff_t& d) const {
	for (auto x : d)
		if (builtin_rels.find(x.first.first) == builtin_rels.end())
			printbdd(os,from_bits(x.second,
				x.first.second,x.first.first));
	return os;
}
