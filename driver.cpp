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
using namespace std;

//#define err_null "'null' can appear only by itself on the rhs.\n"
//#define err_null_in_head 
//	"'null' not allowed to appear in the head of positive rules.\n"
#define err_proof	"proof extraction yet unsupported for programs "\
			"with negation or deletion."

wostream& operator<<(wostream& os, const pair<cws, size_t>& p);

size_t arlen(const ints& ar) {
	size_t r = 0;
	for (auto x : ar) if (x > 0) r += x;
	return r;
}

term driver::get_term(const raw_term& r) {
	term t(r.neg, dict_get_rel(r.e[0].e), {}, r.arity);
	for (size_t n = 1; n < r.e.size(); ++n)
		if (r.e[n].type == elem::NUM)
			t.args.push_back(r.e[n].num + chars);
		else if (r.e[n].type == elem::CHR)
			t.args.push_back(*r.e[n].e[0]);
		else if (r.e[n].type!=elem::OPENP && r.e[n].type!=elem::CLOSEP)
			t.args.push_back(dict_get(r.e[n].e));
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

template<typename V, typename X>
void driver::from_func(V f, wstring name, X from, X to, matrices& r) {
	int_t rel = dict_get_rel(name);
	builtin_rels.emplace(rel);
	for (; from != to; ++from)
		if (f(from)) r.insert({term(false, rel, {from}, {1})});
}

matrices driver::get_char_builtins() {
	matrices m;
	from_func<function<int(int)>>(::isspace, L"space", 0, 255, m);
	from_func<function<int(int)>>(::isalnum, L"alnum", 0, 255, m);
	from_func<function<int(int)>>(::isalpha, L"alpha", 0, 255, m);
	from_func<function<int(int)>>(::isdigit, L"digit", 0, 255, m);
	return m;
}

struct lexcmp {
	bool operator()(const lexeme& x, const lexeme& y) const {
		return	x[1]-x[0] != y[1]-y[0] ? x[1]-x[0] < y[1]-y[0]
			: (wcsncmp(x[0], y[0], x[1]-x[0]) < 0);
	}
};

void driver::get_dict_stats(const vector<pair<raw_prog, strs_t>>& v) {
	set<lexeme, lexcmp> rels, syms;
	for (auto x : v) {
		const raw_prog& p = x.first;
		for (const directive& d : p.d)
			chars = max(chars, (int_t)256),
			rels.insert(d.rel),
			nums = max(nums, !d.fname
				? (int_t)(d.arg[1]-d.arg[0])
				: (int_t)fsize(d.arg[0]+1,
					(size_t)(d.arg[1]-d.arg[0]-1)));
		for (const raw_rule& r : p.r)
			for (const raw_term& t : r.b) {
				rels.insert(t.e[0].e);
				for (size_t n = 1; n < t.e.size(); ++n)
					if (t.e[n].type == elem::NUM)
						nums = max(nums, t.e[n].num);
					else if (t.e[n].type == elem::SYM)
						syms.insert(t.e[n].e);
		}
	}
	relsyms = rels.size(), symbols = syms.size();
	for (const lexeme l : syms) dict_get(l);
	for (const lexeme l : rels) dict_get_rel(l);
	bits = msb(usz());
}

wstring driver::directive_load(const directive& d) {
	wstring str(d.arg[0]+1, d.arg[1]-d.arg[0]-1);
	if (!d.fname) return file_read(str);
	for (size_t i = 0; i != str.size(); ++i)
		if (str[i] == L'\\') str.erase(str.begin() + i);
	return str;
}

strs_t driver::directives_load(const vector<directive>& ds) {
	strs_t r;
	for (const directive& d : ds)
		r.emplace(dict_get_rel(d.rel), directive_load(d));
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

raw_prog driver::transform_grammar(
	const directive& d, const vector<production>& g, const wstring& s) {
	raw_prog r;
//	matrices rtxt = get_char_builtins();
//	m.insert(rtxt.begin(), rtxt.end());
	for (const production& p : g) {
		if (p.p.size() < 2) er("empty production.\n");
		raw_rule l;
		l.goal = l.pgoal = false;
		if (p.p.size() == 2 && p.p[1].e == L"null")
			l.b.push_back(from_grammar_elem(p.p[0], 1, 1));
		else {
			l.b.push_back(from_grammar_elem(p.p[0], 1, p.p.size()));
			for (size_t n = 1; n < p.p.size(); ++n)
				if (p.p[n].type == elem::CHR)
					l.b.push_back(from_grammar_elem_nt(d.rel
						,p.p[n],n,n+1));
				else l.b.push_back(
					from_grammar_elem(p.p[n],n,n+1));
		}
		r.r.push_back(l);
	}
	return transform_string(s, r, d.rel), r;
}

#define append_sym_elem(x, s) (x).push_back({elem::SYM, 0, get_lexeme(s)})
#define append_openp(x) (x).push_back({elem::OPENP, 0, get_lexeme(L"(")})
#define append_closep(x) (x).push_back({elem::CLOSEP, 0, get_lexeme(L")")})
#define cat(x, y) x.insert(x.end(), y.begin(), y.end())

array<raw_prog, 2> driver::transform_proofs(const raw_prog& p,
	const std::vector<raw_rule>& g) {
	raw_prog r, _r;
	for (const raw_rule& x : p.r) {
		if (x.b.size() == 1) continue;
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
			append_openp(gg.e), cat(gg.e, t.b[0].e),
			append_closep(gg.e), gg.calc_arity(),
			_r.r.push_back({{gg, t.b[0]}, false, false});
		}
		for (size_t n = 1; n != x.b.size(); ++n) {
			raw_rule z;
			z.b.push_back({}), z.b[0].neg = false,
			append_sym_elem(z.b[0].e, L"G"), append_openp(z.b[0].e),
			cat(z.b[0].e, x.b[n].e), append_closep(z.b[0].e),
			z.b.push_back(gh), z.b.push_back(y.b[0]),
			z.b[0].calc_arity(), r.r.push_back(z);
			// ~W((h)(b1)...) :- ~G(b1).
			y.b[0].neg = gh.neg = z.b[0].neg = true;
			_r.r.push_back({{y.b[0], gh}, false, false}),
			_r.r.push_back({{y.b[0], z.b[0]}, false, false}),
			y.b[0].neg = gh.neg = false;
		}
		y.b[0].neg = gh.neg = true;
		// ~W((h)(b1)...) :- ~G(h).
		_r.r.push_back({{y.b[0], gh}, false, false});
		// ! W(...)
		_r.outrel = dict_get_rel(L"W");
		//_r.r.push_back({{y.b[0]}, true, false});
	}
	return { r, _r };
}

vector<pair<raw_prog, strs_t>> driver::transform(const raw_prog& p) {
	vector<pair<raw_prog, strs_t>> r;
	vector<raw_rule> pg;
	wcout << L"original program:"<<endl<<p;
	strs_t s = directives_load(p.d);
	for (const raw_rule& x : p.r)
		if (x.pgoal) pg.push_back(x);
	if (!p.g.empty()) {
		if (!p.d.size()) er("grammar without input string.\n");
		if (p.d.size()>1)er("only one string allowed given grammar.\n");
		r.push_back({transform_grammar(p.d[0],p.g,s.begin()->second),s});
	}
	r.push_back({p, s});
	if (!pg.empty()) {
		auto x = transform_proofs(p.g.empty()?p:r[0].first, pg);
		r.push_back({move(x[0]),{}}), r.push_back({move(x[1]),{}});
	}
	return r;
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
	prog = new lp(move(m), move(g), p.outrel, usz(), s, prog);
}

driver::driver(FILE *f) : driver(move(raw_progs(f))) {}
driver::driver(wstring s) : driver(move(raw_progs(s))) {}

driver::driver(raw_progs rp) {
	DBG(drv = this;)
	vector<pair<raw_prog, strs_t>> v;
	for (size_t n = 0; n < rp.p.size(); ++n)
		for (auto x : transform(rp.p[n]))
			v.push_back({move(x.first), move(x.second)});
	get_dict_stats(v);
	for (auto x : v) prog_init(move(x.first), move(x.second));
}

bool driver::pfp() { return prog->pfp() ? printdb(wcout, prog), true : false; }

matrix driver::from_bits(size_t x, ints art, int_t rel) const {
	size_t ar = arlen(art);
	vbools s = allsat(x, bits * ar);
	matrix r(s.size());
	for (term& v : r) v = term(false, rel, ints(ar), art);
	size_t n = s.size(), i, b;
	while (n--)
		for (i = 0; i != ar; ++i)
			for (b = 0; b != bits; ++b)
				if (s[n][i * bits + b])
					r[n].args[i] |= 1 << (bits - b - 1);
	return r;
}

term driver::one_from_bits(size_t x, ints art, int_t rel) const {
	size_t ar = arlen(art);
	bools s(bits * ar, true);
	if (!bdd_onesat(x, bits * ar, s)) return term();
	term r(1, rel, ints(ar), art);
	for (size_t i = 0; i != ar; ++i)
		for (size_t b = 0; b != bits; ++b)
			if (s[i * bits + b])
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
wostream& printndb(wostream& os, lp *p) { return drv->printndb(os, p); }
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
		if (builtin_rels.find(x.first.first) == builtin_rels.end())
			printbdd(os,from_bits(*x.second,
				x.first.second,x.first.first));
	return os;
}
wostream& driver::printndb(wostream& os, lp *p) const {
	for (auto x : p->ndb)
		if (builtin_rels.find(x.first.first) == builtin_rels.end())
			printbdd(os,from_bits(*x.second,
				x.first.second,x.first.first));
	return os;
}
