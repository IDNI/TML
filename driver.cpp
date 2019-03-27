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

#define err_null "'null' can appear only by itself on the rhs.\n"
#define err_null_in_head \
	"'null' not allowed to appear in the head of positive rules.\n"

wostream& operator<<(wostream& os, const pair<cws, size_t>& p);

size_t arlen(const ints& ar) {
	size_t r = 0;
	for (auto x : ar) if (x > 0) r += x;
	return r;
}

term driver::get_term(const raw_term& r) {
	term t(r.neg, dict_get(r.e[0].e), {}, r.arity);
	for (size_t n = 1; n < r.e.size(); ++n)
		if (r.e[n].type == elem::NUM)
			t.args.push_back(r.e[n].num + chars);
		else if (r.e[n].type == elem::CHR)
			t.args.push_back(*r.e[n].e[0]+1);
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

driver::driver(FILE *f) : driver(raw_progs(f)) {}
driver::driver(wstring s) : driver(raw_progs(s)) {}

struct lexcmp {
	bool operator()(const lexeme& x, const lexeme& y) const {
		return	x[1]-x[0] != y[1]-y[0] ? x[1]-x[0] < y[1]-y[0]
			: (wcsncmp(x[0], y[0], x[1]-x[0]) < 0);
	}
};

void driver::get_dict_stats(const raw_progs& ps) {
	set<lexeme, lexcmp> rels, syms;
	for (const raw_prog& p : ps.p) {
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

driver::strs_t driver::directives_load(const raw_prog& p) {
	strs_t r;
	for (const directive& d : p.d) {
		wstring str(d.arg[0]+1, d.arg[1]-d.arg[0]-1);
		if (!d.fname)
			for (size_t i = 0; i != str.size(); ++i)
				if (str[i] == L'\\') str.erase(str.begin()+i);
		r.emplace(dict_get(d.rel), d.fname ? file_read(str) : str);
	}
	return r;
}

void driver::grammar_to_rules(const vector<production>& g, matrices& m,
	int_t rel) {
	int_t null = dict_get_rel(L"null");
	for (const production& p : g) {
		if (p.p.size() < 2) er("empty production.\n");
		int_t x = dict_get_rel(p.p[0].e);
		if (p.p.size() == 2 && p.p[1].type == elem::SYM &&
			null == dict_get_rel(p.p[1].e)) {
			m.insert({	term(false, x, {-1,-1}, {2}),
					term(false, null, {}, {0})});
			continue;
		}
		matrix t;
		int_t v = -1;
		t.emplace_back(false, x, ints{-1, -(int_t)p.p.size()}, ints{2});
		for (size_t n = 1; n < p.p.size(); ++n, --v)
			if (p.p[n].type == elem::SYM) {
				if (null==(x=dict_get_rel(p.p[n].e)))
					er(err_null);
				t.emplace_back(false, x, ints{v, v-1}, ints{2});
			}
			else if (p.p[n].type == elem::CHR) {
				if(!n)er("grammar lhs cannot be a terminal.\n");
				t.emplace_back(false, rel,
					ints{*p.p[n].e[0]+1, v, v-1}, ints{3});
			} else er("unexpected grammar node.\n");
		m.emplace(move(t));
	}
	DBG(wcout << m << endl;)
}

void driver::prog_init(const raw_prog& p, const strs_t& s){
	matrices m;
	matrix g, pg;
	if (p.g.size() && s.size() > 1)
		er("only one string allowed given grammar.\n");
	if (!p.d.empty()) {
		matrices rtxt = get_char_builtins();
		m.insert(rtxt.begin(), rtxt.end());
	}
	for (const raw_rule& x : p.r)
		if (x.goal && !x.pgoal)
			assert(x.b.size() == 1), g.push_back(get_term(x.b[0]));
		else if (x.pgoal)
			assert(x.b.size() == 1), pg.push_back(get_term(x.b[0]));
		else m.insert(get_rule(x));
	for (auto x : s) {
		for (int_t n = 0; n != (int_t)x.second.size()-1; ++n)
			m.insert({term(false, x.first,
				{x.second[n],n+256,n+257},{3})});
		m.insert({term(false, x.first, { x.second.back(),
			(int_t)x.second.size()+256, (int_t)x.second.size()+256 }
			, {3})});
	}
	if (p.g.size()) grammar_to_rules(p.g, m, s.begin()->first);
	prog = new lp(move(m), move(g), move(pg), usz(), prog);
	prog->add_fact(term(false, null, {}, {0}));
//	DBG(printdb(wcout<<L"pos:"<<endl, prog);)
//	DBG(printndb(wcout<<L"neg:"<<endl, prog)<<endl;)
	if (!s.empty())
		for (size_t x : builtin_rels) // to suppress builtins on output
			builtin_symbdds.insert(prog->get_sym_bdd(x, 0));
}

driver::driver(const raw_progs& rp) {
	DBG(drv = this;)
	get_dict_stats(rp);
	for (size_t n = 0; n != rp.p.size(); ++n)
		prog_init(rp.p[n], directives_load(rp.p[n]));
}

bool driver::pfp() {
	if (!prog->pfp()) return false;
//	size_t db = prog->db;
//	for (size_t x : builtin_symbdds) db = bdd_and_not(db, x);
	return printdb(wcout, prog), true;
}

matrix driver::from_bits(size_t x, ints art, int_t rel) const {
	size_t ar = arlen(art);
	vbools s = allsat(x, bits * ar);
	matrix r(s.size());
	for (term& v : r) v = term(1, rel, ints(ar), art);
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
	os << dict_get(t.rel) << L'(';
	size_t ar = 0, n = 0;
	for (;ar != t.arity.size(); ++ar)
		for (size_t k = 0; k < (size_t)t.arity[ar]; ++k) {
			if (t.args[n] < 0 || (size_t)t.args[n] < nsyms())
				os << dict_get(t.args[n]);
			else os << L'[' << t.args[n] << L']';
			if (++n != t.args.size()) os << L' ';
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
//wostream& printbdd(wostream& os, size_t t, size_t bits, size_t ar) {
//	return drv->printbdd(os, from_bits(t,bits,ar));
//}
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
