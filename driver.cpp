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

wostream& operator<<(wostream& os, const pair<cws, size_t>& p);

term driver::get_term(const raw_term& r) {
	term t;
	t.push_back(r.neg ? -1 : 1);
	for (const elem& e : r.e)
		if (e.type == elem::NUM) t.push_back(e.num);
		else if (e.type == elem::CHR) t.push_back(*e.e[0]+1);
		else t.push_back(dict_get(e.e));
	return t;
}

matrix driver::get_rule(const raw_rule& r) {
	matrix m;
	m.push_back(get_term(r.h));
	for (auto x : r.b) m.push_back(get_term(x));
	return m;
}

void driver::term_pad(term& t, size_t ar) {
	size_t l;
	if ((l=t.size())<ar+1) t.resize(ar+1), fill(t.begin()+l, t.end(), pad);
}

string ws2s(const wstring& s) { return string(s.begin(), s.end()); }
void driver::rule_pad(matrix& t, size_t ar) { for (term& x:t) term_pad(x, ar); }

matrix driver::rule_pad(const matrix& t, size_t ar) {
	matrix r;
	rule_pad(r = t, ar);
	return r;
}

template<typename V, typename X>
void driver::from_func(V f, wstring name, X from, X to, matrices& r) {
	int_t rel = dict_get(name);
	builtin_rels.emplace(rel);
	for (; from != to; ++from) if (f(from)) r.insert({{ 1, rel, from }});
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

size_t get_nums(const raw_prog& p) {
	size_t nums = 0;
	for (size_t k = 0; k != p.d.size(); ++k)
		nums = max(nums, !p.d[k].fname
			? (size_t)(256+p.d[k].arg[1]-p.d[k].arg[0])
			: (size_t)(256+(int_t)fsize(ws2s(wstring(p.d[k].arg[0]+1
				,p.d[k].arg[1]-p.d[k].arg[0]-1)).c_str())));
	return nums;
}

void driver::directives_load(const raw_prog& p, size_t n) {
	for (size_t k = 0; k != p.d.size(); ++k) {
		wstring str(p.d[k].arg[0]+1, p.d[k].arg[1]-p.d[k].arg[0]-1);
		if (!p.d[k].fname) for (size_t i = 0; i != str.size(); ++i)
			if (str[i] == L'\\') str.erase(str.begin()+i);
		strs[n].emplace(dict_get(p.d[k].rel), p.d[k].fname ?
			file_read_text(str) : str);
	}
}

void driver::calc_lens(const raw_prog& p, size_t& ar) {
	for (auto x : p.r) {
		ar = max(ar, x.h.e.size());
		for (auto e : x.h.e) if (e.type==elem::SYM) dict_get(e.e);
		for (auto y : x.b) {
			ar = max(ar, y.e.size());
			for (auto e : y.e)
				if (e.type==elem::SYM) dict_get(e.e);
		}
	}
}

void driver::prog_init(const raw_prog& p, size_t ar, const matrices& rtxt) {
	matrices m, g, pg;
	m.insert(rtxt.begin(), rtxt.end());
	for (const raw_rule& x : p.r)
		(x.goal ? x.pgoal ? pg : g : m).insert(get_rule(x));
	prog_add(move(m), move(g), move(pg), ar);
}

void driver::prog_add(matrices m, matrices g, matrices pg, size_t ar) {
	progs.emplace_back(new lp(dict_bits(), ar, nsyms()));
	while (!g.empty()) {
		matrix x = move(*g.begin());
		m.erase(m.begin()),progs.back()->goal_add(rule_pad(move(x),ar));
	}
	while (!pg.empty()) {
		matrix x = move(*pg.begin());
		m.erase(m.begin()),progs.back()->pgoal_add(rule_pad(move(x),ar));
	}
	for (auto x : strs[progs.size()-1])
		for (int_t n = 0; n != (int_t)x.second.size(); ++n)
			progs.back()->rule_add(rule_pad({{ 1, x.first,
				x.second[n]+1, n + 257, n + 258 }}, ar));
	while (!m.empty()) {
		matrix x = move(*m.begin());
		m.erase(m.begin()),progs.back()->rule_add(rule_pad(move(x),ar));
	}
	builtin_symbdds.emplace_back();
	if (strs[progs.size()-1].empty()) return;
	for (size_t x : builtin_rels) // used to suppress builtins on output
		builtin_symbdds.back().insert(progs.back()->get_sym_bdd(x, 0));
}

driver::driver(const raw_progs& rp) {
	DBG(drv = this;)
	bool txt;
	size_t ar = 0, ntxt = 0;
	matrices rtxt;
	syms.push_back(0), lens.push_back(0);
	for (size_t n = 0; n != rp.p.size(); ++n) {
		if (strs.emplace_back(), rp.p[n].d.size()) ar=max(ar,(size_t)4);
		if ((txt = (nums=max((size_t)nums, get_nums(rp.p[n])))))
			ntxt = min(ntxt, n);
	}
	if (txt) rtxt = get_char_builtins();
	for (size_t n = 0; n != rp.p.size(); ++n)
		directives_load(rp.p[n], n), calc_lens(rp.p[n], ar),
		prog_init(rp.p[n], ar, n >= ntxt ? rtxt : matrices());
}

bool driver::pfp(lp *p) {
	size_t d, add, del, t;
	set<size_t> pf;
//	wcout << V.size() << endl;
	for (set<int_t> s;;) {
		add=del=F, s.emplace(d = p->db), p->fwd(add, del);
		if ((t = bdd_and_not(add, del)) == F && add != F)
			return false; // detect contradiction
		else p->db = bdd_or(bdd_and_not(p->db, del), t);
		if (d == p->db) break;
		if (s.find(p->db) != s.end()) return false;
	}
	return true;
//	if (!proof) return true;
/*	prog_add(move(*proof), {}, p->proof_arity(), map<int_t, wstring>(), 0);
	lp *q = progs.back();
	*padd = del = F, q->db = p->get_varbdd();
	q->fwd(*padd, del, 0), delete q, progs.erase(progs.end()-1);

	prog_add(move(*proof), {}, p->proof_arity(), map<int_t, wstring>(), 0);
	q = progs.back();
	q->db = *padd;
	matrices s = p->goals;
	int_t g = dict_get(L"goal");
	for (size_t n = 0; n != p->maxw(); ++n)
		for (size_t i = 1; i != p->rules[i].bd.size(); ++i) {
			matrix m = {{1},{1},{1}};
			for (int_t k = 1; k <= p->ar; ++k)
				m[0].push_back(i*p->ar-k);
			m[0].push_back(g);
			for (int_t k = 1; k <= p->ar; ++k)
				m[1].push_back(-k);
			m[1].push_back(g);
			for (int_t k = 1; k <= p->proof_arity(); ++k)
				m[2].push_back(-k);
			wcout << m << endl;
			s.emplace(move(m));
		}
	pfp(q, 0, &add);
	delete q, progs.erase(progs.end()-1);
	matrix m = {{-1},{-1},{1}};
	for (int_t k = 1; k <= p->proof_arity(); ++k)
		m[0].push_back(-k), m[2].push_back(-k);
	m[0].push_back(g), m[1].push_back(g);
	for (int_t k = 1; k <= p->ar; ++k) m[1].push_back(-k);
	q->fwd(add, del, 0);
	*padd = del;
	return 	delete q, progs.erase(progs.end()-1), true;*/
}

bool driver::pfp() {
	size_t sz = progs.size();
	DBG(printdb(wcout<<L"db:"<<endl, 0) << endl;)
	pfp(progs[0]);
	for (size_t n = 1; n != sz; ++n) {
		size_t db = progs[n-1]->db;
		if (progs[n-1]->bits != progs[n]->bits)
			progs[n]->db = bdd_rebit(db, progs[n-1]->bits,
				progs[n]->bits,progs[n-1]->bits*progs[n-1]->ar);
		DBG(printdb(wcout<<L"db:"<<endl, n) << endl;)
		progs[n]->db = bdd_pad(progs[n]->db, progs[n-1]->ar,
			progs[n]->ar, pad, progs[n]->bits);
		DBG(printdb(wcout<<L"db:"<<endl, n) << endl;)
		if (!pfp(progs[n])) return false;
	}
	// comment the following two lines in order to see builtins
	// in the program's output
	for (size_t x : builtin_symbdds[sz-1])
		progs[sz - 1]->db = bdd_and_not(progs[sz - 1]->db, x);
	printdb(wcout, sz - 1);
//	if (pr)
//		*pr = progs.back()->getbdd(
//			add, progs.back()->bits, progs.back()->proof_arity());
//	if (pr) printbdd(wcout<<"proof:"<<endl, add,
//		progs.back()->bits, progs.back()->proof_arity());
	return true;
}

wostream& driver::printbdd(wostream& os, const matrix& t) const {
	set<wstring> s;
	for (auto v : t) {
		wstringstream ss;
		for (auto k : v)
			if (k == pad) ss << L"* ";
			else if((size_t)k < nsyms())ss<<dict_get(k)<<L' ';
			else ss << L'[' << k << L"] ";
		s.emplace(ss.str());
	}
	for (auto& x : s) os << x << endl;
	return os;
}

#ifdef DEBUG
driver* drv;
//wostream& printbdd(wostream& os,size_t t) { return drv->printbdd(os,t); }
wostream& printbdd_one(wostream& os,size_t t) { return drv->printbdd_one(os,t);}
wostream& printbdd(wostream& os, size_t t, size_t bits, size_t ar) {
	return drv->printbdd(os, t, bits, ar);
}
wostream& printbdd_one(wostream& os, size_t t, size_t bits, size_t ar) {
	return drv->printbdd_one(os, t, bits, ar);
}
#endif

wostream& operator<<(wostream& os, const pair<cws, size_t>& p) {
	for (size_t n = 0; n != p.second; ++n) os << p.first[n];
	return os;
}

wostream& driver::printbdd(wostream& os, size_t t, size_t bits, size_t ar)const{
	return printbdd(os, progs.back()->getbdd(t, bits, ar));
}

wostream& driver::printbdd_one(wostream& os, size_t t, size_t bits,
	size_t ar) const {
	return printbdd(os, progs.back()->getbdd_one(t, bits, ar));
}

//wostream& driver::printbdd(wostream& os, size_t t) const {
//	return printbdd(os, progs.back()->getbdd(t));
//}
wostream& driver::printbdd_one(wostream& os, size_t t) const {
	os << "one of " << bdd_count(t, progs.back()->bits*progs.back()->ar)
		<< " results: ";
	return printbdd(os, progs.back()->getbdd_one(t));
}
wostream& driver::printdb(wostream& os, size_t prog) const {
	return printbdd(os, progs[prog]->getbdd(progs[prog]->db));
}
