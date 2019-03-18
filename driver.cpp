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

#define err_null_in_head \
	"'null' not allowed to appear in the head of positive rules.\n"

int_t null;
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
	if (m[0][0] > 0)
		for (size_t i = 1; i < m[0].size(); ++i)
			if (m[0][i] == null) er(err_null_in_head);
	for (auto x : r.b) m.push_back(get_term(x));
	return m;
}

string ws2s(const wstring& s) { return string(s.begin(), s.end()); }

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
	int_t nums = 0;
	for (size_t k = 0; k != p.d.size(); ++k)
		nums = max(nums, !p.d[k].fname
			? (int_t)(256+p.d[k].arg[1]-p.d[k].arg[0])
			: (int_t)(256+(int_t)fsize(ws2s(wstring(p.d[k].arg[0]+1
				,p.d[k].arg[1]-p.d[k].arg[0]-1)).c_str())));
	for (const raw_rule& r : p.r) {
		for (const elem& e : r.h.e)
			if (e.type == elem::NUM)
				nums = max(nums, e.num);
		for (const raw_term& t : r.b)
			for (const elem& e : t.e)
				if (e.type == elem::NUM)
					nums = max(nums, e.num);
	}
	return nums;
}

driver::strs_t driver::directives_load(const raw_prog& p) {
	strs_t r;
	for (size_t k = 0; k != p.d.size(); ++k) {
		wstring str(p.d[k].arg[0]+1, p.d[k].arg[1]-p.d[k].arg[0]-1);
		if (!p.d[k].fname) for (size_t i = 0; i != str.size(); ++i)
			if (str[i] == L'\\') str.erase(str.begin()+i);
		r.emplace(dict_get(p.d[k].rel), p.d[k].fname ?
			file_read_text(str) : str);
	}
	return r;
}

void driver::prog_init(const raw_prog& p, const matrices& rtxt,const strs_t& s){
	matrices m, pg;
	matrix g;
	m.insert(rtxt.begin(), rtxt.end());
	for (const raw_rule& x : p.r)
		if (x.goal && !x.pgoal) {
			assert(x.b.empty());
			g.push_back(get_term(x.h));
		} else (x.pgoal ? pg : m).insert(get_rule(x));
	for (auto x : s)
		for (int_t n = 0; n != (int_t)x.second.size(); ++n)
			m.insert({{1,x.first,x.second[n]+1,n+257,n+258}});
	prog = new lp(move(m), move(g), move(pg), prog);
	if (!s.empty())
		for (size_t x : builtin_rels) // to suppress builtins on output
			builtin_symbdds.insert(prog->get_sym_bdd(x, 0));
}

driver::driver(const raw_progs& rp) {
	DBG(drv = this;)
	bool txt;
	size_t ntxt = 0;
	matrices rtxt;
	syms.push_back(0), lens.push_back(0);
	null = dict_get(L"null");
	for (size_t n = 0; n != rp.p.size(); ++n)
		if ((txt = (nums=max((size_t)nums, get_nums(rp.p[n])))))
			ntxt = min(ntxt, n);
	if (txt) rtxt = get_char_builtins();
	for (size_t n = 0; n != rp.p.size(); ++n)
		prog_init(rp.p[n], n >= ntxt ? rtxt : matrices(),
			directives_load(rp.p[n]));
}

bool driver::pfp() {
	if (!prog->pfp()) return false;
	size_t db = prog->db;
	for (size_t x : builtin_symbdds) db = bdd_and_not(db, x);
	return printbdd(wcout, prog->getbdd(db)), true;
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
wostream& printdb(wostream& os, lp* p) { return drv->printdb(os, p); }
wostream& printbdd(wostream& os, lp* p, size_t t){return drv->printbdd(os,p,t);}
wostream& printbdd_one(wostream& os, lp* p, size_t t) {
	return drv->printbdd_one(os, p, t);
}
#endif

wostream& operator<<(wostream& os, const pair<cws, size_t>& p) {
	for (size_t n = 0; n != p.second; ++n) os << p.first[n];
	return os;
}

wostream& driver::printbdd(wostream& os, lp *p, size_t t) const {
	return printbdd(os, p->getbdd(t));
}

wostream& driver::printbdd_one(wostream& os, lp *p, size_t t) const {
	os << "one of " << bdd_count(t, p->bits * p->ar) << " results: ";
	return printbdd(os, p->getbdd_one(t));
}
wostream& driver::printdb(wostream& os, lp*p)const{return printbdd(os,p,p->db);}
