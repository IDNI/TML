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

term driver::get_term(const raw_term& r) {
	term t;
	t.push_back(r.neg ? -1 : 1);
	for (const elem& e : r.e)
		if (e.type == elem::NUM) t.push_back(e.num+256);
		else if (e.type == elem::CHR) t.push_back(*e.e[0]+1);
		else if (e.type == elem::OPENP) t.push_back(openp);
		else if (e.type == elem::CLOSEP) t.push_back(closep);
		else t.push_back(dict_get(e.e));
	return t;
}

matrix driver::get_rule(const raw_rule& r) {
	matrix m;
	for (auto x : r.b) m.push_back(get_term(x));
	if (m[0][0] > 0)
		for (size_t i = 1; i < m[0].size(); ++i)
			if (m[0][i] == null) er(err_null_in_head);
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
	for (const raw_rule& r : p.r)
		for (const raw_term& t : r.b)
			for (const elem& e : t.e)
				if (e.type == elem::NUM)
					nums = max(nums, e.num+256);
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

void driver::grammar_to_rules(const vector<production>& g, matrices& m,
	int_t rel) {
	for (const production& p : g) {
		if (p.p.size() < 2) er("empty production.\n");
		matrix t;
		int_t v = -1, x = dict_get(p.p[0].e);
		if (p.p.size() == 2 && p.p[1].type == elem::SYM &&
			null == dict_get(p.p[1].e)) {
			m.insert({{1, x, -1, -1}, {1, rel, -2, -1, -3}});
			m.insert({{1, x, -1, -1}, {1, rel, -2, -3, -1}});
			continue;
		}
		t.push_back({1, x, -1, -(int_t)p.p.size()});
		for (size_t n = 1; n < p.p.size(); ++n, --v)
			if (p.p[n].type == elem::SYM) {
				if (null==(x=dict_get(p.p[n].e))) er(err_null);
				t.push_back({1, x, v, v-1});
			}
			else if (p.p[n].type == elem::CHR) {
				if(!n)er("grammar lhs cannot be a terminal.\n");
				t.push_back({1, rel, *p.p[n].e[0]+1, v, v-1});
			} else er("unexpected grammar node.\n");
		m.emplace(move(t));
	}
//	wcout << m << endl;
}

void driver::prog_init(const raw_prog& p, const strs_t& s){
	matrices m;
	matrix g, pg;
	if (p.g.size() && s.size() > 1)
		er("only one string allowed given grammar.\n");
	grammar_to_rules(p.g, m, s.begin()->first);
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
			m.insert({{1,x.first,x.second[n]+1,n+257,n+258}});
		m.insert({{1,x.first,x.second[x.second.size()-1]+1,
			(int_t)x.second.size()+256,null}});
	}
	prog = new lp(move(m), move(g), move(pg), prog);
	if (!s.empty())
		for (size_t x : builtin_rels) // to suppress builtins on output
			builtin_symbdds.insert(prog->get_sym_bdd(x, 0));
}

driver::driver(const raw_progs& rp) {
	DBG(drv = this;)
	syms.push_back(0), lens.push_back(0);
	for (size_t n = 0; n != rp.p.size(); ++n)
		nums = max((size_t)nums, get_nums(rp.p[n])),
		openp = dict_get(L"("), closep = dict_get(L")"),
		null = dict_get(L"null"),
		prog_init(rp.p[n], directives_load(rp.p[n]));
//		wcout << "v:"<<endl<<v<<endl,
//		exit(0);
}

bool driver::pfp() {
	if (!prog->pfp()) return false;
	size_t db = prog->db;
	for (size_t x : builtin_symbdds) db = bdd_and_not(db, x);
	return printbdd(wcout, prog->getbdd(db)), true;
}

wostream& driver::printbdd(wostream& os, const matrices& t) const {
	for (auto m : t) printbdd(os, m) << endl;
	return os;
}

wostream& driver::printbdd(wostream& os, const matrix& t) const {
	set<wstring> s;
	for (auto v : t) {
		wstringstream ss;
		for (auto k : v)
			if (k == pad) ss << L"* ";
			else if((size_t)k < nsyms())ss<<dict_get(k)<<L' ';
			else ss << L'[' << k << L"] ";
//		os << ss.str() << ',';
		s.emplace(ss.str());
	}
//	os<<endl;
	for (auto& x : s) os << x << endl;
	return os;
}

#ifdef DEBUG
driver* drv;
wostream& printdb(wostream& os, const lp* p) { return drv->printdb(os, p); }
wostream& printbdd(wostream& os, const lp* p, size_t t){
	return drv->printbdd(os,p,t);
}
wostream& printbdd_one(wostream& os, const lp* p, size_t t) {
	return drv->printbdd_one(os, p, t);
}
wostream& printbdd(wostream& os, size_t t, size_t bits, size_t ar) {
	return drv->printbdd(os, from_bits(t,bits,ar));
}
#endif

wostream& operator<<(wostream& os, const pair<cws, size_t>& p) {
	for (size_t n = 0; n != p.second; ++n) os << p.first[n];
	return os;
}

wostream& driver::printbdd(wostream& os, const lp *p, size_t t) const {
	return printbdd(os, p->getbdd(t));
}

wostream& driver::printbdd_one(wostream& os, const lp *p, size_t t) const {
	os << "one of " << bdd_count(t, p->bits * p->ar) << " results: ";
	return printbdd(os, p->getbdd_one(t));
}
wostream& driver::printdb(wostream& os, const lp *p)const{
	return printbdd(os,p,p->db);
}
