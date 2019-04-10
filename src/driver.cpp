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
#include <ctime>
#include "driver.h"
#include "rule.h"
#include "err.h"
using namespace std;

wostream& operator<<(wostream& os, const pair<cws, size_t>& p);

bool lexcmp::operator()(const lexeme& x, const lexeme& y) const {
	return	x[1]-x[0] != y[1]-y[0] ? x[1]-x[0] < y[1]-y[0]
		: (wcsncmp(x[0], y[0], x[1]-x[0]) < 0);
}

bool operator==(const lexeme& l, const wstring& s) {
	if ((size_t)(l[1]-l[0]) != s.size()) return false;
	return !wcsncmp(l[0], s.c_str(), l[1]-l[0]);
}

#define mkchr(x) ((((int_t)x)<<2)|1)
#define mknum(x) ((((int_t)x)<<2)|2)

term driver::get_term(const raw_term& r) {
	term t(r.neg, dict.get_rel(r.e[0].e), {}, r.arity);
	for (size_t n = 1; n < r.e.size(); ++n)
		if (r.e[n].type == elem::NUM)
			t.add_arg(mknum(r.e[n].num));
		else if (r.e[n].type == elem::CHR)
			t.add_arg(mkchr(*r.e[n].e[0]));
		else if (r.e[n].type == elem::VAR)
			t.add_arg(dict.get_var(r.e[n].e));
		else if (r.e[n].type!=elem::OPENP && r.e[n].type!=elem::CLOSEP)
			t.add_arg(dict.get_sym(r.e[n].e));
	return t;
}

pair<matrix, matrix> driver::get_rule(const raw_rule& r) {
	matrix h, b;
	for (auto x : r.heads()) h.push_back(get_term(x));
	for (auto x : r.bodies()) b.push_back(get_term(x));
//	if (m[0][0] > 0)
//		for (size_t i = 1; i < m[0].size(); ++i)
//			if (m[0][i] == null) er(err_null_in_head);
	return { h, b };
}

void driver::count_term(const raw_term& t, set<lexeme, lexcmp>& syms) {
	for (size_t n = 1; n < t.e.size(); ++n)
		if (t.e[n].type == elem::NUM) nums = max(nums, t.e[n].num+1);
		else if (t.e[n].type == elem::SYM) syms.insert(t.e[n].e);
		else if (t.e[n].type == elem::CHR) chars=max(chars, (int_t)256);
}

size_t driver::load_stdin() {
	wstringstream ss;
	std_input = ((ss << wcin.rdbuf()), ss.str());
	return std_input.size();
}

void driver::get_dict_stats(const raw_prog& p) {
	set<lexeme, lexcmp> /*rels,*/syms;
	for (const directive& d : p.d) {
		chars = max(chars, (int_t)256);
		switch (d.type) {
		case directive::FNAME:
			nums = max(nums, (int_t)fsize(d.arg[0]+1,
			(size_t)(d.arg[1]-d.arg[0]-1))+1); break;
		case directive::STR: 
			nums = max(nums,(int_t)(d.arg[1]-d.arg[0])+1);
			break;
		case directive::CMDLINE:
			nums = max(nums,(int_t)(strlen(argv[d.n])+1));
			break;
		case directive::STDIN:
			nums = max(nums,(int_t)(load_stdin()+1));
		default: ;
		}
	}
	for (const raw_rule& r : p.r) {
		for (const raw_term& t : r.heads()) count_term(t, syms);
		for (const raw_term& t : r.bodies()) count_term(t, syms);
	}
	for (const lexeme l : syms) dict.get_sym(l);
//	for (const lexeme l : rels) dict.get_rel(l);
//	for (auto y : s) rels.insert(y.first);
	if (!(dict.nsyms()+nums+chars))nums=1,wcerr<<warning_empty_domain<<endl;
//	return r;
}

wstring s2ws(const string& s) { return wstring(s.begin(), s.end()); } // FIXME

void unquote(wstring& str) {
	for (size_t i = 0; i != str.size(); ++i)
		if (str[i] == L'\\') str.erase(str.begin() + i);
}

wstring driver::directive_load(const directive& d) {
	wstring str(d.arg[0]+1, d.arg[1]-d.arg[0]-2);
	switch (d.type) {
		case directive::FNAME: return file_read(str);
		case directive::STDIN: return move(std_input);
		case directive::CMDLINE:
			if (d.n < argc) return s2ws(argv[d.n]);
			parse_error(err_num_cmdline, L""); break; // FIXME
		default: return unquote(str), str;
	}
	throw 0; // unreachable
}

#define measure_time(x) start = clock(); x; end = clock(); \
	wcerr << double(end - start) / CLOCKS_PER_SEC << endl

lp* driver::prog_run(raw_prog& p, lp* last) {
	prog_data pd;
	bool trace = false;
	lexeme prel;
	for (const directive& d : p.d)
		if (d.type == directive::TRACE) trace = true, prel = d.rel.e;
		else if (d.type == directive::STDOUT)
			pd.out.push_back(get_term(d.t));
		else if (d.type == directive::TREE) {
			if (pd.strtree.find(dict.get_rel(d.t.e[0].e))
					!= pd.strtree.end())
				parse_error(err_str_defined, d.t.e[0].e);
			pd.strtree[dict.get_rel(d.t.e[0].e)] = get_term(d.t);
		} else pd.strs.emplace(dict.get_rel(d.rel.e),directive_load(d));
	//DBG(wcout << L"original program:"<<endl<<p;)
	for (auto x : pd.strs) transform_string(x.second, p, x.first);
	if (!p.g.empty() && pd.strs.size() > 1) er(err_one_input);
	else transform_grammar(p);
	if (trace) transform_proofs(p, prel);
	if (print_transformed) wcout<<L'{'<<endl<<p<<L'}'<<endl;
	get_dict_stats(p);
	clock_t start, end;
	for (const raw_rule& x : p.r)
		switch (x.type) {
		case raw_rule::NONE: pd.r.insert(get_rule(x)); break;
		case raw_rule::GOAL: pd.goals.push_back(get_term(x.head(0)));
				     break;
		case raw_rule::TREE: pd.tgoals.push_back(get_term(x.head(0)));
				     break;
		default: assert(0);
		}
	lp *prog = new lp(move(pd), range(dict.nsyms(), nums, chars), last);
	measure_time(result &= prog->pfp({}));
	return prog;
}

driver::driver(int argc, char** argv, raw_progs rp, bool print_transformed)
	: argc(argc), argv(argv), print_transformed(print_transformed) {
	DBG(drv = this;)
	lp *prog = 0;
	for (raw_prog& p : rp.p) prog = prog_run(p, prog);
	if (prog) { printdb(wcout, prog); delete prog; }
}

driver::driver(int argc, char** argv, FILE *f, bool print_transformed) 
	: driver(argc, argv, move(raw_progs(f)), print_transformed) {}
driver::driver(int argc, char** argv, wstring s, bool print_transformed) 
	: driver(argc, argv, move(raw_progs(s)), print_transformed) {}

