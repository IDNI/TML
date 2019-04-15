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

void unquote(wstring& str) {
	for (size_t i = 0; i != str.size(); ++i)
		if (str[i] == L'\\') str.erase(str.begin() + i);
}

wstring _unquote(wstring str) { unquote(str); return str; }

#define mkchr(x) ((((int_t)x)<<2)|1)
#define mknum(x) ((((int_t)x)<<2)|2)

term driver::get_term(raw_term r, const strs_t& s) {
	for (size_t n = 1; n < r.e.size(); ++n)
		if (	r.e[n].type == elem::SYM && r.e[n].e == L"len" &&
			n+3 < r.e.size() &&
			r.e[n+1].type == elem::OPENP &&
			r.e[n+2].type == elem::SYM &&
			r.e[n+3].type == elem::CLOSEP) {
			auto it = s.find(dict.get_rel(r.e[n+2].e));
			int_t len = it == s.end() ? 0 : it->second.size();
//			if (it == s.end()) parse_error(err_len, r.e[n+2].e);
			r.e.erase(r.e.begin()+n,r.e.begin()+n+4),
			r.e.insert(r.e.begin()+n, elem(len)),
			r.calc_arity();
		}
	term t(r.neg, dict.get_rel(r.e[0].e), {}, r.arity);
	for (size_t n = 1; n < r.e.size(); ++n)
		if (r.e[n].type == elem::NUM)
			t.add_arg(mknum(r.e[n].num));
		else if (r.e[n].type == elem::CHR)
			t.add_arg(mkchr(r.e[n].ch));
		else if (r.e[n].type == elem::VAR)
			t.add_arg(dict.get_var(r.e[n].e));
		else if (r.e[n].type == elem::STR) {
			lexeme l = r.e[n].e;
			++l[0], --l[1];
			t.add_arg(dict.get_sym(dict.get_lexeme(
				_unquote(lexeme2str(l)))));
		}
		else if (r.e[n].type!=elem::OPENP && r.e[n].type!=elem::CLOSEP)
			t.add_arg(dict.get_sym(r.e[n].e));
	return t;
}

pair<matrix, matrix> driver::get_rule(const raw_rule& r, const strs_t& s) {
	matrix h, b;
	for (auto x : r.heads()) h.push_back(get_term(x, s));
	for (auto x : r.bodies()) b.push_back(get_term(x, s));
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

void driver::directives_load(raw_prog& p, prog_data& pd, lexeme& trel) {
	int_t rel;
	for (const directive& d : p.d)
		switch (d.type) {
		case directive::TRACE: trel = d.rel.e; break;
		case directive::STDOUT: pd.out.push_back(get_term(d.t,pd.strs));
					break;
		case directive::TREE:
			rel = dict.get_rel(d.t.e[0].e);
			if (has(pd.strtrees, rel) || has(pd.strs, rel))
				parse_error(err_str_defined, d.t.e[0].e);
			else pd.strtrees.emplace(rel, get_term(d.t,pd.strs));
			break;
		default: pd.strs.emplace(dict.get_rel(d.rel.e),
				directive_load(d));
		}
}

void driver::add_rules(raw_prog& p, prog_data& pd) {
	for (const raw_rule& x : p.r)
		switch (x.type) {
		case raw_rule::NONE: pd.r.insert(get_rule(x,pd.strs)); break;
		case raw_rule::GOAL: pd.goals.push_back(get_term(
					x.head(0),pd.strs)); break;
		case raw_rule::TREE: pd.tgoals.push_back(get_term(
					x.head(0),pd.strs)); break;
		default: assert(0);
		}
}

void driver::transform(raw_prog& p, prog_data& pd, const strs_t& strtrees) {
	lexeme trel = { 0, 0 };
	directives_load(p, pd, trel);
	for (auto x : pd.strs) transform_string(x.second, p, x.first);
	for (auto x : strtrees) transform_string(x.second, p, x.first);
	if (!p.g.empty()) {
		if (pd.strs.size() != 1) er(err_one_input);
		else transform_grammar(p, pd.strs.begin()->second.size());
	}
	if (trel[0]) transform_proofs(p, trel);
}

lp* driver::prog_run(raw_prog& p, lp* last, strs_t& strtrees) {
	//DBG(wcout << L"original program:"<<endl<<p;)
	prog_data pd;
	transform(p, pd, strtrees);
	if (print_transformed) wcout<<L'{'<<endl<<p<<L'}'<<endl;
	strtrees.clear(), get_dict_stats(p), add_rules(p, pd);
	lp *prog = new lp(move(pd), range(dict.nsyms(), nums, chars), last);
	clock_t start, end;
	measure_time(result &= prog->pfp());
	for (auto x : prog->strtrees_out)
		strtrees.emplace(x.first, get_trees(prog->pd.strtrees[x.first],
					x.second, prog->rng.bits));
	int_t tr = dict.get_rel(L"try");
	set<prefix> sp;
	for (auto x : prog->db) if (x.first.rel == tr) sp.insert(x.first);
	for (auto x : sp) prog->db.erase(x);
	return prog;
}

driver::driver(int argc, char** argv, raw_progs rp, bool print_transformed)
	: argc(argc), argv(argv), print_transformed(print_transformed) {
	DBG(drv = this;)
	lp *prog = 0;
	strs_t strtrees;
	for (raw_prog& p : rp.p) prog = prog_run(p, prog, strtrees);
	if (prog) { printdb(wcout, prog); delete prog; }
}

driver::driver(int argc, char** argv, FILE *f, bool print_transformed) 
	: driver(argc, argv, move(raw_progs(f)), print_transformed) {}
driver::driver(int argc, char** argv, wstring s, bool print_transformed) 
	: driver(argc, argv, move(raw_progs(s)), print_transformed) {}

