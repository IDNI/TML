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
using namespace std;

#define err_proof	"proof extraction yet unsupported for programs "\
			"with negation or deletion."
#define err_directive_elem \
	L"universe element in directive not appearing in program.\n"

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

void driver::count_term(const raw_term& t, set<lexeme, lexcmp>& rels,
	set<lexeme, lexcmp>& syms) {
	rels.insert(t.e[0].e);
	for (size_t n = 1; n < t.e.size(); ++n)
		if (t.e[n].type == elem::NUM)
			nums = max(nums, t.e[n].num+1);
		else if (t.e[n].type == elem::SYM)
			syms.insert(t.e[n].e);
		else if (t.e[n].type == elem::CHR)
			chars = max(chars, (int_t)256);
}

size_t driver::load_stdin() {
	wstringstream ss;
	std_input = ((ss << wcin.rdbuf()), ss.str());
	return std_input.size();
}

strs_t driver::get_dict_stats(const raw_prog& p, const map<lexeme, wstring>& s){
	set<lexeme, lexcmp> rels, syms;
	for (const directive& d : p.d) {
		chars = max(chars, (int_t)256),
		rels.insert(d.rel);
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
		for (const raw_term& t : r.heads()) count_term(t, rels, syms);
		for (const raw_term& t : r.bodies()) count_term(t, rels, syms);
	}
	for (const lexeme l : syms) dict.get_sym(l);
	for (const lexeme l : rels) dict.get_rel(l);
	for (auto y : s) rels.insert(y.first);
	if (!dict.nsyms() && !nums && !chars) {
		wcerr<<L"warning: empty domain, adding dummy element."<<endl;
		nums = 1;
	}
	strs_t r;
	for (auto y : s) r[dict.get_rel(y.first)] = move(y.second);
	return r;
}

wstring s2ws(const string& s) { return wstring(s.begin(), s.end()); } // FIXME

wstring driver::directive_load(const directive& d) {
	wstring str(d.arg[0]+1, d.arg[1]-d.arg[0]-2);
	if (d.type == directive::FNAME) return file_read(str);
	if (d.type == directive::STDIN) return move(std_input);
	if (d.type == directive::CMDLINE) {
		if (argc < d.n)
			parse_error( // FIXME
			L"program expects more command line arguments.\n", L"");
		return s2ws(argv[d.n]);
	}
	for (size_t i = 0; i != str.size(); ++i)
		if (str[i] == L'\\') str.erase(str.begin() + i);
	return str;
}

map<lexeme, wstring> driver::directives_load(const vector<directive>& ds) {
	map<lexeme, wstring> r;
	for (const directive& d : ds)
		if (d.type != directive::TREE)
			r.emplace(d.rel, directive_load(d));
	return r;
}

lp* driver::prog_init(const raw_prog& p, strs_t s, lp* last) {
	matpairs m;
	matrix g, pg;
	for (const raw_rule& x : p.r)
		if (x.goal && !x.pgoal) // FIXME
			assert(!x.nbodies()), g.push_back(get_term(x.head(0)));
		else if (x.pgoal)
			assert(!x.nbodies()), pg.push_back(get_term(x.head(0)));
		else m.insert(get_rule(x));
	map<int_t, term> trees;
	for (const directive& d : p.d)
		if (d.type == directive::TREE) {
//			size_t r = dict.get_rel(d.rel), s = syms.size();
//			yields[r] = get_term(d.t);
//			if (syms.size() != s)
//				parse_error(err_directive_elem, d.t.e[0].e);
		}
	size_t usz = (dict.nsyms() + nums + chars)<<2;
	return new lp(move(m), move(g), p.delrel, usz, s, last);
}

driver::driver(int argc, char** argv, FILE *f, bool print_transformed) 
	: driver(argc, argv, move(raw_progs(f)), print_transformed) {}
driver::driver(int argc, char** argv, wstring s, bool print_transformed) 
	: driver(argc, argv, move(raw_progs(s)), print_transformed) {}

driver::driver(int argc, char** argv, raw_progs rp, bool print_transformed)
	: argc(argc), argv(argv) {
	DBG(drv = this;)
	lp *prog = 0;
	set<lp*> progs;
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
	vector<pair<strs_t, size_t>> x;
	for (auto t : v) {
		strs_t s = get_dict_stats(t.first, t.second);
		clock_t start, end;
		start = clock();
		prog = prog_init(move(t.first), move(s), prog);
		end = clock();
		wcerr << double(end - start) / CLOCKS_PER_SEC << endl;
		start = clock();
		result &= prog->pfp({});
		end = clock();
		wcerr << double(end - start) / CLOCKS_PER_SEC << endl;
		progs.insert(prog);
	}
	if (prog) printdb(wcout, prog);
	for (lp* p : progs) delete p;
}
