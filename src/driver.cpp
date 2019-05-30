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
#include <locale>
#include <codecvt>
#include <fstream>
#include "driver.h"
#include "err.h"
#include "ast.h"
using namespace std;

wostream& operator<<(wostream& os, const pair<cws, size_t>& p);

#define mkchr(x) ((((int_t)x)<<2)|1)
#define mknum(x) ((((int_t)x)<<2)|2)

void driver::transform_len(raw_term& r, const strs_t& s) {
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
}

/*term driver::get_term(raw_term r, const strs_t& s) {
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
	for (auto x : r.h.size()) h.push_back(get_term(x, s));
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
}*/

size_t driver::load_stdin() {
	wstringstream ss;
	std_input = ((ss << wcin.rdbuf()), ss.str());
	return std_input.size();
}

/*void driver::get_dict_stats(const raw_prog& p) {
	set<lexeme, lexcmp> syms;
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
}*/

wstring s2ws(const std::string& s) {
	return std::wstring_convert<std::codecvt_utf8<wchar_t>>().from_bytes(s);
}

string ws2s(const wstring& s) {
	return std::wstring_convert<std::codecvt_utf8<wchar_t>>().to_bytes(s);
}

void unquote(wstring& str);

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

void driver::directives_load(raw_prog& p, lexeme& trel) {
//	int_t rel;
	for (const directive& d : p.d)
		switch (d.type) {
		case directive::BWD: pd.bwd = true; break;
		case directive::TRACE: trel = d.rel.e; break;
/*		case directive::STDOUT: pd.out.push_back(get_term(d.t,pd.strs));
					break;
		case directive::TREE:
			rel = dict.get_rel(d.t.e[0].e);
			if (has(pd.strtrees, rel) || has(pd.strs, rel))
				parse_error(err_str_defined, d.t.e[0].e);
			else pd.strtrees.emplace(rel, get_term(d.t,pd.strs));
			break;*/
		default: pd.strs.emplace(dict.get_rel(d.rel.e),
				directive_load(d));
		}
}

/*void driver::add_rules(raw_prog& p) {
	for (const raw_rule& x : p.r)
		switch (x.type) {
		case raw_rule::NONE: pd.r.insert(get_rule(x,pd.strs)); break;
		case raw_rule::GOAL: pd.goals.push_back(get_term(
						x.head(0),pd.strs)); break;
		case raw_rule::TREE: pd.tgoals.push_back(get_term(
					x.head(0),pd.strs)); break;
		default: assert(0);
		}
}*/

void driver::transform(raw_progs& rp, size_t n, const strs_t& strtrees) {
	lexeme trel = { 0, 0 };
	directives_load(rp.p[n], trel);
	for (auto x : pd.strs)
		if (!has(transformed_strings, x.first))
			transform_string(x.second, rp.p[n], x.first),
			transformed_strings.insert(x.first);
	for (auto x : strtrees)
		if (!has(transformed_strings, x.first))
			transform_string(x.second, rp.p[n], x.first),
			transformed_strings.insert(x.first);
	if (!rp.p[n].g.empty()) {
		if (pd.strs.size() != 1) er(err_one_input);
		else transform_grammar(rp.p[n],
			dict.get_rel(pd.strs.begin()->first),
			pd.strs.begin()->second.size());
	}
	if (opts.enabled(L"ms"))
		for (raw_prog& p : rp.p)
			p = transform_ms(p);
//	if (trel[0]) transform_proofs(rp.p[n], trel);
	//wcout<<rp.p[n]<<endl;
//	if (pd.bwd) rp.p.push_back(transform_bwd(rp.p[n]));
}

void driver::output_pl(const raw_prog& p) const {
	if (opts.enabled(L"xsb"))     print_xsb    (output::to(L"xsb"),     p);
	if (opts.enabled(L"swipl"))   print_swipl  (output::to(L"swipl"),   p);
	if (opts.enabled(L"souffle")) print_souffle(output::to(L"souffle"), p);
}

void driver::output_ast() const {
	if (opts.enabled(L"ast"))      print_ast     (output::to(L"ast"));
	if (opts.enabled(L"ast-json")) print_ast_json(output::to(L"ast-json"));
	if (opts.enabled(L"ast-xml"))  print_ast_xml (output::to(L"ast-xml"));
	if (opts.enabled(L"ast-html")) print_ast_html(output::to(L"ast-html"));
	ast::clear();
}

void driver::prog_run(raw_progs& rp, size_t n, strs_t& strtrees) {
//	pd.clear();
	//DBG(wcout << L"original program:"<<endl<<p;)
	transform(rp, n, strtrees);
	output_pl(rp.p[n]);
	if (opts.enabled(L"t"))
		for (auto p : rp.p)
			output::to(L"transformed")<<L'{'<<endl<<p<<L'}'<<endl;
//	strtrees.clear(), get_dict_stats(rp.p[n]), add_rules(rp.p[n]);
	if (opts.disabled(L"run")) return;
	clock_t start, end;
	measure_time(tbl.run_prog(rp.p[n]));
//	for (auto x : prog->strtrees_out)
//		strtrees.emplace(x.first, get_trees(prog->pd.strtrees[x.first],
//					x.second, prog->rng.bits));
//	int_t tr = dict.get_rel(L"try");
}

void driver::init() {
	output::create(L"output",      L".out.tml");
	output::create(L"transformed", L".trans.tml");
	output::create(L"xsb",         L".P");
	output::create(L"swipl",       L".pl");
	output::create(L"souffle",     L".souffle");
	output::create(L"ast",         L".ast.tml");
	output::create(L"ast-json",    L".ast.json");
	output::create(L"ast-xml",     L".ast.xml");
	output::create(L"ast-html",    L".ast.html");
}

driver::driver(int argc, char** argv, raw_progs rp, options o) : argc(argc),
	argv(argv), opts(o) {
	opts.parse(argc, argv);
	DBG(wcout<<L"parsed args: "<<opts<<endl;)
	strs_t strtrees;
	output_ast();
	for (size_t n = 0; n != rp.p.size(); ++n) {
		prog_run(rp, n, strtrees);
		DBG(if(opts.enabled(L"o"))tbl.out(output::to(L"output")<<endl);)
	}
	NDBG(if (opts.enabled(L"o")) tbl.out(output::to(L"output")<<endl);)
	if (opts.enabled(L"csv")) wcout<<L"opts.enabled(csv) = true"<<endl, save_csv();
}

driver::driver(int argc, char** argv, FILE *f, options o) :
	driver(argc, argv, raw_progs(f), o) {}
driver::driver(int argc, char** argv, wstring s, options o) :
	driver(argc, argv, raw_progs(s), o) {}
driver::driver(int argc, char** argv, char *s, options o) :
	driver(argc, argv, raw_progs(s2ws(string(s))), o) {}
driver::driver(int argc, char** argv, FILE *f) :
	driver(argc, argv, f, options()) {}
driver::driver(int argc, char** argv, wstring s) :
	driver(argc, argv, s, options()) {}
driver::driver(int argc, char** argv, char *s) :
	driver(argc, argv, s, options()) {}
driver::driver(int argc, char** argv, raw_progs rp) :
	driver(argc, argv, rp, options()) {}
