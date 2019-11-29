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

#ifdef __EMSCRIPTEN__
#include "../js/embindings.h"
#endif

using namespace std;

wostream& operator<<(wostream& os, const pair<cws, size_t>& p);

namespace o {
wostream& out() { static wostream& os = output::to(L"output"); return os; }
wostream& err() { static wostream& os = output::to(L"error");  return os; }
wostream& inf() { static wostream& os = output::to(L"info");   return os; }
wostream& dbg() { static wostream& os = output::to(L"debug");  return os; }
}

void driver::transform_len(raw_term& r, const strs_t& s) {
	for (size_t n = 1; n < r.e.size(); ++n)
		if (	r.e[n].type == elem::SYM && r.e[n].e == L"len" &&
			n+3 < r.e.size() &&
			r.e[n+1].type == elem::OPENP &&
			r.e[n+2].type == elem::SYM &&
			r.e[n+3].type == elem::CLOSEP) {
			auto it = s.find(r.e[n+2].e);
			int_t len = it == s.end() ? 0 : it->second.size();
//			if (it == s.end()) parse_error(err_len, r.e[n+2].e);
			r.e.erase(r.e.begin()+n,r.e.begin()+n+4),
			r.e.insert(r.e.begin()+n, elem(len)),
			r.calc_arity();
		}
}

size_t driver::load_stdin() {
	wstringstream ss;
	std_input = ((ss << wcin.rdbuf()), ss.str());
	return std_input.size();
}

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
		case directive::CMDLINE:
			if (d.n < opts.argc())
				pd.strs.emplace(d.rel.e, opts.argv(d.n));
			else parse_error(err_num_cmdline, L""); // FIXME
			break;
/*		case directive::STDOUT: pd.out.push_back(get_term(d.t,pd.strs));
					break;
		case directive::TREE:
			rel = dict.get_rel(d.t.e[0].e);
			if (has(pd.strtrees, rel) || has(pd.strs, rel))
				parse_error(err_str_defined, d.t.e[0].e);
			else pd.strtrees.emplace(rel, get_term(d.t,pd.strs));
			break;*/
		default: pd.strs.emplace(d.rel.e, directive_load(d));
		}
}

void driver::transform(raw_progs& rp, size_t n, const strs_t& /*strtrees*/) {
	lexeme trel = { 0, 0 };
	directives_load(rp.p[n], trel);
	auto get_vars = [this](const raw_term& t) {
		for (const elem& e : t.e)
			if (e.type == elem::VAR)
				vars.insert(e.e);
	};
	auto get_all_vars = [get_vars](const raw_prog& p) {
		for (const raw_rule& r : p.r) {
			for (const raw_term& t : r.h) get_vars(t);
			for (const vector<raw_term>& b : r.b)
				for (const raw_term& t : b)
					get_vars(t);
		}
	};
	for (const raw_prog& p : rp.p) get_all_vars(p);
//	for (auto x : pd.strs)
//		if (!has(transformed_strings, x.first))
//			transform_string(x.second, rp.p[n], x.first),
//			transformed_strings.insert(x.first);
//	for (auto x : strtrees)
//		if (!has(transformed_strings, x.first))
//			transform_string(x.second, rp.p[n], x.first),
//			transformed_strings.insert(x.first);
	if (!rp.p[n].g.empty()) //{
		if (pd.strs.size() > 1) er(err_one_input);
//		else transform_grammar(rp.p[n], pd.strs.begin()->first,
//			pd.strs.begin()->second.size());
//	}
//	if (opts.enabled(L"sdt"))
//		for (raw_prog& p : rp.p)
//			p = transform_sdt(move(p));
#ifdef TRANSFORM_BIN_DRIVER
	if (opts.enabled(L"bin"))
		for (raw_prog& p : rp.p)
			transform_bin(p);
#endif
//	if (trel[0]) transform_proofs(rp.p[n], trel);
	//o::out()<<rp.p[n]<<endl;
//	if (pd.bwd) rp.p.push_back(transform_bwd(rp.p[n]));
}

void driver::output_pl(const raw_prog& p) const {
	if (opts.enabled(L"xsb"))     print_xsb    (output::to(L"xsb"),     p);
	if (opts.enabled(L"swipl"))   print_swipl  (output::to(L"swipl"),   p);
	if (opts.enabled(L"souffle")) print_souffle(output::to(L"souffle"), p);
}

void driver::prog_run(raw_progs& rp, size_t n, strs_t& strtrees) {
//	pd.clear();
	//DBG(o::out() << L"original program:"<<endl<<p;)
	transform(rp, n, strtrees);
	output_pl(rp.p[n]);
	if (opts.enabled(L"t"))
		for (auto p : rp.p)
			output::to(L"transformed")<<L'{'<<endl<<p<<L'}'<<endl;
//	strtrees.clear(), get_dict_stats(rp.p[n]), add_rules(rp.p[n]);
	clock_t start, end;
	tbl = new tables(opts.enabled(L"proof"), true, opts.enabled(L"bin"),
		opts.enabled(L"t"));
	if (opts.disabled(L"run")) return;
	measure_time(tbl->run_prog(rp.p[n], pd.strs));
//	for (auto x : prog->strtrees_out)
//		strtrees.emplace(x.first, get_trees(prog->pd.strtrees[x.first],
//					x.second, prog->rng.bits));
}

void driver::init() {
	output::create(L"output",      L".out.tml");
	output::create(L"error",       L".error.log");
	output::create(L"info",        L".info.log");
	output::create(L"debug",       L".debug.log");
	output::create(L"transformed", L".trans.tml");
	output::create(L"xsb",         L".P");
	output::create(L"swipl",       L".pl");
	output::create(L"souffle",     L".souffle");
}

driver::driver(raw_progs rp, options o) : opts(o) {
	strs_t strtrees;
	try {
		for (size_t n = 0; n != rp.p.size(); ++n) {
			prog_run(rp, n, strtrees);
			DBG(if (opts.enabled(L"o"))
				tbl->out(o::out() << endl);)
		}
		NDBG(if (opts.enabled(L"o"))
			tbl->out(o::out() << endl);)
		if (opts.enabled(L"csv")) save_csv();
	} catch (unsat_exception& e) {
		o::out() << s2ws(string(e.what())) << endl;
		result = false;
	}
}

driver::driver(FILE *f,   options o) : driver(raw_progs(f), o) {}
driver::driver(wstring s, options o) : driver(raw_progs(s), o) {}
driver::driver(char *s,   options o) : driver(raw_progs(s2ws(string(s))), o) {}
driver::driver(options o)            : driver(raw_progs(o.input()), o) {}
driver::driver(FILE *f)              : driver(f, options()) {}
driver::driver(wstring s)            : driver(s, options()) {}
driver::driver(char *s)              : driver(s, options()) {}
driver::driver(raw_progs rp)         : driver(rp, options()) {}

driver::~driver() {
	if (tbl) delete tbl;
	for (auto x : strs_extra) free((wstr)x[0]);
}

