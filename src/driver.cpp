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
#include "archive.h"

#ifdef __EMSCRIPTEN__
#include "../js/embindings.h"
#endif

using namespace std;

template <typename T>
std::basic_ostream<T>& operator<<(std::basic_ostream<T>& os, const pair<ccs, size_t>& p);

void driver::transform_len(raw_term& r, const strs_t& s) {
	for (size_t n = 1; n < r.e.size(); ++n)
		if (	r.e[n].type == elem::SYM && r.e[n].e == "len" &&
			n+3 < r.e.size() &&
			r.e[n+1].type == elem::OPENP &&
			r.e[n+2].type == elem::SYM &&
			r.e[n+3].type == elem::CLOSEP) {
			auto it = s.find(r.e[n+2].e);
			int_t len = it == s.end() ? 0 : it->second.size();
//			if (it == s.end()) parse_error(err_len, r.e[n+2].e);
			r.e.erase(r.e.begin()+n,r.e.begin()+n+4),
			r.e.insert(r.e.begin()+n, elem(len)),
			r.calc_arity(current_input);
		}
}

size_t driver::load_stdin() {
	ostringstream_t ss; ss << CIN.rdbuf();
	pd.std_input = to_string_t(ws2s(ss.str()));
	return pd.std_input.size();
}

void unquote(string_t& str);

string_t driver::directive_load(const directive& d) {
	string_t str(d.arg[0]+1, d.arg[1]-d.arg[0]-2);
	switch (d.type) {
		case directive::FNAME:
			return to_string_t(input::file_read(to_string(str)));
		case directive::STDIN: return move(pd.std_input);
		default: return unquote(str), str;
	}
	DBGFAIL;
}

void driver::directives_load(raw_prog& p, lexeme& trel) {
//	int_t rel;
	for (const directive& d : p.d)
		switch (d.type) {
		case directive::BWD: pd.bwd = true; break;
		case directive::TRACE: trel = d.rel.e; break;
		case directive::CMDLINE:
			if (d.n < opts.argc())
				pd.strs.emplace(d.rel.e,
					to_string_t(opts.argv(d.n)));
			else parse_error(err_num_cmdline);
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

bool driver::transform(raw_progs& rp, size_t n, const strs_t& /*strtrees*/) {
	if (!rp.p.size()) return true;
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
		if (pd.strs.size() > 1)
			return throw_runtime_error(err_one_input);
//		else transform_grammar(rp.p[n], pd.strs.begin()->first,
//			pd.strs.begin()->second.size());
//	}
//	if (opts.enabled("sdt"))
//		for (raw_prog& p : rp.p)
//			p = transform_sdt(move(p));
#ifdef TRANSFORM_BIN_DRIVER
	if (opts.enabled("bin"))
		for (raw_prog& p : rp.p)
			transform_bin(p);
#endif
//	if (trel[0]) transform_proofs(rp.p[n], trel);
	//o::out()<<rp.p[n]<<endl;
//	if (pd.bwd) rp.p.push_back(transform_bwd(rp.p[n]));
	return true;
}

void driver::output_pl(const raw_prog& p) const {
	if (opts.enabled("xsb"))     print_xsb(o::to("xsb"), p);
	if (opts.enabled("swipl"))   print_swipl(o::to("swipl"), p);
	if (opts.enabled("souffle")) print_souffle(o::to("souffle"), p);
}

bool driver::prog_run(raw_progs& rp, size_t n, size_t steps,
	size_t break_on_step)
{
//	pd.clear();
	//DBG(o::out() << "original program:"<<endl<<p;)
//	strtrees.clear(), get_dict_stats(rp.p[n]), add_rules(rp.p[n]);
	clock_t start, end;
	size_t step = nsteps();
	measure_time_start();
	bool fp = tbl->run_prog(rp.p[n], pd.strs, steps, break_on_step);
	if (tbl->error) error = true;
	o::ms() << "# elapsed: ";
	measure_time_end();
	pd.elapsed_steps = nsteps() - step;
//	for (auto x : prog->strtrees_out)
//		strtrees.emplace(x.first, get_trees(prog->pd.strtrees[x.first],
//					x.second, prog->rng.bits));
	return fp;
}

bool driver::add(input* in) {
	if (!rp.parse(in, tbl->get_dict(), in->newseq)) return error=true,false;
	if (!in->newseq) transform(rp, pd.n, pd.strs);
	return true;
}

template <typename T>
void driver::list(std::basic_ostream<T>& os, size_t n) {
	size_t e = n ? n-- : rp.p.size();
	if (e > rp.p.size()) { os<<"# no such program exist"<<endl; return; }
	for (; n != e; ++n) os<<"# Listing program "<<(n + 1)<<":\n{\n"
		<<rp.p[n]<<"}\n";
	os << flush;
}
template void driver::list(std::basic_ostream<char>&, size_t);
template void driver::list(std::basic_ostream<wchar_t>&, size_t);

void driver::new_sequence() {
	//DBG(o::dbg() << "new sequence" << endl;)
	transform(rp, pd.n, pd.strs);
	raw_prog &p = rp.p[pd.n];
	for (const string& s : str_bltins) p.builtins.insert(get_lexeme(s));
	output_pl(p);
}

void driver::restart() {
	pd.n = 0;
	pd.start_step = nsteps();
	running = true;
}

bool driver::run(size_t steps, size_t break_on_step, bool break_on_fp) {
	if (!rp.p.size()) return result = true;
	if (!running) restart();
next_sequence:
	if (nsteps() == pd.start_step) new_sequence();
	if (opts.disabled("run") && opts.disabled("repl"))
		return true;
	bool fp = prog_run(rp, pd.n, steps, break_on_step);
	if (fp) {
		//DBG(if (opts.enabled("dump")) out(o::dump());)
		if (pd.n == rp.p.size()-1) // all progs fp
			return result = true, true;
		++pd.n;
		pd.start_step = nsteps();
		if (steps && steps >= pd.elapsed_steps)
			if (!(steps -= pd.elapsed_steps)) return false;
		if ((break_on_step && nsteps() == break_on_step)
			|| break_on_fp) return false;
		goto next_sequence;
	}
	return false;
}

bool driver::step(size_t steps, size_t break_on_step, bool break_on_fp) {
	return run(steps, break_on_step, break_on_fp);
}

template <typename T>
void driver::info(std::basic_ostream<T>& os) {
	size_t l = rp.p.size();
	os<<"# prog n:    \t" << (pd.n+1) <<" of: " << (l>0?l:0) << endl;
	os<<"# step:      \t" << nsteps() <<" - " << pd.start_step <<" = "
		<< (nsteps() - pd.start_step) << " ("
		<< (running ? "" : "not ") << "running)" << endl;
	bdd::stats(os<<"# bdds:     \t")<<endl;
	//DBG(os<<"# opts:    \t" << opts << endl;)
}
template void driver::info(std::basic_ostream<char>&);
template void driver::info(std::basic_ostream<wchar_t>&);

size_t driver::size() {
	return archive::size(*this);
}

void driver::db_load(std::string filename) {
	load_archives.emplace_back(archive::type::BDD, filename, 0, false);
	load_archives.back() >> *this;
}

void driver::db_save(std::string filename) {
	archive ar(archive::type::BDD, filename, archive::size(*this), true);
	ar << *this;
}

void driver::load(std::string filename) {
	if (!ii->size()) {
		load_archives.emplace_back(archive::type::DRIVER, filename,0,0);
		if (!load_archives.back().error) load_archives.back() >> *this;
		return;
	}
	error = true;
	throw_runtime_error(
		"Loading into a running program is not yet supported."); // TODO
}

void driver::save(std::string filename) {
	archive ar(archive::type::DRIVER, filename, archive::size(*this), true);
	ar << *this;
}

void driver::read_inputs() {
	//COUT << "read_inputs() current_input: " << current_input << " next_input: " << (current_input ? current_input->next() : 0) << endl;
	while (current_input && current_input->next()) {
		current_input = current_input->next();
		if (!add(current_input)) return;
		++current_input_id;
		//COUT << "current_inputid: " << current_input_id << endl;
	}
}

driver::driver(string s, options o) : rp(), opts(o) {
	dict_t dict;

	// inject inputs from opts to driver and dict (needed for archiving)
	dict.set_inputs(ii = opts.get_inputs());

	if (s.size()) opts.parse(strings{ "-ie", s });

	// we don't need the dict any more, tables owns it from now on...
	tbl = new tables(move(dict), opts.enabled("proof"), 
		opts.enabled("optimize"), opts.enabled("bin"),
		opts.enabled("t"), opts.enabled("regex"));
	set_print_step(opts.enabled("ps"));
	set_print_updates(opts.enabled("pu"));
	set_populate_tml_update(opts.enabled("tml_update"));
	if (ii) {
		current_input = ii->first();
		if (current_input)
			if (!add(current_input)) return;
		read_inputs();
	}
}
driver::driver(FILE *f,    options o)   : driver(input::file_read_text(f), o) {}
driver::driver(string_t s, options o)   : driver(to_string(s), o) {}
driver::driver(const char *s,options o) : driver(string(s), o) {}
driver::driver(ccs   s,    options o)   : driver(string_t(s), o) {}
driver::driver(options o)               : driver(string(), o) {}
driver::driver(string s)                : driver(s, options()) {}
driver::driver(FILE *f)                 : driver(f, options()) {}
driver::driver(string_t s)              : driver(to_string(s)) {}
driver::driver(const char *s)           : driver(s, options()) {}
driver::driver(ccs   s)                 : driver(string_t(s)) {}

driver::~driver() {
	if (tbl) delete tbl;
	for (auto x : strs_allocated) free((char *)x);
}
