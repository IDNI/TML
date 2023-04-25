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

#include <algorithm>
#include <cctype>
#include <codecvt>
#include <cstring>
#include <ctime>
#include <forward_list>
#include <fstream>
#include <functional>
#include <iterator>
#include <locale>
#include <memory>
#include <optional>
#include <ranges>
#include <sstream>
#include <string>
#include <vector>
#include <set>
#include <ctime>
#include <random>

#include "driver.h"
#include "err.h"
#include "iterators.h"
#include "transform_opt_cqc.h"
#include "transform_opt_squaring.h"

using namespace std;


struct cost { 

	cost(size_t sample_size_ = 100): sample_size(sample_size_) {}; 

	size_t sample_size;
	map<flat_rule, double> memo_rule_cost;
	map<rel_arity, flat_prog> memo_random_facts;

	flat_rule generate_random_fact(const rel_arity& r) {
		// Prepare random number generator
		static random_device rd;
		static mt19937 gen(rd()); 
		static uniform_int_distribution<> dis(1 << 2 | 2, sample_size << 2 | 2); 
		flat_rule fr;
		term t; t.tab = r.first;
		for (size_t i = 0; i < r.second; ++i) t.emplace_back(dis(gen));	
		fr.emplace_back(t);
		return fr;
	}

	flat_prog generate_random_facts(const rel_arity& r) {
		if (memo_random_facts.contains(r)) {
			o::dbg() << "Cache hit (random facts)" << endl;
			return memo_random_facts[r];
		}
		flat_prog fp;
		for (size_t i = 0; i != sample_size; ++i) fp.insert(generate_random_fact(r)); 
		memo_random_facts[r] = fp;
		return fp;
	}

	flat_prog generate_facts(const flat_rule& fr) {
		set<rel_arity> rels;
		for (auto& r: fr) rels.insert(get_rel_info(r));
		flat_prog facts;
		for (auto& r: rels) 
			for(auto& f: generate_random_facts(r)) facts.insert(f);
		return facts;
	}

	flat_prog update_with_new_symbols(tables& tbl, const flat_prog& fp) {
		flat_prog nfp;
		map<int_t, int_t> renaming;
		for (auto& r: fp) {
			flat_rule nfr;
			for (auto& t: r) {
				term nt = t;
				// If the table is not in the original program and it has not been
				// renamed yet...
				if (!renaming.contains(t.tab)) {
					// ...add it to tables with a new index and cache the change
					// in the renaming map. 
					renaming[t.tab] = tbl.tbls.size();
					table ntbl; ntbl.len = t.size(); ntbl.generated = true;
					tbl.tbls.emplace_back(ntbl);
				}
				// Apply renaming.
				nt.tab = renaming[t.tab];
				nfr.emplace_back(nt);
			}
			nfp.insert(nfr);
		}
		return nfp;
	}

	flat_rule canonize(vector<term> fr) {
		int rel = 0, var = 0;
		map<int, int> rel_renaming;
		map<int, int> var_renaming;
		flat_rule nfr;
		for (auto& t: fr) {
			term nt = t;
			if (t.is_builtin()) { nfr.push_back(t); continue; }
			else if (!rel_renaming.contains(t.tab)) rel_renaming[t.tab] = ++rel, nt.tab = rel_renaming[t.tab];
			for (auto& a: t)
				if (var_renaming.contains(a)) nt.push_back(a);
				else {
					var_renaming[a] = ++var;
					nt.push_back(var_renaming[a]);
				}
			nfr.push_back(nt);
		}
		return nfr;
	}

	double operator()(const vector<term>& fr) {
		// Canonize the rule
		auto cfr = canonize(fr);
		// Check cache
		if (memo_rule_cost.contains(cfr))  {
			o::dbg() << "Cache hit (cost function)" << endl;
			return memo_rule_cost[cfr];
		}
		// The cost of the empty rule is 0.
		if (cfr.empty()) return 0;

		rt_options to; to.optimize = true, to.fp_step = false, to.bproof = proof_mode::none;

		dict_t dict;
		ir_builder ir(dict, to);
		builtins_factory* bf = new builtins_factory(dict, ir);
		auto bltins = bf
			->add_basic_builtins()
			.add_bdd_builtins()
			.add_print_builtins()
			.add_js_builtins().bltins;

		tables tbls(to, bltins); 
		// Build flat_program
		flat_rule nfr = cfr;
		flat_prog fp = generate_facts(nfr); fp.insert(nfr);
		// Run the program to obtain the results which we will then filter

		options o;
		driver drv(o);

		DBG(o::dbg() << "run_prog" << endl;);
		clock_t start{}, end;
		double t;
		measure_time_start();


		drv.error = false;

		#if defined(BIT_TRANSFORM) | defined(BIT_TRANSFORM_V2)
		tbls.bits = 1;
		#else
			#ifdef TYPE_RESOLUTION
			TODO Fix the bit computation for the type resolution case
			size_t a = max(max(ir_handler.nums, ir_handler.chars), ir_handler.syms);
			if (a == 0) tbls.bits++;
			else while (a > size_t (1 << tbls.bits)-1) tbls.bits++;
			#else
		auto bts = 0;
		for (auto& r: fp) for (auto& t: r) for (auto& a: t) bts = max(a, bts >> 2);
		while (bts >= (1 << (tbls.bits - 2))) { tbls.add_bit(); }
			#endif
		#endif // BIT_TRANSFORM | BIT_TRANSFORM_V2
		
		auto nfp = update_with_new_symbols(tbls, fp);
		tbls.fixed_point_term.tab = tbls.tbls.size() + 1;
		tbls.rules.clear(), tbls.datalog = true;
		if (!tbls.get_rules(nfp)) return false;

		// run program only if there are any rules
		if (tbls.rules.size()) {
			tables_progress p( dict, ir);
			tbls.fronts.clear();
			tbls.pfp(1, 1, p);
		} else {
			bdd_handles l = tbls.get_front();
			tbls.fronts = {l, l};
		}

		end = clock(), t = double(end - start) * 1000000 / CLOCKS_PER_SEC;
		o::ms() << "# pfp: " << t << endl; measure_time_start();
		// Cache rule cost
		memo_rule_cost[cfr] = t;
		return t;
	}

	double operator()(const flat_prog& fp) {
		double fp_cost = 0; for (const auto& r:fp) fp_cost += this->operator()(r);
		return fp_cost;
	}

};

/* Represents a change in program. */
struct change {
	function<double(flat_rule)> cost; 
	set<flat_rule> del;
	set<flat_rule> add;

	auto operator<=>(const change& that) const {
		double cost_this = 0, cost_that = 0;
		for (auto& fr: del) cost_this -= cost(fr);
		for (auto& fr: add) cost_this += cost(fr);
		for (auto& fr: that.del) cost_that -= cost(fr);
		for (auto& fr: that.add) cost_that += cost(fr);
		return cost_this <=> cost_that;
	}

	bool operator()(flat_prog& fp) const {
		if (del == add) return false;
		for (auto& fr: del) fp.erase(fr);
		fp.insert(add.begin(), add.end());
		return !add.empty() || !del.empty();
	}
};

/* Auxiliary functions */
static int_t tab = 1 << 16;

int get_tmp_sym() {
	return tab++;
}

set<int> get_vars(const term& t) {
	set<int> vars;
	for (auto& i: t) if (i < 0) vars.insert(i);
	return vars;
}

set<int> get_vars(const flat_rule fr) {
	set<int> vars; 
	for (auto& t: fr) for (auto& v: get_vars(t)) vars.insert(v);
	return vars;
}

set<int> get_vars(const flat_prog fp) {
	set<int> vars; 
	for (auto& fr: fp) for (auto& v: get_vars(fr)) vars.insert(v);
	return vars;
}

term create_term(int s, const set<int>& vs) {
	term nt; nt.tab = s;
	for(auto& i: vs) nt.push_back(i);
	return nt;
}

pair<flat_rule, flat_rule> extract_rule(const flat_rule& r, int s, const flat_rule& e) {
	// Compute the rest of the rule (without the terms in e)
	flat_rule remains;
	for (auto& t: r) if (ranges::find(e.begin(), e.end(), t) == e.end()) remains.emplace_back(t);
	// Compute the variables of the new rule
	auto remains_vars = get_vars(remains);
	set<int> extracted_vars;
	for (auto& v: get_vars(e)) if (remains_vars.contains(v)) extracted_vars.insert(v);
	// Create the rule extracted
	auto extracted_head = create_term(s, extracted_vars); 
	flat_rule extracted {extracted_head};
	for (auto& t: e) extracted.push_back(t);
	// Compute remaining rule
	remains.push_back(extracted_head);
	return {remains, extracted};
}

bool include_renamings(const change& c) {
	for (auto& r: c.add) if (r.size() == 2) if (r[0].tab >= 65536) return true;
	return false;
}

bool is_identity(const change& c) {
	return c.add == c.del;
}

change extract_common(const flat_rule& r1, const flat_rule& r2, const flat_prog& fp, cost& cf) {
	vector<term> b1(++r1.begin(), r1.end());
	vector<term> b2(++r2.begin(), r2.end());
	change min { .cost = cf, .del = {}, .add = {r1, r2}}; 
	for (auto c1 : powerset_range(b1)) {
		if (c1.empty()) continue;
		int s = get_tmp_sym();
		auto er1 = extract_rule(r1, s, c1);
		for (auto c2 : powerset_range(b2)) {
			if (c2.empty()) continue;
			auto er2 = extract_rule(r2, s, c2);
			// If heads have different size, they shouldn't be extracted
			if (er1.second[0].size() != er2.second[0].size()) continue;
			// For each pair or extracted rules we check if r1.second is 
			// contained in r2.second, i.e. if r1.second => r2.second
			if (rule_contains(er1.second, er2.second, fp)) {
				change proposed { 
					.cost = cf, 
					.del = {r1, r2}, 
					.add = {er1.first, er2.first, er1.second}};
				// auto c = propose_change(r1, er1, r2, er2);
				// Check we are not renaming
				if (include_renamings(proposed)) continue;
				// Check we are not adding the same rule again
				if (is_identity(proposed)) continue;
				// Is the proposal valid
				if (min > proposed) min = proposed;
				else continue;	
			}
		}
	}
	return min;
}

inline bool head_neg(const flat_rule& r) {
	return r[0].neg;
}

change minimize_step_using_rule(const flat_rule& r, const flat_prog& fp, const flat_prog& p, cost& cf) { 
	change min { .cost = cf, .del = {}, .add = {r}};
	for (auto fr: fp) {
		if (r != fr && head_neg(r) && head_neg(fr) && rule_contains(r, fr, fp)) {
			change proposed { .cost= cf, .del = {fr}, .add = {}};
			min = min < proposed ? min : proposed;
		}			
		auto proposed = extract_common(r, fr, p, cf);
		min = min < proposed ? min : proposed;
	} 
	return min;
}

bool minimize_step(flat_prog& fp, cost& cf) {
	set<flat_rule> pending(fp.begin(), fp.end());
	bool changed = false;
	while (!pending.empty()) {
		auto r = *pending.begin();
		auto change = minimize_step_using_rule(r, pending, fp, cf);
		changed |= change(fp);
		pending.erase(r);
		for (auto& d: change.del) pending.erase(d);
	}
	return changed;
}

flat_prog update_with_new_symbols(tables& tbl, const flat_prog& fp) {
	flat_prog nfp;
	map<int_t, int_t> renaming;
	for (auto& r: fp) {
		flat_rule nfr;
		for (auto& t: r) {
			term nt = t;
			// If the table is not in the original program and it has not been
			// renamed yet...
			if (!renaming.contains(t.tab) && (t.tab >= (1<<16))) {
				// ...add it to tables with a new index and cache the change
				// in the renaming map. 
				renaming[t.tab] = tbl.tbls.size();
				table ntbl; ntbl.len = t.size(); ntbl.generated = true;
				tbl.tbls.emplace_back(ntbl);
				nt.tab = renaming[t.tab];
			}
			// Apply renaming.
			nfr.emplace_back(nt);
		}
		nfp.insert(nfr);
	}
	return nfp;
}

using step_printer = function<void(const flat_prog&, int)>;

flat_prog minimize(const flat_prog& fp, int minimizations, cost& cf, step_printer& printer) {
	flat_prog mfp = fp;
	for (int i = 0; i != minimizations; i++)
		if (!minimize_step(mfp, cf)) break;
		else printer(mfp, i);
	return mfp;
}

flat_prog iterate(const flat_prog& fp, int iterations, step_printer& printer) {
	flat_prog ifp = fp;
	for (int i = 0; i != iterations; i++) {
		ifp = square_program(ifp);
		printer(ifp, i);
	}
	return ifp;
}

flat_prog minimize_and_iterate(const flat_prog& fp, int iterations, cost& cf, step_printer& printer) {
	flat_prog ifp = fp;
	for (int i = 0; i != iterations; i++) {
		ifp = iterate(ifp, 1, printer);
		ifp = minimize(ifp, 1, cf, printer);
		printer(ifp, i);
	}
	return ifp;
}

flat_prog driver::optimize(const flat_prog& fp) const {
	cost cf;
	#ifdef DEBUG
	step_printer printer = [&](const flat_prog& fp, int it) {
		print(o::dbg() << "Current flat_prog after:" << it << " steps.\n", fp) << endl;
		o::dbg() << "Flat program size: " << fp.size() << endl;
		o::dbg() << "Flat program cost: " << cf(fp) << endl; 
	};
	#else // DEBUG
	step_printer printer = [&](const flat_prog&, int) {	};
	#endif // DEBUG
	flat_prog tfp = fp;
	if (auto iterations = opts.get_int("iterate")) tfp = iterate(fp, iterations, printer);
	if (auto minimizations = opts.get_int("minimize")) tfp = minimize(tfp, minimizations, cf, printer);
	if (auto minimizations = opts.get_int("minimize-and-iterate")) tfp = minimize_and_iterate(tfp, minimizations, cf, printer);
	if (opts.get_int("iterate") || opts.get_int("minimize") || opts.get_int("minimize-and-iterate")) print(o::dump(), tfp);
	return update_with_new_symbols(*tbl, tfp);
}