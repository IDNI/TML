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
#include <cstdlib>

#include "driver.h"
#include "err.h"
#include "iterators.h"
#include "transform_opt_cqc.h"
#include "transform_opt_squaring.h"

using namespace std;

#ifdef WITH_EXACT_COST_FUNCTION
static size_t facts_4_predicate = 100;

flat_rule generate_random_fact(const int p, const size_t s) {
	// Prepare random number generator
	static bool seeded = false;
	if (!seeded) srand(time(0)), seeded = true;
	flat_rule r;
	term t; t.tab = p;
	for (size_t i = 0; i < s; ++i) t.emplace_back(abs(rand()) % facts_4_predicate);	
	r.emplace_back(t);
	return r;
}

flat_prog generate_random_facts(const int p, const size_t s) {
	flat_prog fp;
	for (size_t i = 0; i != facts_4_predicate; ++i) fp.insert(generate_random_fact(p,s)); 
	return fp;
}

flat_prog generate_facts(const flat_rule& fr) {
	// Collect predicates
	map<int_t, size_t> predicates;
	for (int i = 1; i != fr.size(); ++i ) predicates.insert({fr[i].tab, fr[i].size()});
	// Generate facts 
	flat_prog facts;
	for (auto& [p, s]: predicates) 
		for(auto& f: generate_random_facts(p, s)) facts.insert(f);
	return facts;
}

flat_prog update_with_new_symbols(tables& tbl, const flat_prog& fp) {
	static int_t idx = 1;
	flat_prog nfp;
	map<int_t, int_t> renaming;
	for (auto& r: fp) {
		flat_rule nfr;
		for (auto& t: r) {
			term nt = t;
			// If the table is not in the original program and it has not been
			// renamed yet...
			if ( !renaming.contains(t.tab)) {
				// ...add it to tables with a new index and cache the change
				// in the renaming map. 
				renaming[t.tab] = idx++;
				table ntbl; ntbl.len = t.size(); ntbl.generated = true;
				tbl.tbls.emplace_back(ntbl);
			}
			// Apply renaming if needed.
			nt.tab = renaming.contains(t.tab) ? renaming[t.tab] : t.tab;
			nfr.emplace_back(nt);
		}
		nfp.insert(nfr);
	}
	return nfp;
}

double cost(const vector<term>& fr) {
	if (fr.size() == 0) return 0;

	rt_options to; 
	to.bproof            = proof_mode::none;
	to.fp_step           = true;
	to.optimize          = true;

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
	flat_rule nfr = fr;
	flat_prog fp = generate_facts(nfr); fp.insert(nfr);
	// Run the program to obtain the results which we will then filter

	#ifdef DEBUG
	o::dbg() << "Sample prog for cost computation\n";
	for (auto& a: fp) {
		o::dbg() << "RULE: = [";
		for(auto &r: a) {
			o::dbg() << r.tab << "[";
			for (auto &t: r) o::dbg() << t << ",";
			o::dbg() << "],";
		} 
		o::dbg() << "]: " <<" \n";
	}
	#endif

	options o;
	driver drv(o);

	DBG(o::dbg() << "run_prog" << endl;);
	clock_t start{}, end;
	double t;
	measure_time_start();


	drv.error = false;

	update_with_new_symbols(tbls, fp);
	//tbls.fixed_point_term.tab = tbls.tbls.size();
	tbls.rules.clear(), tbls.datalog = true;
	if (!tbls.get_rules(fp)) return false;


	nlevel begstep = tbls.nstep;

	bool r = true;
	// run program only if there are any rules
	if (tbls.rules.size()) {
		tables_progress p( dict, ir);
		tbls.fronts.clear();
		r = tbls.pfp(1, 1, p);
	} else {
		bdd_handles l = tbls.get_front();
		tbls.fronts = {l, l};
	}

	end = clock(), t = double(end - start) / CLOCKS_PER_SEC;
	o::ms() << "# pfp: " << endl; measure_time_start();
	return t;
}

double cost(const flat_prog& fp) {
	double fp_cost = 0; for (const auto& r:fp) fp_cost += cost(r);
	return fp_cost;
}

#else

long cost(const flat_rule& fr) {
	// Count the number of uses of each variable
	map<int, size_t> count;
	ranges::for_each(fr.begin(), fr.end(), [&](auto& t){
		ranges::for_each(t.begin(), t.end(), [&](int i) {
			count[i] = count.contains(i) ? count[i] + 1: 1;
		});
	});
	// Remove exported variables
	ranges::for_each(fr[0].begin(), fr[0].end(), [&](int i) {
		if (i < 0) count.erase(i);
	});
	// Compute the actual cost
	long cost = 1;
	ranges::for_each(count.begin(), count.end(), [&](auto& i){
		cost = cost + (i.second + 1) * (i.second + 1);
	});
	cost = cost * fr.size();
	return cost;
}

long cost(const flat_prog& fp) {
	long fp_cost = 0; for (const auto& r:fp) fp_cost += cost(r);
	return fp_cost;
}
#endif // WITH_EXACT_COST_FUNCTION


/* Represents a change of a program. */

struct change {
	set<flat_rule> del;
	set<flat_rule> add;

	auto operator<=>(const change& that) const {
		// TODO add del && add are empty special case to avoid creating
		// fake initial mins... other posibility would be to use optionals, 
		// but the natural order defined for them does not help us.
		#ifdef WITH_EXACT_COST_FUNCTION
		double cost_this = 0, cost_that = 0;
		#else
		long cost_this = 0, cost_that = 0;
		#endif // WITH_EXACT_COST_FUNCTION
		for (auto& fr: del) cost_this -= cost(fr);
		for (auto& fr: add) cost_this += cost(fr);
		for (auto& fr: that.del) cost_that -= cost(fr);
		for (auto& fr: that.add) cost_that += cost(fr);
		return cost_this <=> cost_that;
	}

	bool operator()(flat_prog& fp) {
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

change extract_common(const flat_rule& r1, const flat_rule& r2, const flat_prog& fp) {
	vector<term> b1(++r1.begin(), r1.end());
	vector<term> b2(++r2.begin(), r2.end());
	change min { .add = {r1, r2}}; 
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

			#ifndef DEBUG
			o::dbg() << "c1 = [";
			for(auto &s: c1) {
				o::dbg() << s.tab << "[";
				for (auto &t: s) o::dbg() << t << ",";
				o::dbg() << "],";
			} 
			o::dbg() << "]: " << cost(c1) <<" \n";

			o::dbg() << "c2 = [";
			for(auto &s: c2) {
				o::dbg() << s.tab << "[";
				for (auto &t: s) o::dbg() << t << ",";
				o::dbg() << "],";
			} 
			o::dbg() << "]: " << cost(c2) <<" \n";

			o::dbg() << "r1 = [";
			for(auto &s: r1) {
				o::dbg() << s.tab << "[";
				for (auto &t: s) o::dbg() << t << ",";
				o::dbg() << "],";
			} 
			o::dbg() << "]: " << cost(r1) <<" \n";

			o::dbg() << "r2 = [";
			for(auto &s: r2) {
				o::dbg() << s.tab <<"[";
				for (auto &t: s) o::dbg() << t << ",";
				o::dbg() << "],";
			} 
			o::dbg() << "]: " << cost(r2) <<" \n";

			o::dbg() << "er1.remains = [";
			for(auto &r: er1.first) {
				o::dbg() << r.tab << "[";
				for (auto &t: r) o::dbg() << t << ",";
				o::dbg() << "],";
			} 
			o::dbg() << "]: " << cost(er1.first) <<" \n";
			o::dbg() << "er1.extracted = [";
			for(auto &r: er1.second) {
				o::dbg() << r.tab << "[";
				for (auto &t: r) o::dbg() << t << ",";
				o::dbg() << "],";
			} 
			o::dbg() << "]: " << cost(er1.second) <<" \n";

			o::dbg() << "er2.remains = [";
			for(auto &r: er2.first) {
				o::dbg() << r.tab <<  "[";
				for (auto &t: r) o::dbg() << t << ",";
				o::dbg() << "],";
			} 
			o::dbg() << "]: " << cost(er2.first) <<" \n";
			o::dbg() << "er2.extracted = [";
			for(auto &r: er2.second) {
				o::dbg() << r.tab << "[";
				for (auto &t: r) o::dbg() << t << ",";
				o::dbg() << "],";
			} 
			o::dbg() << "]: " << cost(er2.second) <<" \n";
			#endif
				
			if (rule_contains(er1.second, er2.second, fp)) {
				change proposed { 
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

				#ifndef DEBUG
				o::dbg() << "er2.extracted DOES IMPLY er1.extracted\n";
				o::dbg() << "Proposed changes\n";
				for (auto& a: c.add) {
					o::dbg() << "ADDITION: = [";
					for(auto &r: a) {
						o::dbg() << r.tab << "[";
						for (auto &t: r) o::dbg() << t << ",";
						o::dbg() << "],";
					} 
					o::dbg() << "]: " << cost(a) <<" \n";
				}

				for (auto& d: c.del) {
					o::dbg() << "DELETION: = [";
					for(auto &r: d) {
						o::dbg() << r.tab << "[";
						for (auto &t: r) o::dbg() << t << ",";
						o::dbg() << "],";
					} 
					o::dbg() << "]: " << cost(d) <<" \n";
				}
				#endif
			}
		}
	}
	return min;
}

inline bool head_neg(const flat_rule& r) {
	return r[0].neg;
}

change minimize_step_using_rule(const flat_rule& r, const flat_prog& fp, const flat_prog& p) { 
	change min { .add = {r}};
	for (auto fr: fp) {
		if (r != fr && head_neg(r) && head_neg(fr) && rule_contains(r, fr, fp)) {
			change proposed { .del = {fr}};
			min = min < proposed ? min : proposed;
		}			
		auto proposed = extract_common(r, fr, p);
		min = min < proposed ? min : proposed;
	} 
	return min;
}

bool minimize_step(flat_prog& fp) {
	set<flat_rule> pending(fp.begin(), fp.end());
	bool changed = false;
	while (!pending.empty()) {
		auto r = *pending.begin();
		auto change = minimize_step_using_rule(r, pending, fp);
		changed |= change(fp);
		pending.erase(r);
		for (auto& d: change.del) pending.erase(d);
	}
	return changed;
}

#ifndef WITH_EXACT_COST_FUNCTION
flat_prog update_with_new_symbols(tables& tbl, const flat_prog& fp) {
	static int_t idx = tbl.tbls.size();
	flat_prog nfp;
	map<int_t, int_t> renaming;
	for (auto& r: fp) {
		flat_rule nfr;
		for (auto& t: r) {
			term nt = t;
			// If the table is not in the original program and it has not been
			// renamed yet...
			if (t.tab >= tbl.tbls.size() && !renaming.contains(t.tab)) {
				// ...add it to tables with a new index and cache the change
				// in the renaming map. 
				renaming[t.tab] = idx++;
				table ntbl; ntbl.idbltin = idx; ntbl.len = t.size(); ntbl.generated = true;
				tbl.tbls.emplace_back(ntbl);
			}
			// Apply renaming if needed.
			nt.tab = renaming.contains(t.tab) ? renaming[t.tab] : t.tab;
			nfr.emplace_back(nt);
		}
		nfp.insert(nfr);
	}
	return nfp;
}
#endif WITH_EXACT_COST_FUNCTION

flat_prog driver::minimize(const flat_prog& fp) const {
	flat_prog mfp = fp;
	print(o::out() << "Initial uniterated flat_prog:\n", mfp) << endl;
	o::out() << "Flat program size: " << mfp.size() << endl;
	o::out() << "Flat program cost: " << cost(mfp) << endl;
	for (int i = 0; i != opts.get_int("minimize"); i++) {
		if (!minimize_step(mfp)) break;
		print(o::out() << "Minimized flat_prog after:" << i+1 << " iterations.\n", mfp) << endl;
		o::out() << "Flat program size:" << mfp.size() << endl;
		o::out() << "Flat program cost: " << cost(mfp) << endl;
	}
	return update_with_new_symbols(*tbl, mfp);
}

flat_prog driver::iterate(const flat_prog& fp) const {
	flat_prog ifp = fp;
	print(o::out() << "Initial uniterated flat_prog:\n", ifp) << endl;
	o::out() << "Flat program size: " << ifp.size() << endl;
	o::out() << "Flat program cost: " << cost(ifp) << endl;
	for (int i = 0; i != opts.get_int("iterate"); i++) {
		ifp = square_program(ifp);
		print(o::out() << "Iterated flat_prog after:" << i+1 << " iterations.\n", ifp) << endl;
		o::out() << "Flat program size: " << ifp.size() << endl;
		o::out() << "Flat program cost: " << cost(ifp) << endl;
	}
	return update_with_new_symbols(*tbl, ifp);
}