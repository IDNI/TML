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

#include "driver.h"
#include "err.h"
#include "iterators.h"
#include "transform_opt_cqc.h"
#include "transform_opt_squaring.h"

using namespace std;

long cost(flat_rule const& fr) {
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
		cost = cost + i.second;
	});
	cost = cost * cost * fr.size();
	return cost;
}

long cost(flat_prog const& fp) {
	long fp_cost = 0; for (const auto& r:fp) fp_cost += cost(r);
	return fp_cost;
}

/* Represents a change of a program. */

struct change {
	set<flat_rule> del;
	set<flat_rule> add;

	auto operator<=>(const change& that) const {
		// TODO add case del && add are empty special case to avoid creating
		// fake initial mins... other posibility would be to use optionals, 
		// but the order defined does not help us.
		long cost_this = 0, cost_that = 0;
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

term create_term(int s, set<int>& vs) {
	term nt; nt.tab = s;
	for(auto& i: vs) nt.push_back(i);
	return nt;
}

pair<flat_rule, flat_rule> extract_rule(flat_rule& r, int s, flat_rule& e) {
	// Compute the rest of the rule (without the terms in e)
	flat_rule remains;
	for (auto& t: r) if (ranges::find(e.begin(), e.end(), t) == e.end()) remains.emplace_back(t);
	// Compute the variables of the new rule
	auto remains_vars = get_vars(remains);
	set<int> extracted_vars;
	for (auto& v: get_vars(e)) if (remains_vars.contains(v)) extracted_vars.insert(v);
	// Create the rule extracted
	auto extracted_head = create_term(s, extracted_vars); 
	flat_rule extracted; 
	extracted.push_back(extracted_head);
	for (auto& t: e) extracted.push_back(t);
	// Compute remaining rule
	remains.push_back(extracted_head);
	return {remains, extracted};
}

change propose_change(flat_rule& r1, pair<flat_rule, flat_rule>& er1,
		flat_rule& r2, pair<flat_rule, flat_rule>& er2) {
	change c;
	c.del.insert(r1);
	c.del.insert(r2);
	c.add.insert(er1.first);
	c.add.insert(er2.first);
	c.add.insert(er1.second);
	return c;
}

bool include_renamings(change& c) {
    //for (auto& r: c.add) if (r.size() == 2) for (auto& p: r) if (p.tab >= 65536) return true;
	for (auto& r: c.add) if (r.size() == 2) if (r[0].tab >= 65536) return true;
	return false;
}

bool is_identity(change& c) {
	for (auto& r: c.add) if (!c.del.contains(r)) return false;
	return c.del.size() == c.add.size();
}

change extract_common(flat_rule& r1, flat_rule& r2, flat_prog& fp) {
	vector<term> b1(++r1.begin(), r1.end());
	vector<term> b2(++r2.begin(), r2.end());
	change min; 
	min.add.emplace(r1);
	min.add.emplace(r2);
	for (auto c1 : powerset_range(b1)) {
		if (c1.empty()) continue;
		int s = get_tmp_sym();
		auto er1 = extract_rule(r1, s, c1);
		for (auto c2 : powerset_range(b2)) {
			if (c2.empty()) continue;
			auto er2 = extract_rule(r2, s, c2);
			// If heads have different size, they shouldn't be extracted
			if (er1.second.size() != er2.second.size()) continue;
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
				auto c = propose_change(r1, er1, r2, er2);
				// Check we are not renaming
				if (include_renamings(c)) continue;
				// Check we are not adding the same rule again
				if (is_identity(c)) continue;
				// Is the proposal valid
				if (min > c) min = c;
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

change minimize_step_using_rule(flat_rule& r, flat_prog& fp, flat_prog& p) { 
	change min;
	min.add.emplace(r);
	for (auto fr: fp) {
		auto c = extract_common(r, fr, p);
		min = min < c ? min : c;
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

flat_prog update_with_new_symbols(tables& tbl, flat_prog& fp) {
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
		// return mfp;
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
		// return ifp;
}