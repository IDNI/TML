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

#include <vector>
#include <string>
#include <cstring>
#include <sstream>
#include <forward_list>
#include <functional>
#include <cctype>
#include <ctime>
#include <memory>
#include <locale>
#include <codecvt>
#include <fstream>
#include <iterator>
#include <optional>
#include <ranges>
#include <functional>
#include <optional>
#include "driver.h"
#include "err.h"
#include "iterators.h"
#include "transform_opt_cqc.h"
#include "transform_opt_squaring.h"
#include "transform_opt.h"

using namespace std;

/* Branchers and changes. */

/* Optimization branch and bound definitions. */


/* Represents a changed program, i.e. the original program, the additions and 
 * substractions. */

struct changed_prog  {
	// starting node of the changed progs log
	explicit changed_prog(const flat_prog &rp): current(rp) {};
	// link to previous changed prog
	explicit changed_prog(const changed_prog *mp): current(mp->current) {};

	flat_prog current;
};

/* Represents a change of a given (changed) program. If selected, it is
 * applied to the given (changed) program. This is a cheap implementation of
 * the command pattern. */

struct change {
public:
	set<flat_rule> del;
	set<flat_rule> add;

	bool operator()(changed_prog &cp) const {
		cp.current.insert(add.begin(), add.end());
		cp.current.erase(del.begin(), del.end());
		return true;
	}
};

/* Computes the approximate cost of executing a given changed program. */

using cost_function = function<size_t(changed_prog&)>;
const cost_function exp_in_heads = [](const changed_prog &mp) {
	auto const& rs = mp.current;
	size_t c = 0.0;
	for (auto &it : rs) {
		// TODO properly define this cost function
		c += it.size();
	}
	return c;
};

/* Computes the approximate cost of executing a given changed program. */

using brancher = function<vector<change>(changed_prog&)>;

/* Represents and strategy to select the best change according to the passed
 * cost_function. */

class bounder {
public:
	virtual bool bound(changed_prog& p) = 0;
	virtual flat_prog solution() = 0;
};

/* Custom implementation of bounder interface that returns the best solution
 * found so far. */

class best_solution: public bounder {
public:
	best_solution(cost_function& f, changed_prog &rp): 
			func_(f), 
			cost_(numeric_limits<size_t>::max()), 
			best_(reference_wrapper<changed_prog>(rp)) {};

	bool bound(changed_prog &p) {
		if (size_t cost = func_(p); cost < cost_) {
			cost_ = cost;
			best_ = p;
			return true;
		}
		return false;
	};

	flat_prog solution() {
		return best_.get().current;
	};
private:
	cost_function func_;
	size_t cost_;
	reference_wrapper<changed_prog> best_;
};

/* Auxiliary function used during rule splitting. */

flat_rule with_canonical_vars(const flat_rule &r) {
	// TODO rename variables from -1 to -n.
	return r;
}

// TODO move this function to a more general scope
term make_temp_term(const ints &is) {
	static int_t tab = 1 << 16;
	term nt; for (auto &i: is) nt.emplace_back(i);
	nt.tab = tab++;
	return nt;
}

ints get_vars(const vector<term> &b) {
	set<int_t> vs;
	for (auto &t: b) for (auto &i: t)
		if (i < 0) vs.insert(i);
	return ints(vs.begin(), vs.end());
}

flat_rule create_rule_from(const vector<term> &b) {
	flat_rule r;
	ints vs = get_vars(b);
	term head = make_temp_term(vs);
	r.emplace_back(head);
	for (auto &t: b) r.emplace_back(t);
	return r;
}

flat_rule remove_from_rule(const flat_rule &fr, const vector<term> &b) {
	flat_rule r;
	r.emplace_back(fr[0]);
	for (auto &t: b) r.emplace_back(t);
	return r;
}

/* Split a rule according to a subset of terms of the body. */

pair<flat_rule, flat_rule> split_rule(const flat_rule &r, const vector<term> &b) {
	// Rule using the elements of b and...
	flat_rule r1 = create_rule_from(b);
	flat_rule r2 = remove_from_rule(r, b);
	return {with_canonical_vars(r1), with_canonical_vars(r2)};
}

/* Brancher computing all the possible splits of all the rules. */

vector<change> brancher_split_bodies(const changed_prog &cp) {
	vector<change> changes;
	// For every rule and every possible subset of rules body we produce a
	// change splitting the rule accordingly.
	for (auto &r: cp.current) {
		vector<term> body(++r.begin(), r.end());
		for (auto &b : powerset_range(body)) {
			// For each choice we compute the new rules
			auto split = split_rule(r, b);
			change c;
			c.del.insert(r);
			c.add.insert(split.first);
			c.add.insert(split.second);
			changes.emplace_back(c);
		}
	}
	return changes;
}

/* Brancher computing quick splits of all the rules. */

vector<change> brancher_quick_split_bodies(const changed_prog &cp) {
	vector<change> changes;
	// For every rule and every possible subset of rules body we produce a
	// change splitting the rule accordingly.
	for (auto &r: cp.current) {
		vector<term> body(++r.begin(), r.end());
		for (auto &b : powerset_range(body)) {
			// For each choice we compute the new rules
			auto split = split_rule(r, b);
			change c;
			c.del.insert(r);
			c.add.insert(split.first);
			c.add.insert(split.second);
			changes.emplace_back(c);
		}
	}
	return changes;
}

vector<change> brancher_minimize(changed_prog& cp) {
	vector<change> changes;
	o::dbg() << "Minimizing rules ..." << endl << endl;
	for(auto rr: cp.current) {
		minimize_rule(rr, cp.current);
	}
	o::dbg() << "Minimized:" << endl << endl;
	return changes; 
} 

/* Optimization methods. */

vector<change> get_optimizations(changed_prog& changed, vector<brancher>& branchers) {
	// We collect all possible changes to the current mutated program.
	vector<change>  optimizations;
	for(brancher brancher: branchers) {
		auto proposed = brancher(changed);
		optimizations.insert(optimizations.end(), proposed.begin(), proposed.end());
	}
	return optimizations;
}

void optimize(changed_prog& mutated, vector<brancher>& branchers) {
	// We collect all possible changes to the current mutated program.
	vector<change>  optimizations = get_optimizations(mutated, branchers);
	// For each subset of optimizations, compute the new mutated program,
	// bound the current change and try to optimize again if needed.
	for (auto it = optimizations.begin(); it != optimizations.end(); ++it) {
		it->operator()(mutated);
	}
}

void optimize_loop(changed_prog& mutated, bounder& bounder, vector<brancher>& branchers) {
	// We collect all possible changes to the current mutated program.
	vector<change>  optimizations = get_optimizations(mutated, branchers);
	// For each subset of optimizations, compute the new mutated program,
	// bound the current change and try to optimize again if needed.
	powerset_range<change> subsets(optimizations);
	for (auto it = ++subsets.begin(); it != subsets.end(); ++it) {
		changed_prog new_mutated(mutated);
		vector<change> v = *it;
		for (auto mt = v.begin(); mt != v.end(); ++mt) mt->operator()(new_mutated);
		if (bounder.bound(new_mutated)) {
			optimize_loop(new_mutated, bounder, branchers);
		}
	}
}

flat_prog optimize_o1(const flat_prog &fp) {
	// body splitting
}

flat_prog squaring_o1(const flat_prog &fp) {

}

flat_prog optimize_o2(const flat_prog& fp) {
	// cqc and minimization
}

flat_prog squaring_o2(const flat_prog &fp) {

}

flat_prog optimize_o3(const flat_prog& fp) {
	// optimal body splitting and cqc + minimization
}

flat_prog squaring_o3(const flat_prog &fp) {

}
