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
#include "transform_opt.h"

using namespace std;

const cost_function exp_in_heads = [](const changed_prog &mp) {
	auto const& rs = mp.current;
	size_t c = 0.0;
	for (auto &it : rs) {
		// TODO properly define this cost function
		c += it.size();
	}
	return c;
};

void changed_prog::operator()(const change &m) {
	// Apply the change to the current changed_prog
	m(*this);
}

bool best_solution::bound(changed_prog &p) {
	if (size_t cost = func_(p); cost < cost_) {
		cost_ = cost;
		best_ = std::make_shared<changed_prog>(p);
		return true;
	}
	return false;
}

flat_prog best_solution::solution() {
	return best_.get()->current;
}

using flat_rule = vector<term>;
using rel_arity = tuple<int_t, size_t>;
using rule_index = map<rel_arity, set<flat_rule>>;
using unification = map<int_t, int_t>;
using selection = vector<flat_rule>;

struct squaring_context {
	reference_wrapper<dict_t> dict;
	reference_wrapper<rule_index> index;
};

/* Get relation info from the head term in a way suitable for be used as key. */

inline rel_arity get_rel_info(const term &t) {
	return make_tuple(t[0], t.size());
}

/* Get relation info from a flat rule in a way suitable to be used as a key. */

inline rel_arity get_rel_info(const flat_rule &t) {
	return get_rel_info(t[0]);
}

/* Returns true if the vector of terms correspond to a fact, false otherwise. */

inline bool is_fact(const flat_rule &r) {
	// Only one term and is not a goal
	return r.size() == 1 && !r[0].goal;
}

/* Returns true if the vector of terms correspond to a goal, false otherwise. */

inline bool is_goal(const flat_rule &r) {
	// TODO consider remove defensive programming
	// Non empty and its a goal
	return !r.empty() && r[0].goal;
}

/* Constructs a map with head/body information. In our case, the body is the 
 * first element of the vector of terms and the body the remaining terms. */

rule_index index_rules(const flat_prog &fp) {
	rule_index c;
	for (auto const &t: fp) {
		if (is_goal(t) || is_fact(t)) continue;
		if (c.contains(get_rel_info(t))) c[get_rel_info(t)].insert(t);
		else c[get_rel_info(t)] = set<flat_rule> {t};
	}
	return c;
}

/* Check if it the given substitution is compatible. */

inline bool is_compatible(int_t s, int_t u) {
	return (u >= 0 && (s <= 0 || u == s)) || (u < 0 && s < 0);
}

/* Apply a given unification to a given tail of a relation. */

bool apply_unification(unification &u, flat_rule &fr) {
	for (auto &t: fr) 
		for(size_t i = 1; i < t.size(); ++i) 
			if (u.contains(t[i])) 
				t[i] = u.at(t[i]);
	return true;
}

/* Compute the unification of two terms. To do this we take into account that
 * we are only considering the case where both term have the same symbol,  
 * the same arity and there are no recursive structures (they are flat). 
 * The procedure is as follows:
 * - a=a or X=X continue,
 * - a=X or X=a add X->a (apply X->a to the rest of the arguments)
 * - X=Y add X->Y
 * See [Martelli, A.; Montanari, U. (Apr 1982). "An Efficient Unification 
 * Algorithm". ACM Trans. Program. Lang. Syst. 4 (2): 258–282] for details. */

optional<unification> unify(const term &t1, const term &t2) {
	unification u;
	for (size_t i= 1; i < t1.size(); ++i) {
		if (t1[i] > 0 /* is cte */ && t2[i] > 0 /* is cte */) {
			if (t1[i] != t2[i]) return optional<unification>();
		} else if (t1[i] < 0 /* is var */ && t2[i] > 0 /* is constant */) { 
			if (u.contains(t1[i])) {
				if (u[t1[i]] == t2[i]) continue;
				else return optional<unification>();
			}
			u[t1[i]] = t2[i]; continue; 
		} else if (t1[i] > 0 /* is constant */ && t2[i] < 0 /* is var */) { 
			if (u.contains(t1[i])) {
				if (u[t1[i]] == t2[i]) continue;
				else return optional<unification>();
			}
			u[t2[i]] = t1[i]; continue; 
		} else {
			if (u.contains(t1[i])) {
				if (u[t1[i]] == t2[i]) continue;
				else return optional<unification>();
			}
			u[t1[i] /* is var */ ]  = t2[i] /* is var */;
		}
	}
	return optional<unification>(u);
}

/* Copmpute the last var used in the given rule. */

int_t get_last_var(const flat_rule &r) {
	int_t lst = 0;
	for (auto &t: r) for (auto i: t) lst = (i < lst) ? i : lst;
	return lst;
}

/* Renames all variables of a rule. */

flat_rule rename_rule_vars(const flat_rule &fr, int_t& lv) {
	flat_rule nfr(fr);
	map<int_t, int_t> sbs;
	for (auto &t: nfr) for (size_t i = 0; i != t.size(); ++i)
		if (!sbs.contains(t[i]) && t[i] < 0) sbs[t[i]] = --lv, t[i] = sbs[t[i]];
	return nfr;
}

/* Returns the squaring of a rule given a selection for the possible substitutions. */

void square_rule(flat_rule &fr, selection &sels, flat_prog &fp) {
	// TODO check fr is a datalog program
	flat_rule sfr; 
	// Add the head of the existing rule
	sfr.emplace_back(fr[0]);
	auto lv = get_last_var(fr);
	bool unified = true;
	for (size_t i = 0; i < sels.size(); ++i) {
		auto rfr = rename_rule_vars(sels[i], lv);
		if (auto u = unify(fr[i + 1], rfr[0])) {
			#ifndef DELETE_ME
			std::cout << "UNIFICATIOIN: {";
			for (auto &[f, s]: *u) {
				std::cout << "{" << f << ':' << s << "}, ";
				std::cout << "}" << std::endl;
			}
			#endif // DELETE_ME
			unified = unified && apply_unification(*u, sfr);
			unified = unified && apply_unification(*u, rfr);
			if (!unified) break;
			sfr.insert(sfr.end(), ++rfr.begin(), rfr.end()); 
		} else { unified = false; break; }
	}
	if (!unified) fp.insert(fr);
	else fp.insert(sfr);
}

/* Returns the squaring of a rule  */

void square_rule(flat_rule &fr, selection &sels, const rule_index &idx, 
		flat_prog &fp, size_t pos = 0) {
	if (!idx.contains(get_rel_info(fr[pos + 1]))) {
		fp.insert(fr);
		return;
	}
	// If we have selected all possible alternatives proceed with
	// the squaring of the rule
	if (pos == sels.size()) {
		square_rule(fr, sels, fp);
		return;
	}
	// otherwise, try all the possible selections
	for (auto &o: idx.at(get_rel_info(fr[pos + 1]))) {
		sels[pos] = o; 
		square_rule(fr, sels, idx, fp, pos + 1);
	}
}

/* Returns the squaring of a rule. As square_program automatically 
 * deals with facts and goals, we could assume that the body is not empty. */

void square_rule(flat_rule &fr, flat_prog &fp, const rule_index &idx) {
	// Cache vector with the selected rules to be used in squaring
	selection sels(fr.size() - 1 );
	square_rule(fr, sels, idx, fp);
}

/*! Produces a program where executing a single step is equivalent to
 * executing two steps of the original program. This is achieved through
 * inlining where each body term is replaced by the disjunction of the
 * bodies of the relation that it refers to. For those facts not
 * computed in the previous step, it is enough to check that they were
 * derived to steps ago and were not deleted in the previous step. */

flat_prog square_program(const flat_prog &fp) {
	// New flat_prog holding the squaring of fp
	flat_prog sqr;
	// Cache info for speed up the squaring holding a map between heads
	// and associated bodies
	auto idx = index_rules(fp);
	for (auto fr: fp) {
		if(is_fact(fr) || is_goal(fr)) 
			sqr.insert(fr);
		else square_rule(fr, sqr, idx);
	}
	return sqr;
}

#ifndef WORK_IN_PROGRESS

/* Query conatainment and minimization */

/* Provides consistent conversions of TML objects into Z3. */

class z3_context {
	size_t arith_bit_len;
	size_t universe_bit_len;
	z3::context context;
	z3::solver solver;
	z3::expr_vector head_rename;
	z3::sort bool_sort;
	z3::sort value_sort;
	std::map<rel_arity, z3::func_decl> rel_to_decl;
	std::map<int_t, z3::expr> var_to_decl;
	std::map<flat_rule, z3::expr> rule_to_decl;

	/* Initialize an empty context that can then bn e populated with TML to Z3
	 * conversions. value_sort is either a bit-vector whose width can
	 * contain the enire program universe and will be used for all Z3
	 * relation arguments and bool_sort is the "return" type of all
	 * relations. */

	z3_context(size_t arith_bit_len, size_t universe_bit_len) :
			arith_bit_len(arith_bit_len), universe_bit_len(universe_bit_len),
			solver(context), head_rename(context), bool_sort(context.bool_sort()),
			value_sort(context.bv_sort(universe_bit_len ? universe_bit_len : 1)) {
		// Initialize Z3 solver instance parameters
		z3::params p(context);
		p.set(":timeout", 500u);
		// Enable model based quantifier instantiation since we use quantifiers
		p.set("mbqi", true);
		solver.set(p);
	}

	string get_tmp_pred() const {
		static int_t pred;
		return "?0p" + to_string_(++pred);
	}

	string get_tmp_const() const {
		static int_t cons;
		return "?0c" + to_string_(++cons);
	}

	/* Function to lookup and create where necessary a Z3 representation of
	* a relation. */

	z3::func_decl rel_to_z3(const term &t) {
		const auto &rel_sig = get_rel_info(t);
		if(auto decl = rel_to_decl.find(rel_sig); decl != rel_to_decl.end())
			return decl->second;
		else {
			z3::sort_vector domain(context);
			for (size_t i = t.size() - 1; i != 0; --i)
				domain.push_back(value_sort);
			z3::func_decl ndecl =
				context.function(get_tmp_pred().c_str(), domain, bool_sort);
			rel_to_decl.try_emplace(rel_sig, ndecl);
			return ndecl;
		}
	}

	/* Function to create Z3 representation of global head variable names.
	 * The nth head variable is always assigned the same Z3 constant in
	 * order to ensure that different rules are comparable. */

	z3::expr globalHead_to_z3(const int_t pos) {
		for (int_t i=head_rename.size(); i<=pos; ++i)
			head_rename.push_back(z3::expr(context, fresh_constant()));
		return head_rename[pos];
	}

	/* Make a fresh Z3 constant. */

	inline z3::expr fresh_constant() {
		return z3::expr(context, Z3_mk_fresh_const(context, nullptr, value_sort));
	}

	/* Function to lookup and create where necessary a Z3 representation of
	 * elements. */

	z3::expr arg_to_z3(const int_t arg) {
		if(auto decl = var_to_decl.find(arg); decl != var_to_decl.end())
			return decl->second;
		else if(arg >= 0) {
			const z3::expr &ndecl = context.bv_val(arg, value_sort.bv_size());
			var_to_decl.try_emplace(arg, ndecl);
			return ndecl;
		} else {
			auto cons = get_tmp_const();
			const z3::expr &ndecl = context.constant(cons.c_str(), value_sort);
			var_to_decl.try_emplace(arg, ndecl);
			return ndecl;
		}
	}

	/* Construct a formula that constrains the head variables. The
	 * constraints are of two sorts: the first equate pairwise identical
	 * head variables to each other, and the second equate literals to their
	 * unique Z3 equivalent. Also exports a mapping of each head element to
	 * the Z3 head variable it has been assigned to. */

	z3::expr z3_head_constraints(const term &head, map<int_t, z3::expr> &body_rename) {
		z3::expr restr = context.bool_val(true);
		for (size_t i = 0; i < head.size(); ++i) {
			auto h = head[i];
			const z3::expr &var = globalHead_to_z3(i);
			if (const auto &[it, found] = body_rename.try_emplace(h, var); !found)
				restr = restr && it->second == var;
			else if (head[i] >= 0)
				restr = restr && var == arg_to_z3(h);
		}
		return restr;
	}

	/* Given a term, output the equivalent Z3 expression using and updating
	 * the mappings in the context as necessary. */

	z3::expr term_to_z3(const term &t) {
		if(t.extype == term::REL) {
			z3::expr_vector vars_of_rel (context);
			for (auto arg = t.begin() + 1; arg != t.end(); ++arg) {
				// Pushing head variables
				vars_of_rel.push_back(arg_to_z3(*arg));
			}
			return rel_to_z3(t)(vars_of_rel);
		} else assert(false); // Should never reach here
	}

	/* Given a rule, output the body of this rule converted to the
	 * corresponding Z3 expression. Caches the conversion in the context in
	 * case the same rule is needed in future. */

	z3::expr rule_to_z3(const flat_rule &r) {
		if(auto decl = rule_to_decl.find(r); decl != rule_to_decl.end())
			return decl->second;
		// Create map from bound_vars
		map<int_t, z3::expr> body_rename;
		z3::expr restr = z3_head_constraints(r[0], body_rename);
		// Collect bound variables of rule and restrictions from constants in head
		set<int_t> free_vars;
		vector<int_t> bound_vars(r[0].size());
		// Free variables are existentially quantified
		z3::expr_vector ex_quant_vars (context);
		for (const auto& var : free_vars)
			ex_quant_vars.push_back(arg_to_z3(var));
		map<int_t, z3::expr> var_backup;
		// For the intent of constructing this Z3 expression, replace head
		// variable expressions with the corresponding global head
		for(auto &[arg, constant] : body_rename) {
			var_backup.try_emplace(arg, arg_to_z3(arg));
			var_to_decl.try_emplace(arg, constant);
		}
		// Construct z3 expression from rule
		z3::expr formula = context.bool_val(true);
		// Now undo the global head mapping for future constructions
		for(auto &[el, constant] : var_backup) var_to_decl.at(el) = constant;
		z3::expr decl = restr && (ex_quant_vars.empty() ? formula : z3::exists(ex_quant_vars, formula));
		rule_to_decl.try_emplace(r, decl);
		return decl;
	}

	/* Checks if the rule has a single head and a body that is either a tree
	 * or a non-empty DNF. Second order quantifications and builtin terms
	 * are not supported. */

	bool is_query (const flat_rule &r) const {
		// Ensure that there are no multiple heads
		if(r.size() != 1) return false;
		// Ensure that head is positive
		if(r[0].neg) return false;
		return true;
	}

	bool disjoint(const flat_rule &r1, const flat_rule &r2) const {
		auto get_heads = [](term t) { return t[0]; };
		auto r1_terms = r1 | views::transform(get_heads);
		auto r2_terms = r2 | views::transform(get_heads);
		vector<int_t> i;
		set_intersection(r1_terms.begin(), r1_terms.end(),
			r2_terms.begin(), r2_terms.end(), back_inserter(i));
		return !i.empty();
	}

	bool comparable(const flat_rule &r1, const flat_rule &r2) const {
		return (r1[0][0] == r2[0][0] && r1[0].size() == r2[0].size());
	}

	/* Cretaes a new rule from head and body. */

	flat_rule get_rule_from(term &h, vector<term> &b) {
		flat_rule nr;
		nr.emplace_back(h);
		for (auto &t: b) nr.emplace_back(t);
		return nr;
	}
	
#endif // WORK_IN_PROGRESS
public:

#ifndef WORK_IN_PROGRESS

	/*! Checks if r2 is contained in r1. */

	bool check_qc(const flat_rule &r1, const flat_rule &r2) {
		// Have we compute already the result?
		static map<pair<flat_rule, flat_rule>, bool> memo;
		auto key = make_pair(r1, r2);
		if (memo.contains(key)) {
			return memo[key];
		}

		// If the heads in the body are disjoint, no qc is possible
		if (disjoint(r1, r2) || !comparable(r1, r2)) {
			memo[key] = false;
			swap(get<0>(key), get<1>(key));
			memo[key] = false;
		}

		// Do the expensive work
		o::dbg() << "Z3 QC Testing if " << r1 << " <= " << r2 << " : ";
		// Get head variables for z3
		z3::expr_vector bound_vars(context);
		for (size_t i = 0; i != r1[0].size(); ++i)
			bound_vars.push_back(globalHead_to_z3(i));
		// Rename head variables on the fly such that they match
		// on both rules
		z3::expr rule1 = rule_to_z3(r1);
		z3::expr rule2 = rule_to_z3(r2);
		solver.push();
		// Add r1 => r2 to solver
		if (bound_vars.empty()) solver.add(!z3::implies(rule1, rule2));
		else solver.add(!z3::forall(bound_vars,z3::implies(rule1, rule2)));
		bool res = solver.check() == z3::unsat;
		solver.pop();
		o::dbg() << res << endl;
		memo[key] = res;
		return res;
	}

	/*! Minimize the given rule using CQC. */

	// TODO Check that this is a Chruch-Rossen like algorithm.
	flat_rule minimize(flat_rule &r) {
		// Have we compute already the result
		static map<flat_rule, flat_rule> memo;
		if (memo.contains(r)) {
			return memo[r];
		}
		// Check basic cases.
		if(is_fact(r) || is_goal(r)) return r;
		// TODO Write a quick test to avoid easy cases.
		// We set the reference rule to r.
		auto rr = r;
		// We consider the body and the head off r and...
		vector<term> body(++r.begin(), r.end());
		term head = r[0];
		// ...generate all possible subsets.
		for (powerset_range bodies(body); auto b : bodies) {
			// For each choice we check for containment...
			auto nr = get_rule_from(head, b);
			// ...update the reference rule if needed and
			// memoize intermediate results.
			if (check_qc(nr, rr)) memo[rr] = nr, rr = nr; 
		}
		// We memoize and return the current reference (minimal) rule.
		memo[r] = rr;
		return rr;
	}
#endif // WORK_IN_PROGRESS


#ifndef WORK_IN_PROGRESS



#endif // WORK_IN_PROGRESS
};

#ifdef CHANGE_ME

/* Returns all the possible splittings of the rule. */

set<pair<flat_rule, flat_rule>> split_rule(flat_rule &fp) {
	set<pair<flat_rule, flat_rule>> splt;
	// do splitting
	return splt;
}


/*!
 * Optimize a mutated program
 */
vector<std::shared_ptr<change>> get_optimizations(changed_prog& mutated, vector<brancher>& branchers) {
	// we collect all possible changes to the current mutated program
	vector<std::shared_ptr<change>>  optimizations;
	for(brancher brancher: branchers) {
		auto proposed = brancher(mutated);
		optimizations.insert(optimizations.end(), proposed.begin(), proposed.end());
	}
	return optimizations;
}

/*! Entry point for optimization process. */

void optimize(flat_prog fp) {
	changed_prog cp(fp);
	best_solution bs(exp_in_heads, fp); 

	if(int_t iter_num = opts.get_int("O3")) {
	// Trimmed existentials are a precondition to program optimizations
	o::dbg() << "Removing Redundant Quantifiers ..." << endl << endl;

	// remove call to pdatalog_transform
	pdatalog_transform(rp, [&](raw_prog &rp) {
		o::dbg() << "P-DATALOG Pre-Transformation:" << endl << endl << rp << endl;
		split_heads(rp);
		// Alternately square and simplify the program iter_num times
		for(int_t i = 0; i < iter_num; i++) {
			o::dbg() << "Squaring Program ..." << endl << endl;
			square_program(rp);
			o::dbg() << "Squared Program: " << endl << endl << rp << endl;
		}
		o::dbg() << "P-DATALOG Post-Transformation:" << endl << endl << rp << endl;
	});

	if(opts.enabled("O1") || opts.enabled("O2")) {
		flat_prog fp;
		changed_prog mp(fp);
		plan begin(bs);
		flat_prog optimized(fp);
		if (!opts.get_int("O3")) {
			// Trimmed existentials are a precondition to program optimizations
			o::dbg() << "Adding export outer quantifiers brancher ..." << endl << endl;
			begin.branchers.push_back(bind(&driver::brancher_export_outer_quantifiers, this, placeholders::_1));
		}
		optimized = optimize_once(rp, begin);
		step_transform(optimized, [&](raw_prog &rp) {
			plan o1(bs);
			// This transformation is a prerequisite to the CQC and binary
			// transformations, hence its more general activation condition.
			o::dbg() << "Adding dnf brancher in begin..." << endl << endl;
			o1.branchers.push_back(bind(&driver::brancher_to_dnf, this, placeholders::_1));
			if (!opts.get_int("O3")) {
				o::dbg() << "Adding split heads brancher in begin..." << endl << endl;
				o1.branchers.push_back(bind(&driver::brancher_split_heads, this, placeholders::_1));
			}
			// Though this is a binary transformation, rules will become
			// ternary after timing guards are added
			optimized = optimize_once(rp, o1);
			if(opts.enabled("O2")) {
				plan o2_loop(bs), o2_once(bs);
				o::dbg() << "Adding Minimizer brancher ..." << endl << endl;
				o2_once.branchers.push_back(bind(&driver::brancher_minimize, this, placeholders::_1));
				optimized = optimize_loop(optimized, o2_once);
				o::dbg() << "Adding Z3 brancher ..." << endl << endl;
				o2_loop.branchers.push_back(bind(&driver::brancher_subsume_queries, this, placeholders::_1));
				o::dbg() << "Adding rulse factor brancher ..." << endl << endl;
				o2_loop.branchers.push_back(bind(&driver::brancher_factor_rules, this, placeholders::_1));
				optimized = optimize_loop(optimized, o2_loop);
			}
			plan end(bs);
			o::dbg() << "Adding split bodies brancher in loop..." << endl << endl;
			end.branchers.push_back(bind(&driver::brancher_split_bodies, this, placeholders::_1));
			o::dbg() << "Step Transformed Program:" << endl << rp << endl;
			end.branchers.push_back(bind(&driver::brancher_eliminate_dead_variables, this, placeholders::_1));
			rp = optimize_once(optimized, end);
			o::dbg() << "Current:" << endl << rp << endl;
		});
	}
}

void optimize(changed_prog& mutated, vector<brancher>& branchers) {
	// we collect all possible changes to the current mutated program
	vector<std::shared_ptr<change>>  optimizations = get_optimizations(mutated, branchers);
	// for each subset of optimizations, compute the new mutated program,
	// bound the current change and try to optimize again if needed
	for (auto it = optimizations.begin(); it != optimizations.end(); ++it) {
		(*it).get()->operator()(mutated);
	}
}

void optimize_loop(changed_prog& mutated, bounder& bounder, vector<brancher>& branchers) {
	// we collect all possible changes to the current mutated program
	vector<std::shared_ptr<change>>  optimizations = get_optimizations(mutated, branchers);
	// for each subset of optimizations, compute the new mutated program,
	// bound the current change and try to optimize again if needed
	powerset_range<std::shared_ptr<change>> subsets(optimizations);
	for (auto it = ++subsets.begin(); it != subsets.end(); ++it) {
		changed_prog new_mutated(mutated);
		vector<std::shared_ptr<change>> v = *it;
		for (auto mt = v.begin(); mt != v.end(); ++mt) (*mt).get()->operator()(new_mutated);
		if (bounder.bound(new_mutated)) {
			optimize_loop(new_mutated, bounder, branchers);
		}
	}
}

/*!
 * Optimize a raw program
 */
flat_prog optimize_once(flat_prog &program, plan &plan) {
	// the first mutated program just contain the original program as additions.
	changed_prog mutated {program};
	o::dbg() << "Applying optimizations ..." << endl << endl;
	optimize(mutated, plan.branchers); 
	plan.bndr.get().bound(mutated);
	return plan.bndr.get().solution();
}

flat_prog optimize_loop(flat_prog &program, plan &plan) {
	// loop over the branchers.
	changed_prog mutated {program};
	o::dbg() << "Looping over optimizations ..." << endl << endl;
	optimize_loop(mutated, plan.bndr, plan.branchers);
	return plan.bndr.get().solution();
}

#endif // CHANGE_ME

class change_del_rule : public virtual change  {
public:
	explicit change_del_rule(flat_prog &d): change(d) { }
	explicit change_del_rule(vector<term> &r): change(r) { }

	bool operator()(changed_prog &cp) const override {
		for (auto& r: clashing)	cp.current.erase(r);
		return true;
	}
};

class change_add_rule : public virtual change  {
public:
	vector<term> add;

	explicit change_add_rule(vector<term> &a): add(a) { }
	explicit change_add_rule(vector<term> &a, flat_prog d): change(d), add(a) { }
	explicit change_add_rule(vector<term> &a, vector<term> d): change(d), add(a)  { }

	bool operator()(changed_prog &cp) const override {
		cp.current.insert(add);
		return true;
	}
};

#ifdef CHANGE_ME
/* Recurse through the given formula tree in pre-order calling the given
 * function with the accumulator. */

template<typename X, typename F>
X prefold_tree2(raw_form_tree &t, X acc, const F &f) {
	const X &new_acc = f(t, acc);
	switch(t.type) {
		case elem::ALT: case elem::AND: case elem::IMPLIES: case elem::COIMPLIES:
				case elem::EXISTS: case elem::FORALL: case elem::UNIQUE:
			// Fold through binary trees by threading accumulator through both
			// the LHS and RHS
			return prefold_tree2(*t.r, prefold_tree2(*t.l, new_acc, f), f);
		// Fold though unary trees by threading accumulator through this
		// node then single child
		case elem::NOT: return prefold_tree2(*t.l, new_acc, f);
		// Otherwise for leaf nodes like terms and variables, thread
		// accumulator through just this node
		default: return new_acc;
	}
}

/* Update the number and characters counters as well as the distinct
 * symbol set to account for the given term. */

void update_element_counts2(const raw_term &rt, set<elem> &distinct_syms,
		int_t &char_count, int_t &max_int) {
	for(const elem &el : rt.e)
		if(el.type == elem::NUM) max_int = max(max_int, el.num);
		else if(el.type == elem::SYM) distinct_syms.insert(el);
		else if(el.type == elem::CHR) char_count = 256;
} 

/* Compute the number of bits required to represent first the largest
 * integer in the given program and second the universe. */

pair<int_t, int_t> prog_bit_len2(const raw_prog &rp) {
	int_t max_int = 0, char_count = 0;
	set<elem> distinct_syms;

	for(const raw_rule &rr : rp.r) {
		// Updates the counters based on the heads of the current rule
		for(const raw_term &rt : rr.h)
			update_element_counts2(rt, distinct_syms, char_count, max_int);
		// If this is a rule, update the counters based on the body
		if(rr.is_dnf() || rr.is_form()) {
			raw_form_tree prft = *rr.get_prft();
			prefold_tree2(prft, monostate {},
				[&](const raw_form_tree &t, monostate) -> monostate {
					if(t.type == elem::NONE)
						update_element_counts2(*t.rt, distinct_syms, char_count, max_int);
					return monostate {};
				});
		}
	}
	// Now compute the bit-length of the largest integer found
	size_t int_bit_len = 0, universe_bit_len = 0,
		max_elt = max_int + char_count + distinct_syms.size();
	for(; max_int; max_int >>= 1, int_bit_len++);
	for(; max_elt; max_elt >>= 1, universe_bit_len++);
	o::dbg() << "Integer Bit Length: " << int_bit_len << endl;
	o::dbg() << "Universe Bit Length: " << universe_bit_len << endl << endl;
	return {int_bit_len, universe_bit_len};
} 

/*! Go through the program and removed those queries that the function f
 * determines to be subsumed by others. While we're at it, minimize
 * (i.e. subsume a query with its part) the shortlisted queries to
 * reduce time cost of future subsumptions. This function does not
 * respect order, so it should only be used on an unordered stratum. */

std::vector<std::shared_ptr<change>> driver::brancher_subsume_queries(changed_prog &mp) {
	//TODO Check if z3 context should be static?
	const auto &[int_bit_len, universe_bit_len] = prog_bit_len2(mp.current);
	z3_context ctx(int_bit_len, universe_bit_len);

	std::vector<std::shared_ptr<change>> mutations;
	vector<raw_rule> reduced;
	for (raw_rule &rr : mp.current.r) {
		bool subsumed = false;
		for (auto nrr = reduced.begin(); nrr != reduced.end();) {
			if (check_qc(rr, *nrr, ctx)) {
				// If the current rule is contained by a rule in reduced rules,
				// then move onto the next rule in the outer loop
				mutation_del_rule del(rr);
				mutations.push_back(std::make_shared<mutation_del_rule>(del));
				subsumed = true;
				break;
			} else if (check_qc(*nrr, rr, ctx)) {
				// If current rule contains that in reduced rules, then remove
				// the subsumed rule from reduced rules
				reduced.erase(nrr);
				mutation_del_rule del(*nrr);
				mutations.push_back(std::make_shared<mutation_del_rule>(del));

			} else {
				// Neither rule contains the other. Move on.
				nrr++;
			}
		}
		if (!subsumed) reduced.push_back(rr);
	}
	return mutations;
} 

struct mutation_minimize : public virtual change  {
	driver &drvr;

	mutation_minimize(driver &d) : drvr(d) {}

	bool operator()(changed_prog &mp) const override {
		const auto &[int_bit_len, universe_bit_len] = prog_bit_len2(mp.current);
		z3_context ctx(int_bit_len, universe_bit_len);
		o::dbg() << "Minimizing rules ..." << endl << endl;
//		auto f = [this, &z3_ctx](const raw_rule &rr1, const raw_rule &rr2)
//			{ return drvr.check_qc(rr1, rr2, z3_ctx); };
		for(auto rr: mp.current.r) {
			drvr.minimize(rr, ctx);
		}
		o::dbg() << "Minimized:" << endl << endl << mp.current << endl;
		return true;
	}
};

vector<std::shared_ptr<change>> driver::brancher_minimize(changed_prog&) {
	vector<std::shared_ptr<change>> mutations;
	mutation_minimize m(*this);
	mutations.push_back(std::make_shared<mutation_minimize>(m));
	return mutations; 
} 

struct mutation_factor_rules : public virtual change  {
	driver &drvr;

	mutation_factor_rules(driver &d) : drvr(d) {}

	bool operator()(changed_prog &mp) const override {
		o::dbg() << "Factoring rules..." << endl << endl;
		drvr.factor_rules(mp.current);
		o::dbg() << "Factored Program:" << endl << endl << mp.current << endl;
		return true;
	}
};

vector<std::shared_ptr<change>> driver::brancher_factor_rules(changed_prog&) {
	vector<std::shared_ptr<change>> mutations;
	mutation_factor_rules m(*this);
	mutations.push_back(std::make_shared<mutation_factor_rules>(m));
	return mutations; 
}

struct mutation_to_split_heads : public virtual change  {
	driver &drvr;

	mutation_to_split_heads(driver &d) : drvr(d) {}

	bool operator()(changed_prog &mp) const override {
		o::dbg() << "Splitting heads ..." << endl;
		drvr.split_heads(mp.current);
		o::dbg() << "Binary Program:" << endl << mp.current << endl;
		return false;
	}
};

vector<std::shared_ptr<change>> driver::brancher_split_heads(changed_prog&) {
	vector<std::shared_ptr<change>> mutations;
	mutation_to_split_heads m(*this);
	mutations.push_back(std::make_shared<mutation_to_split_heads>(m));
	return mutations;
}

#endif //CHANGE_ME

#ifdef DELETE_ME

struct mutation_eliminate_dead_variables : public virtual change  {
	driver &drvr;

	mutation_eliminate_dead_variables(driver &d) : drvr(d) {}

	bool operator()(changed_prog &mp) const override {
		o::dbg() << "Eliminating dead variables ..." << endl << endl;
		drvr.eliminate_dead_variables(mp.current);
		o::dbg() << "Stripped TML Program:" << endl << endl << mp.current << endl;
		return true;
	}
};

vector<std::shared_ptr<change>> driver::brancher_eliminate_dead_variables(changed_prog&) {
	vector<std::shared_ptr<change>> mutations;
	mutation_eliminate_dead_variables m(*this);
	mutations.push_back(std::make_shared<mutation_eliminate_dead_variables>(m));
	return mutations;
}

struct mutation_split_bodies : public virtual change  {
	driver &drvr;

	mutation_split_bodies(driver &d) : drvr(d) {}

	bool operator()(changed_prog &mp) const override {
		o::dbg() << "Splitting bodies ..." << endl;
		drvr._bintransform(mp.current);
		o::dbg() << "Binary Program:" << endl << mp.current << endl;
		return true;
	}
};

vector<std::shared_ptr<change>> driver::brancher_split_bodies(changed_prog&) {
	vector<std::shared_ptr<change>> mutations;
	mutation_split_bodies m(*this);
	mutations.push_back(std::make_shared<mutation_split_bodies>(m));
	return mutations;
}

#endif // DELETE_ME