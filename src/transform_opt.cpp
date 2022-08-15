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
// #include "generators.h"
#include "transform_opt.h"

using namespace std;

const cost_function exp_in_heads = [](changed_prog &mp) {
	auto rs = mp.current;
	size_t c = 0.0;
	for (auto it = rs.begin(); it != rs.end(); ++it) {
		// TODO properly define this cost function
		c += (*it).size();
	}
	return c;
};

void changed_prog::operator()(change &m) {
	// apply the change to the current changed_prog
	m(*this);
}

bool best_solution::bound(changed_prog &p) {
	size_t cost = func_(p);
	if (cost < cost_) {
		cost_ = cost;
		best_ = std::make_shared<changed_prog>(p);
		return true;
	}
	return false;
}

flat_prog best_solution::solution() {
	return best_.get()->current;
}

#ifndef WORK_IN_PROGRESS

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
	// only one term and is not a goal
	return r.size() == 1 && !r[0].goal;
}

/* Returns true if the vector of terms correspond to a goal, false otherwise. */
inline bool is_goal(const flat_rule &r) {
	// TODO consider remove defensive programming
	// non empty and its a goal
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

#ifdef DELETE_ME
/* Apply a given unification to a given tail of a relation. */
term apply_unification(const unification &nf, const term &t) {
	term n(t); 
	for( size_t i = 1; i < t.size(); ++i) 
		if (nf.contains(t[i])) n[i] = nf.at(t[i]);
	return n;
}
#endif // DELETE_ME

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
 * Algorithm". ACM Trans. Program. Lang. Syst. 4 (2): 258–282] for details.
 */
optional<unification> unify(term &t1, term &t2) {
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
			// TODO avoid collisions
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
flat_rule rename_rule_vars(flat_rule &fr, int_t& lv) {
	flat_rule nfr(fr);
	map<int_t, int_t> sbs;
	for (auto &t: nfr) for (size_t i = 0; i != t.size(); ++i)
		if (!sbs.contains(t[i]) && t[i] < 0) sbs[t[i]] = --lv, t[i] = sbs[t[i]];
	return nfr;
}

/* Returns the squaring of a rule given a selection for the possible substitutions */
void square_rule(flat_rule &fr, selection &sels, flat_prog &fp) {
	flat_rule sfr; 
	// add the head of the existing rule
	sfr.emplace_back(fr[0]);
	auto lv = get_last_var(fr);
	bool unified = true;
	for (size_t i = 0; i < sels.size(); ++i) {
		auto rfr = rename_rule_vars(sels[i], lv);
		if (auto u = unify(fr[i + 1], rfr[0])) {
			#ifndef DELETE_ME
			std::cout << "UNIFICATIOIN: {";
			for (auto p: *u)
			std::cout << "{" << p.first << ':' << p.second << "}, ";
			std::cout << "}" << std::endl;
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
	// if we have selected all possible alternatives proceed with
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
	// cache vector with the selected rules to be used in squaring
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
	// new flat_prog holding the squaring of fp
	flat_prog sqr;
	// cache info for speed up the squaring holding a map between heads
	// and associated bodies
	auto idx = index_rules(fp);
	for (auto fr: fp) {
		if(is_fact(fr) || is_goal(fr)) 
			sqr.insert(fr);
		else square_rule(fr, sqr, idx);
	}
	return sqr;
}

/* Query conatainment*/

/* Provides consistent conversions of TML objects into Z3. */
struct z3_context {
	size_t arith_bit_len;
	size_t universe_bit_len;
	z3::context context;
	z3::solver solver;
	z3::expr_vector head_rename;
	z3::sort bool_sort;
	z3::sort value_sort;
	std::map<rel_info, z3::func_decl> rel_to_decl;
	std::map<elem, z3::expr> var_to_decl;
	std::map<raw_rule, z3::expr> rule_to_decl;
	
	z3_context(size_t arith_bit_len, size_t universe_bit_len);

	z3::func_decl rel_to_z3(const raw_term& rt);
	z3::expr globalHead_to_z3(const int_t pos);
	z3::expr fresh_constant();
	z3::expr arg_to_z3(const elem& el);
	z3::expr z3_head_constraints(const raw_term &head,
		std::map<elem, z3::expr> &body_rename);
	z3::expr term_to_z3(const raw_term &rel);
	z3::expr rule_to_z3(const raw_rule &rr, dict_t &dict);
};

/* Initialize an empty context that can then bn e populated with TML to Z3
 * conversions. value_sort is either a bit-vector whose width can
 * contain the enire program universe and will be used for all Z3
 * relation arguments and bool_sort is the "return" type of all
 * relations. */

z3_context::z3_context(size_t arith_bit_len, size_t universe_bit_len) :
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

/* Function to lookup and create where necessary a Z3 representation of
 * a relation. */

z3::func_decl z3_context::rel_to_z3(const raw_term& rt) {
	const auto &rel = rt.e[0];
	const rel_info &rel_sig = get_relation_info(rt);
	if(auto decl = rel_to_decl.find(rel_sig); decl != rel_to_decl.end())
		return decl->second;
	else {
		z3::sort_vector domain(context);
		for (int_t i = rt.get_formal_arity(); i != 0; --i)
			domain.push_back(value_sort);
		z3::func_decl ndecl =
			context.function(rel.to_str().c_str(), domain, bool_sort);
		rel_to_decl.emplace(make_pair(rel_sig, ndecl));
		return ndecl;
	}
}

/* Function to create Z3 representation of global head variable names.
 * The nth head variable is always assigned the same Z3 constant in
 * order to ensure that different rules are comparable. */

z3::expr z3_context::globalHead_to_z3(const int_t pos) {
	for (int_t i=head_rename.size(); i<=pos; ++i)
		head_rename.push_back(z3::expr(context, fresh_constant()));
	return head_rename[pos];
}

/* Function to lookup and create where necessary a Z3 representation of
 * elements. */
z3::expr z3_context::arg_to_z3(const elem& el) {
	if(auto decl = var_to_decl.find(el); decl != var_to_decl.end())
		return decl->second;
	else if(el.type == elem::NUM) {
		const z3::expr &ndecl =
			context.bv_val(el.num, value_sort.bv_size());
		var_to_decl.emplace(make_pair(el, ndecl));
		return ndecl;
	} else if (el.ch != 0) {
		const z3::expr &ndecl =
			context.constant(el.to_str().c_str(), value_sort);
		var_to_decl.emplace(make_pair(el, ndecl));
		return ndecl;
	}
}

/* Construct a formula that constrains the head variables. The
 * constraints are of two sorts: the first equate pairwise identical
 * head variables to each other, and the second equate literals to their
 * unique Z3 equivalent. Also exports a mapping of each head element to
 * the Z3 head variable it has been assigned to. */
z3::expr z3_context::z3_head_constraints(const raw_term &head, map<elem, z3::expr> &body_rename) {
	z3::expr restr = context.bool_val(true);
	for (size_t i = 0; i < head.e.size() - 3; ++i) {
		const elem &el = head.e[i + 2];
		const z3::expr &var = globalHead_to_z3(i);
		if(const auto &[it, found] = body_rename.try_emplace(el, var); !found)
			restr = restr && it->second == var;
		else if (el.type != elem::VAR)
			restr = restr && var == arg_to_z3(el);
	}
	return restr;
}

/* Given a term, output the equivalent Z3 expression using and updating
 * the mappings in the context as necessary. */
z3::expr z3_context::term_to_z3(const raw_term &rel) {
	if(rel.extype == raw_term::REL) {
		z3::expr_vector vars_of_rel (context);
		for (auto el = rel.e.begin()+2; el != rel.e.end()-1; ++el) {
			// pushing head variables
			vars_of_rel.push_back(arg_to_z3(*el));
		}
		return rel_to_z3(rel)(vars_of_rel);
	} else assert(false); //should never reach here
}

/* Make a fresh Z3 constant. */
z3::expr z3_context::fresh_constant() {
	return z3::expr(context,
		Z3_mk_fresh_const(context, nullptr, value_sort));
}

/* Checks if the rule has a single head and a body that is either a tree
 * or a non-empty DNF. Second order quantifications and builtin terms
 * are not supported. */

bool is_query (const raw_rule &rr) {
	// Ensure that there are no multiple heads
	if(rr.h.size() != 1) return false;
	// Ensure that head is positive
	if(rr.h[0].neg) return false;
	// Ensure that this rule is either a tree or non-empty DNF
	if(!(rr.is_dnf() || rr.is_form())) return false;
	// Ensure that there is no second order quantification or builtins in
	// the tree
	return true;
}

bool disjoint(const raw_rule &r1, const raw_rule &r2) {
	auto get_terms = [](vector<raw_term> t) { return t[0]; };
	auto r1_terms = r1.b | views::transform(get_terms);
	auto r2_terms = r2.b | views::transform(get_terms);
	vector<raw_term> i;
	set_intersection(r1_terms.begin(), r1_terms.end(), r2_terms.begin(), r2_terms.end(), back_inserter(i));
	return !i.empty();
}

bool comparable(const raw_rule &r1, const raw_rule &r2) {
	return (r1.h[0].e[0] == r2.h[0].e[0] && r1.h[0].arity == r2.h[0].arity);
}

/*! 
 * Checks if r1 is contained in r2 or vice versa.
 * Returns false if rules are not comparable or not contained.
 * Returns true if r1 is contained in r2. 
 */
bool check_qc(const raw_rule &r1, const raw_rule &r2, z3_context &ctx) {
	// have we compute already the result
	static map<pair<raw_rule, raw_rule>, bool> memo;
	auto key = make_pair(r1, r2);
	if (memo.contains(key)) {
		return memo[key];
	}

	// if the heads in the body are disjoint, no qc is possible
	if (disjoint(r1, r2) || !comparable(r1, r2) || !is_query(r1) || !is_query(r2)) {
		memo[key] = false;
		swap(get<0>(key), get<1>(key));
		memo[key] = false;
	}

	// do the expensive work
	o::dbg() << "Z3 QC Testing if " << r1 << " <= " << r2 << " : ";
	// Get head variables for z3
	z3::expr_vector bound_vars(ctx.context);
	for (uint_t i = 0; i != r1.h[0].e.size() - 3; ++i)
		bound_vars.push_back(ctx.globalHead_to_z3(i));
	// Rename head variables on the fly such that they match
	// on both rules
	
	// TODO adapt this without dict
	// -> dict_t &dict = tbl->get_dict();
	// -> z3::expr rule1 = ctx.rule_to_z3(r1, dict);
	// -> z3::expr rule2 = ctx.rule_to_z3(r2, dict);
	// -> ctx.solver.push();
	// Add r1 => r2 to solver
	// -> if (bound_vars.empty()) ctx.solver.add(!z3::implies(rule1, rule2));
	// -> else ctx.solver.add(!z3::forall(bound_vars,z3::implies(rule1, rule2)));
	bool res = ctx.solver.check() == z3::unsat;
	ctx.solver.pop();
	o::dbg() << res << endl;
	memo[key] = res;
	return res;
}

/* Given a rule, output the body of this rule converted to the
 * corresponding Z3 expression. Caches the conversion in the context in
 * case the same rule is needed in future. */

z3::expr z3_context::rule_to_z3(const raw_rule &rr, dict_t &dict) {
	if(auto decl = rule_to_decl.find(rr); decl != rule_to_decl.end())
		return decl->second;
	// create map from bound_vars
	map<elem, z3::expr> body_rename;
	z3::expr restr = z3_head_constraints(rr.h[0], body_rename);
	// Collect bound variables of rule and restrictions from constants in head
	set<elem> free_vars;
	vector<elem> bound_vars(rr.h[0].e.begin() + 2, rr.h[0].e.end() - 1);
	collect_free_vars(*rr.get_prft(), bound_vars, free_vars);
	// Free variables are existentially quantified
	z3::expr_vector ex_quant_vars (context);
	for (const auto& var : free_vars)
		ex_quant_vars.push_back(arg_to_z3(var));
	map<elem, z3::expr> var_backup;
	// For the intent of constructing this Z3 expression, replace head
	// variable expressions with the corresponding global head
	for(auto &[el, constant] : body_rename) {
		var_backup.emplace(make_pair(el, arg_to_z3(el)));
		var_to_decl.at(el) = constant;
	}
	// TODO fix this code 
	// Construct z3 expression from rule
	// -> z3::expr formula = tree_to_z3(*rr.get_prft(), dict);
	// Now undo the global head mapping for future constructions
	// -> for(auto &[el, constant] : var_backup) var_to_decl.at(el) = constant;
	// -> z3::expr decl; // ->  = restr && (ex_quant_vars.empty() ? formula : z3::exists(ex_quant_vars, formula));
	// -> rule_to_decl.emplace(make_pair(rr, decl));
	// -> return decl;
}

/* Go through the subtrees of the given rule and see which of them can
 * be removed whilst preserving rule equivalence according to the given
 * containment testing function. */
void minimize(raw_rule &rr, z3_context &ctx) {
	// have we compute already the result
	static set<raw_rule> memo;
	if (memo.contains(rr)) {
		return;
	}
	// TODO Write a quick test to avoid easy cases
	
	// do the expensive computation
	if(rr.is_fact() || rr.is_goal()) return;
	// Switch to the formula tree representation of the rule if this has
	// not yet been done for this is a precondition to minimize_aux. Note
	// the current form so that we can attempt to restore it afterwards.
	bool orig_form = rr.is_dnf();
	rr = rr.try_as_prft();
	// Copy the rule to provide scratch for minimize_aux
	raw_rule var_rule = rr;
	// Now minimize the formula tree of the given rule using the given
	// containment testing function
	// TODO fix this code
	// -> minimize_aux(rr, var_rule, *rr.prft, *var_rule.prft, ctx);
	// If the input rule was in DNF, provide the output in DNF
	if(orig_form) rr = rr.try_as_b();
	// remmber raw_rule as minimized
	memo.insert(rr);
}

/* Minimize the rule using CQC. */
flat_rule minimize_rule(flat_rule &fp) {
	flat_rule mnmzd;
	// do minimization
	return mnmzd;
}

/* Returns all the possible splittings of the rule. */
set<pair<flat_rule, flat_rule>> split_rule(flat_rule &fp) {
	set<pair<flat_rule, flat_rule>> splt;
	// do splitting
	return splt;
}

#endif // WORK_IN_PROGRESS

#ifdef CHANGE_ME
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

#ifdef DELETE_ME
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