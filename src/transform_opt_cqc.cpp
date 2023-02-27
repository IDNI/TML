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
#include <ranges>
#include <algorithm>

#include "z3++.h"
#include "iterators.h"
#include "transform_opt_cqc.h"

using namespace std;

/* Query conatainment and minimization */

/* Provides consistent conversions of TML objects into Z3. */

class z3_context {
private:
	size_t arith_bit_len;
	size_t universe_bit_len;
	z3::context context;
	z3::solver solver;
	z3::expr_vector head_rename;
	z3::sort bool_sort;
	z3::sort value_sort;
	map<rel_arity, z3::func_decl> rel_to_decl;
	map<int, z3::expr> var_to_decl;
	map<flat_rule, z3::expr> rule_to_decl;

public:
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
		auto rel_sig = get_rel_info(t);
		if(auto decl = rel_to_decl.find(rel_sig); decl != rel_to_decl.end())
			return decl->second;
		else {
			z3::sort_vector domain(context);
			for (size_t i = 0; i != t.size(); ++i)
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

	z3::expr arg_to_z3(const int arg) {
		if(auto decl = var_to_decl.find(arg); decl != var_to_decl.end())
			return decl->second;
		else if(arg >= 0) {
			const z3::expr &ndecl = context.bv_val(arg, value_sort.bv_size());
			var_to_decl.try_emplace(arg, ndecl);
			return ndecl;
		} else {
			auto cons = "?0v" + to_string_(-arg);
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
			for (auto arg = t.begin(); arg != t.end(); ++arg) {
				// Pushing head variables
				vars_of_rel.push_back(arg_to_z3(*arg));
			}
			return rel_to_z3(t)(vars_of_rel);
		} else if(t.extype == term::EQ) {
			return arg_to_z3(t[0]) == arg_to_z3(t[1]);
		} else if(t.extype <= term::LEQ) {
			return arg_to_z3(t[0]) <= arg_to_z3(t[2]);
		} else if(t.extype <= term::ARITH && t.size() == 3) {
			// Obtain the Z3 equivalents of TML elements
			z3::expr arg1 = arg_to_z3(t[0]), arg2 = arg_to_z3(t[2]),
				arg3 = arg_to_z3(t[2]);
			// The arithmetic universe may be smaller than the entire universe,
			// so zero the high bits of arithmetic expressions to ensure that
			// only the lower bits are relevant in comparisons
			z3::expr embedding = universe_bit_len == arith_bit_len ?
				context.bool_val(true) :
				arg1.extract(universe_bit_len-1, arith_bit_len) == 0 &&
				arg2.extract(universe_bit_len-1, arith_bit_len) == 0 &&
				arg3.extract(universe_bit_len-1, arith_bit_len) == 0;
			// Its possible that the largest integer in TML program is 0. Z3
			// does not support 0-length bit-vectors, so short-circuit
			if(arith_bit_len == 0) return embedding;
			z3::expr arg1_lo = arg1.extract(arith_bit_len-1, 0),
				arg2_lo = arg2.extract(arith_bit_len-1, 0),
				arg3_lo = arg3.extract(arith_bit_len-1, 0);
			// Finally produce the arithmetic constraint based on the low bits
			// of the operands
			switch(t.arith_op) {
				case ADD: return (arg1_lo + arg2_lo) == arg3_lo && embedding;
				case SUB: return (arg1_lo - arg2_lo) == arg3_lo && embedding;
				case MULT: return (arg1_lo * arg2_lo) == arg3_lo && embedding;
				case SHL: return shl(arg1_lo, arg2_lo) == arg3_lo && embedding;
				case SHR: return lshr(arg1_lo, arg2_lo) == arg3_lo && embedding;
				case BITWAND: return (arg1_lo & arg2_lo) == arg3_lo && embedding;
				case BITWXOR: return (arg1_lo ^ arg2_lo) == arg3_lo && embedding;
				case BITWOR: return (arg1_lo | arg2_lo) == arg3_lo && embedding;
				default: assert(false); //should never reach here
			}
		} else if(t.extype <= term::ARITH && t.size() == 4) {
			// Obtain the Z3 equivalents of TML elements
			z3::expr arg1 = arg_to_z3(t[0]), arg2 = arg_to_z3(t[1]),
				arg3 = arg_to_z3(t[2]), arg4 = arg_to_z3(t[3]);
			// The arithmetic universe may be smaller than the entire universe,
			// so zero the high bits of arithmetic expressions to ensure that
			// only the lower bits are relevant in comparisons
			z3::expr embedding = universe_bit_len == arith_bit_len ?
				context.bool_val(true) :
				arg1.extract(universe_bit_len-1, arith_bit_len) == 0 &&
				arg2.extract(universe_bit_len-1, arith_bit_len) == 0 &&
				arg3.extract(universe_bit_len-1, arith_bit_len) == 0 &&
				arg4.extract(universe_bit_len-1, arith_bit_len) == 0;
			// Its possible that the largest integer in TML program is 0. Z3
			// does not support 0-length bit-vectors, so short-circuit
			if(arith_bit_len == 0) return embedding;
			// Since this is double precision arithmetic, join the 3rd and 4th
			// operands to form the RHS
			z3::expr arg1_lo = zext(arg1.extract(arith_bit_len-1, 0), arith_bit_len),
				arg2_lo = zext(arg2.extract(arith_bit_len-1, 0), arith_bit_len),
				arg34 = concat(arg3.extract(arith_bit_len-1, 0),
					arg4.extract(arith_bit_len-1, 0));
			// Finally produce the arithmetic constraint based on the low bits
			// of the LHS operands and full bits of the RHS operand
			switch(t.arith_op) {
				case ADD: return embedding && (arg1_lo + arg2_lo) == arg34;
				case MULT: return embedding && (arg1_lo * arg2_lo) == arg34;
				default: assert(false); //should never reach here
			} 
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
		set<int> free_vars;
		set<int> bound_vars;
		for (auto& i: r[0]) if (i < 0) bound_vars.insert(i);
		for (auto& t: r) for(auto& i: t)
			if (i < 0  && !bound_vars.contains(i)) free_vars.insert(i); 
		// Free variables are existentially quantified
		z3::expr_vector ex_quant_vars (context);
		for (const auto& var : free_vars)
			ex_quant_vars.push_back(arg_to_z3(var));
		map<int, z3::expr> var_backup;
		// For the intent of constructing this Z3 expression, replace head
		// variable expressions with the corresponding global head
		for(auto &[arg, constant] : body_rename) {
			var_backup.try_emplace(arg, arg_to_z3(arg));
			var_to_decl.try_emplace(arg, constant);
		}
		// Construct z3 expression from rule
		z3::expr body = context.bool_val(true);
		for (int i = 1; i!= r.size(); ++i) body = body && term_to_z3(r[i]);
		z3::expr head = term_to_z3(r[0]);
		z3::expr formula = (!body) || head;
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
		// auto get_heads = [](term t) { return t[0]; };
		ints r1_terms, r2_terms, intersection;
		ranges::transform(r1.begin(), r1.end(), back_inserter(r1_terms), [](auto& t) { return t.tab; });
		ranges::transform(r2.begin(), r2.end(), back_inserter(r2_terms), [](auto& t) { return t.tab; });
		ranges::sort(r1_terms.begin(), r1_terms.end());
		ranges::sort(r2_terms.begin(), r2_terms.end());
		ranges::set_intersection(r1_terms.begin(), r1_terms.end(),
			r2_terms.begin(), r2_terms.end(), 
			back_inserter(intersection));
		return intersection.empty();
	}

	bool comparable(const flat_rule &r1, const flat_rule &r2) const {
		return (r1[0].tab == r2[0].tab && r1[0].size() == r2[0].size());
	}

	/* Creates a new rule from head and body. */

	flat_rule get_rule_from(term &h, vector<term> &b) const {
		flat_rule nr;
		nr.emplace_back(h);
		for (auto &t: b) nr.emplace_back(t);
		return nr;
	}

public:

	/* Checks if r1 is contained in r2. */

	bool check_qc(const flat_rule &r1, const flat_rule &r2) {
		// Have we compute already the result?
		static map<pair<flat_rule, flat_rule>, bool> memo;
		auto key = make_pair(r1, r2);
		if (memo.contains(key)) {
			return memo[key];
		}

		// If the heads in the body are disjoint, no qc is possible
		if (r1.empty() || r2.empty() || disjoint(r1, r2) || !comparable(r1, r2)) {
			memo[key] = false;
			swap(get<0>(key), get<1>(key));
			memo[key] = false;
			return false;
		}

		// Do the expensive work
		// o::dbg() << "Z3 QC Testing if "; // << r1 << " <= " << r2 << " : ";
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

	/* Minimize the given rule using CQC. */

	// TODO Check that really is a Chruch-Rossen like algorithm.
	flat_rule minimize(flat_rule const &r) {
		// Have we compute already the result?
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
		// ...generate all possible body subsets.
		for (auto b : powerset_range(body)) {
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
};

/* Compute the number of bits required to represent first the largest
* integer in the given program and second the universe. */

pair<int_t, int_t> prog_bit_len_opt(const flat_prog &rp) {
	int_t max_int = 0, char_count = 0;
	set<int_t> distinct_syms;

	for(const flat_rule &rr : rp) {	
		// Updates the counters based on the heads of the current rule
		for(const term &rt : rr) {
			distinct_syms.insert(rt.tab);
			for (const auto &a: rt) max_int = max(max_int, a);
		} 
	}
	// Now compute the bit-length of the largest integer found
	size_t int_bit_len = 0, universe_bit_len = 0,
		max_elt = max_int + char_count + distinct_syms.size();
	for(; max_int; max_int >>= 1, int_bit_len++);
	for(; max_elt; max_elt >>= 1, universe_bit_len++);
	// o::dbg() << "Integer Bit Length: " << int_bit_len << endl;
	// o::dbg() << "Universe Bit Length: " << universe_bit_len << endl << endl;
	return {int_bit_len, universe_bit_len};
} 

z3_context& get_z3_context(flat_prog const &fp) {
	// TODO Use a map according to bit_len & universe_bit_len for z3_context
	const auto &[int_bit_len, universe_bit_len] = prog_bit_len_opt(fp);
	static z3_context ctx(int_bit_len, universe_bit_len);
	return ctx;
}

flat_rule minimize_rule(flat_rule const &r, flat_prog const &p) {
	return get_z3_context(p).minimize(r);
}

flat_prog minimize_rules(flat_prog const &p) {
	flat_prog mrp;
	for (auto &r: p) 
		mrp.insert(get_z3_context(p).minimize(r));
	return mrp;
}

bool rule_contains(flat_rule const &r1, flat_rule const &r2, flat_prog const &p) {
	return get_z3_context(p).check_qc(r1, r2);
}
