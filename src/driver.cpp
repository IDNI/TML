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

signature get_signature(const raw_term &rt) {
	return {rt.e[0].e, rt.arity};
}

void driver::directives_load(raw_prog& p, lexeme& trel,
		const raw_term &false_term) {
//	int_t rel;
	for (const directive& d : p.d)
		switch (d.type) {
		case directive::BWD: pd.bwd = true; break;
		case directive::TRACE: trel = d.rel.e; break;
		case directive::EDOMAIN: transform_domains(p, d); break;
		case directive::EVAL: transform_evals(p, d); break;
		case directive::QUOTE: transform_quotes(p, false_term, d); break;
		case directive::CODEC: transform_codecs(p, d); break;
		case directive::INTERNAL:
			p.hidden_rels.insert(get_signature(d.internal_term)); break;
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


/* Reduce the top-level logical operator to a more primitive one if this
 * is possible. That is, reduce implications and co-implications to
 * conjunctions/disjunctions, and reduce uniqueness quantifications to
 * universal and existential quantifications. Useful for avoiding having
 * to separately process these operators. */

sprawformtree expand_formula_node(const sprawformtree &t, dict_t &d) {
	switch(t->type) {
		case elem::IMPLIES: {
			// Implication is logically equivalent to the following
			return make_shared<raw_form_tree>(elem::ALT,
				make_shared<raw_form_tree>(elem::NOT, t->l), t->r);
		} case elem::COIMPLIES: {
			// Co-implication is logically equivalent to the following
			return make_shared<raw_form_tree>(elem::AND,
				make_shared<raw_form_tree>(elem::IMPLIES, t->l, t->r),
				make_shared<raw_form_tree>(elem::IMPLIES, t->r, t->l));
		} case elem::UNIQUE: {
			// The uniqueness quantifier is logically equivalent to the
			// following
			const elem evar = elem::fresh_var(d), qvar = *(t->l->el);
			return make_shared<raw_form_tree>(elem::EXISTS,
				make_shared<raw_form_tree>(evar),
				make_shared<raw_form_tree>(elem::FORALL,
					make_shared<raw_form_tree>(qvar),
					make_shared<raw_form_tree>(elem::COIMPLIES, t->r,
						make_shared<raw_form_tree>(
							raw_term(raw_term::EQ, { evar, elem(elem::EQ), qvar })))));
		} default: {
			return t;
		}
	}
}

/* Puts the formulas parented by a tree of associative binary operators
 * into a flat list. */

void driver::flatten_associative(const elem::etype &tp,
		const sprawformtree &tree, vector<sprawformtree> &tms) {
	if(tree->type == tp) {
		flatten_associative(tp, tree->l, tms);
		flatten_associative(tp, tree->r, tms);
	} else {
		tms.push_back(tree);
	}
}

/* Checks if the body of the given rule is conjunctive. */

bool is_cq(const raw_rule &rr) {
	// Ensure that there are no disjunctions
	if(rr.h.size() != 1 || rr.b.size() != 1) return false;
	// Ensure that head is positive
	if(rr.h[0].neg) return false;
	// Ensure that this rule is a proper rule
	if(!rr.is_rule()) return false;
	// Ensure that each body term is positive and is a relation
	for(const raw_term &rt : rr.b[0]) {
		if(rt.neg || rt.extype != raw_term::REL) return false;
	}
	return true;
}

/* Checks if the body of the given rule is conjunctive with negation. */

bool is_cqn(const raw_rule &rr) {
	// Ensure that there are no disjunctions
	if(rr.h.size() != 1 || rr.b.size() != 1) return false;
	// Ensure that head is positive
	if(rr.h[0].neg) return false;
	// Ensure that this rule is a proper rule
	if(!rr.is_rule()) return false;
	// Ensure that each body term is a relation
	for(const raw_term &rt : rr.b[0]) {
		if(rt.extype != raw_term::REL) return false;
	}
	return true;
}

// Recurse through the given formula tree calling the given function
// with the accumulator

template<typename X, typename F>
		X fold_tree(const sprawformtree &t, X acc, const F &f) {
	switch(t->type) {
		case elem::ALT: case elem::AND: case elem::IMPLIES: case elem::COIMPLIES:
				case elem::EXISTS: case elem::FORALL: case elem::UNIQUE:
			// Fold through binary trees by threading accumulator through both
			// the LHS and RHS
			return fold_tree(t->r, fold_tree(t->l, f(t, acc), f), f);
		// Fold though unary trees by threading accumulator through this
		// node then single child
		case elem::NOT: return fold_tree(t->l, f(t, acc), f);
		// Otherwise for leaf nodes like terms and variables, thread
		// accumulator through just this node
		default: return f(t, acc);
	}
}

/* Checks if the rule has a single head and a body that is either a tree
 * or a non-empty DNF. Second order quantifications and terms that are
 * neither relations nor equalities are not supported. */

bool is_query (const raw_rule &rr, const raw_term &false_term) {
	// Ensure that there are no multiple heads
	if(rr.h.size() != 1) return false;
	// Ensure that head is positive
	if(rr.h[0].neg) return false;
	// Ensure that this rule is either a tree or non-empty DNF
	if(!(rr.is_rule() || rr.is_form())) return false;
	// Ensure that all terms in the tree are either relations or
	// equalities and that there is no second order quantification
	if(!fold_tree(rr.get_prft(false_term), true,
			[&](const sprawformtree &t, bool acc) -> bool {
				return acc && (t->type != elem::NONE ||
					t->rt->extype == raw_term::REL ||
					t->rt->extype == raw_term::EQ) && t->type != elem::SYM;}))
		return false;
	return true;
}

/* Convenience function for getting relation name and arity from
 * term. */

rel_info get_relation_info(const raw_term &rt) {
	return make_tuple(rt.e[0], rt.e.size() - 3);
}

/* If rr1 and rr2 are both conjunctive queries, check if there is a
 * homomorphism rr2 to rr1. By the homomorphism theorem, the existence
 * of a homomorphism implies that rr1 is contained by rr2. */

bool driver::cqc(const raw_rule &rr1, const raw_rule &rr2) {
	// Get dictionary for generating fresh symbols
	dict_t &old_dict = tbl->get_dict();
	dict_t d;
	d.op = old_dict.op;
	d.cl = old_dict.cl;

	if(is_cq(rr1) && is_cq(rr2) &&
			get_relation_info(rr1.h[0]) == get_relation_info(rr2.h[0])) {
		o::dbg() << "CQC Testing if " << rr1 << " <= " << rr2 << endl;
		
		// Freeze the variables and symbols of the rule we are checking the
		// containment of
		map<elem, elem> freeze_map;
		raw_rule frozen_rr1 = freeze_rule(rr1, freeze_map, d);

		// Build up the queries necessary to check homomorphism.
		set<raw_term> edb(frozen_rr1.b[0].begin(), frozen_rr1.b[0].end());
		o::dbg() << "Canonical Database: " << edb << endl;
		raw_prog nrp;
		nrp.r.push_back(rr2);

		// Run the queries and check for the frozen head. This process can
		// be optimized by inlining the frozen head of rule 1 into rule 2.
		set<raw_term> results;
		tables::run_prog(edb, nrp, d, opts, ir, results);
		for(const raw_term &res : results) {
			if(res == frozen_rr1.h[0]) {
				// If the frozen head is found, then there is a homomorphism
				// between the two rules.
				o::dbg() << "True: " << rr1 << " <= " << rr2 << endl;
				return true;
			}
		}
		// If no frozen head found, then there is no homomorphism.
		o::dbg() << "False: " << rr1 << " <= " << rr2 << endl;
		return false;
	} else {
		return false;
	}
}

/* If rr1 and rr2 are both conjunctive bodies, check if there is a
 * homomorphism rr2 to rr1. By the homomorphism theorem, the existence
 * of a homomorphism implies that a valid substitution for rr1 can be
 * turned into a valid substitution for rr2. This function provides all
 * off them. */

bool driver::cbc(const raw_rule &rr1, raw_rule rr2,
		set<terms_hom> &homs) {
	// Get dictionary for generating fresh symbols
	dict_t &old_dict = tbl->get_dict();
	dict_t d;
	d.op = old_dict.op;
	d.cl = old_dict.cl;

	if(is_cq(rr1) && is_cq(rr2)) {
		o::dbg() << "Searching for homomorphisms from " << rr2.b[0]
			<< " to " << rr1.b[0] << endl;
		// Freeze the variables and symbols of the rule we are checking the
		// containment of
		// Map from variables occuring in rr1 to frozen symbols
		map<elem, elem> freeze_map;
		raw_rule frozen_rr1 = freeze_rule(rr1, freeze_map, d);
		// Map from frozen symbols to variables occuring in rr1
		map<elem, elem> unfreeze_map;
		for(const auto &[k, v] : freeze_map) {
			unfreeze_map[v] = k;
		}

		// Build up the extensional database necessary to check homomorphism.
		set<raw_term> edb;
		// Map from term ids to terms in rr1
		map<elem, raw_term> term_map;
		int j = 0;
		// First put the frozen terms of rr1 into our containment program
		for(raw_term &rt : frozen_rr1.b[0]) {
			// Record the mapping from the term id to the raw_term it
			// represents
			elem term_id = elem::fresh_sym(d);
			term_map[term_id] = rr1.b[0][j++];
			// Mark our frozen term with an id so that we can trace the terms
			// involved in the homomorphism if it exists
			rt.e.insert(rt.e.begin() + 2, term_id);
			rt.calc_arity(nullptr);
			edb.insert(rt);
		}
		
		o::dbg() << "Canonical Database: " << edb << endl;
		
		// Build up the query that proves the existence of a homomorphism
		// Make a new head for rr2 that exports all the variables used in
		// its body + ids of the frozen terms it binds to
		set<elem> rr2_body_vars_set;
		collect_vars(rr2.b[0].begin(), rr2.b[0].end(), rr2_body_vars_set);
		vector<elem> rr2_new_head = { elem::fresh_temp_sym(d), elem_openp };
		rr2_new_head.insert(rr2_new_head.end(), rr2_body_vars_set.begin(),
			rr2_body_vars_set.end());
		// Prepend term id variables to rr2's body terms and export the term
		// ids through the head
		for(raw_term &rt : rr2.b[0]) {
			// This variable will bind to the term id of a frozen body term
			// used in the homomorphism
			elem term_id = elem::fresh_var(d);
			rt.e.insert(rt.e.begin() + 2, term_id);
			rt.calc_arity(nullptr);
			rr2_new_head.push_back(term_id);
		}
		rr2_new_head.push_back(elem_closep);
		// Put body and head together and make containment program
		rr2.h[0] = raw_term(rr2_new_head);
		raw_prog nrp;
		nrp.r.push_back(rr2);

		// Run the queries and check for the frozen head. This process can
		// be optimized by inlining the frozen head of rule 1 into rule 2.
		set<raw_term> results;
		if(!tables::run_prog(edb, nrp, d, opts, ir, results)) return false;
		for(const raw_term &res : results) {
			// If the result comes from the containment query (i.e. it is not
			// one of the frozen terms), then there is a homomorphism between
			// the bodies
			raw_term hd_src = rr2.h[0];
			if(res.e[0] == hd_src.e[0]) {
				var_subs var_map;
				set<raw_term> target_terms;
				// Now we want to express the homomorphism in terms of the
				// original (non-frozen) variables and terms of rr1.
				for(size_t i = 2; i < res.e.size() - 1; i++) {
					// If current variable is a body var
					if(rr2_body_vars_set.find(hd_src.e[i]) != rr2_body_vars_set.end()) {
						// Then trace the original var through the unfreeze map
						var_map[hd_src.e[i]] = at_default(unfreeze_map, res.e[i], res.e[i]);
					} else {
						// Otherwise trace the original term through the term map
						target_terms.insert(term_map[res.e[i]]);
					}
				}
				homs.insert(make_pair(target_terms, var_map));
				// Print the homomorphism found
				o::dbg() << "Found homomorphism from " << rr2.b[0] << " to "
					<< target_terms << " under mapping {";
				for(auto &[k, v] : var_map) {
					o::dbg() << k << " -> " << v << ", ";
				}
				o::dbg() << "}" << endl;
			}
		}
		// If no results produced, then there is no homomorphism.
		return true;
	} else {
		return false;
	}
}

/* Given a homomorphism (i.e. a pair comprising variable substitutions
 * and terms surjected onto) and the rule that a homomorphism maps into,
 * determine which variables of the domain would be needed to express
 * constraints in the codomain. */

void driver::compute_required_vars(const raw_rule &rr,
		const terms_hom &hom, set<elem> &orig_vars) {
	auto &[rts, vs] = hom;
	// Get all the terms used by the given rule.
	set<raw_term> aggregate(rr.h.begin(), rr.h.end());
	aggregate.insert(rr.b[0].begin(), rr.b[0].end());
	// Make a vector containing all terms used by the given rule that are
	// not in homomorphism target.
	vector<raw_term> diff(aggregate.size());
	auto it = set_difference(aggregate.begin(), aggregate.end(),
		rts.begin(), rts.end(), diff.begin());
	diff.resize(it - diff.begin());
	// Get variables used outside homomorphism target
	set<elem> diff_vars;
	collect_vars(diff.begin(), diff.end(), diff_vars);
	// Get variables used inside homomorphism target
	set<elem> rts_vars;
	collect_vars(rts.begin(), rts.end(), rts_vars);
	// Compute the variables of the homomorphism target that we need to
	// retain control of
	vector<elem> nonfree_vars(diff_vars.size());
	auto jt = set_intersection(diff_vars.begin(), diff_vars.end(),
		rts_vars.begin(), rts_vars.end(), nonfree_vars.begin());
	nonfree_vars.resize(jt - nonfree_vars.begin());
	// Trace these variables of the homomorphism target to the
	// homomorphism source.
	for(auto &[var, covar] : vs) {
		if(find(nonfree_vars.begin(), nonfree_vars.end(), covar) !=
				nonfree_vars.end()) {
			orig_vars.insert(var);
		}
	}
}

/* Count the number of rules (including the given one) that derive facts
 * for the same relation that the given rule derives facts for. */

int_t driver::count_related_rules(const raw_rule &rr1, const raw_prog &rp) {
	int_t count = 0;
	for(const raw_rule &rr2 : rp.r) {
		if(rr1.h[0].e[0] == rr2.h[0].e[0] &&
				rr1.h[0].e.size() == rr2.h[0].e.size()) {
			count++;
		}
	}
	return count;
}

/* Takes two pure TML rules and returns true if the first is "smaller"
 * than the second. Smaller means less conjuncts in the body, and in the
 * case of a tie means less arguments in the head. */

bool rule_smaller(const raw_rule &rr2, const raw_rule &rr1) {
	if(rr1.b.size() == 1 && rr2.b.size() == 1) {
		if(rr1.b[0].size() == rr2.b[0].size()) {
			return rr1.h[0].e.size() > rr2.h[0].e.size();
		} else {
			return rr1.b[0].size() > rr2.b[0].size();
		}
	} else {
		return rr1.b.size() > rr2.b.size();
	}
}

/* Algorithm to factor the rules in a program using other rules.
 * Starting with the conjunctive rules with the biggest bodies, record
 * all the homomorphisms from this body into the bodies of other rules.
 * Afterwards, check if the head of this rule could be substituted
 * verbatim into the bodies of other rules, or whether a temporary
 * relation taking more arguments would be required. Afterwards,
 * replace the homomorphism targets with our chosen head. */

void driver::factor_rules(raw_prog &rp) {
	// Get dictionary for generating fresh symbols
	dict_t &d = tbl->get_dict();
	
	o::dbg() << "Factorizing rules ..." << endl;
	
	// Sort the rules so the biggest come first. Idea is that we want to
	// reduce total substitutions by doing the biggest factorizations
	// first. Also prioritizing rules with more arguments to reduce chance
	// that tmprel with more arguments is created.
	sort(rp.r.rbegin(), rp.r.rend(), rule_smaller);
	// The place where we temporarily store our temporary rules
	vector<raw_rule> pending_rules;
	// Go through the rules we want to try substituting into other
	for(raw_rule &rr2 : rp.r) {
		// Because we use a conjunctive homomorphism finding rule
		if(is_cq(rr2) && rr2.b[0].size() > 1) {
			// The variables of the current rule that we'd need to be able to
			// constrain/substitute into
			set<elem> needed_vars;
			set<tuple<raw_rule *, terms_hom>> agg;
			// Now let's look for rules that we can substitute the current
			// into
			for(raw_rule &rr1 : rp.r) {
				set<terms_hom> homs;
				// Find all the homomorphisms between outer and inner rule. This
				// way we can substitute the outer rule into the inner multiple
				// times.
				if(is_cq(rr1) && cbc(rr1, rr2, homs)) {
					for(const terms_hom &hom : homs) {
						auto &[target_terms, var_map] = hom;
						// Record only those homomorphisms where the target is at
						// least as big as the source for there is no point in
						// replacing a group of terms with a rule utilizing a bigger
						// group.
						if(target_terms.size() >= rr2.b[0].size()) {
							agg.insert(make_tuple(&rr1, hom));
							// If we were to substitute the target group of terms with
							// a single head, what arguments would we need to pass to
							// it?
							compute_required_vars(rr1, hom, needed_vars);
						}
					}
				}
			}

			// Now we need to figure out if we should create a temporary
			// relation containing body of current rule or whether we can just
			// use it directly. This depends on whether the head exports
			// enough variables.
			elem target_rel;
			vector<elem> target_args;
			set<elem> exported_vars;
			collect_vars(rr2.h[0], exported_vars);
			// Note whether we have created a temporary relation. Important
			// because we make the current rule depend on the temporary
			// relation in this case.
			bool tmp_rel =
				!((exported_vars == needed_vars && count_related_rules(rr2, rp) == 1) ||
					agg.size() == 1);

			if(tmp_rel) {
				// Variables are not exactly what is required. So make relation
				// exporting required variables and note argument order.
				target_rel = elem::fresh_temp_sym(d);
				target_args.assign(needed_vars.begin(), needed_vars.end());
				pending_rules.push_back(raw_rule(raw_term(target_rel, target_args), rr2.b[0]));
			} else {
				// The variables exported by current rule are exactly what is
				// needed by all homomorphisms from current body
				target_rel = rr2.h[0].e[0];
				for(size_t i = 2; i < rr2.h[0].e.size() - 1; i++) {
					target_args.push_back(rr2.h[0].e[i]);
				}
			}

			// Now we go through all the homomorphisms and try to apply
			// substitutions to their targets
			for(auto &[rr1, hom] : agg) {
				// If no temporary relation was created, then don't touch the
				// outer rule as its definition is irreducible.
				if(!tmp_rel && rr1 == &rr2) continue;
				auto &[rts, vs] = hom;
				set<raw_term> rr1_set(rr1->b[0].begin(), rr1->b[0].end());
				// If the target rule still includes the homomorphism target,
				// then ... . Note that this may not be the case as the targets
				// of several homomorphisms could overlap.
				if(includes(rr1_set.begin(), rr1_set.end(), rts.begin(),
						rts.end())) {
					// Remove the homomorphism target from the target rule
					auto it = set_difference(rr1_set.begin(), rr1_set.end(),
						rts.begin(), rts.end(), rr1->b[0].begin());
					rr1->b[0].resize(it - rr1->b[0].begin());
					// And place our chosen head with localized arguments.
					vector<elem> subbed_args;
					for(const elem &e : target_args) {
						// If the current parameter of the outer rule is a constant,
						// then just place it in our new term verbatim
						subbed_args.push_back(at_default(vs, e, e));
					}
					rr1->b[0].push_back(raw_term(target_rel, subbed_args));
				}
			}
		}
	}
	// Now add the pending rules. Done here to prevent movement of rules
	// during potential vector resizing.
	for(const raw_rule &rr : pending_rules) {
		rp.r.push_back(rr);
		o::dbg() << "New Factor Created: " << rr << endl;
	}
}

/* Function to iterate through the partitions of the given set. Calls
 * the supplied function with a vector of sets representing each
 * partition. If the supplied function returns false, then the iteration
 * stops. */

template<typename T, typename F> bool partition_iter(set<T> &vars,
		vector<set<T>> &partition, const F &f) {
	if(vars.empty()) {
		return f(partition);
	} else {
		const T nvar = *vars.begin();
		vars.erase(nvar);
		for(size_t i = 0; i < partition.size(); i++) {
			partition[i].insert(nvar);
			if(!partition_iter(vars, partition, f)) {
				return false;
			}
			partition[i].erase(nvar);
		}
		set<T> npart = { nvar };
		partition.push_back(npart);
		if(!partition_iter(vars, partition, f)) {
			return false;
		}
		partition.pop_back();
		vars.insert(nvar);
		return true;
	}
}

/* Function to iterate through the given set raised to the given
 * cartesian power. The supplied function is called with each tuple in
 * the product and if it returns false, the iteration stops. */

template<typename T, typename F>
		bool product_iter(const set<T> &vars, vector<T> &seq,
			size_t len, const F &f) {
	if(len == 0) {
		return f(seq);
	} else {
		for(const T &el : vars) {
			seq.push_back(el);
			if(!product_iter(vars, seq, len - 1, f)) {
				return false;
			}
			seq.pop_back();
		}
		return true;
	}
}

/* Function to iterate through the power set of the given set. The
 * supplied function is called with each element of the power set and
 * if it returns false, the iteration stops. */

template<typename T, typename F> bool power_iter(set<T> &elts,
		set<T> &subset, const F &f) {
	if(elts.size() == 0) {
		return f(subset);
	} else {
		const T nelt = *elts.begin();
		elts.erase(nelt);
		// Case where current element will not be in subset
		if(!power_iter(elts, subset, f)) {
			return false;
		}
		if(subset.insert(nelt).second) {
			// Case where current element will be in subset
			if(!power_iter(elts, subset, f)) {
				return false;
			}
			subset.erase(nelt);
		}
		elts.insert(nelt);
		return true;
	}
}

/* Collect the variables used in the given terms and return. */

void collect_vars(const raw_term &rt, set<elem> &vars) {
	for(const elem &e : rt.e) {
		if(e.type == elem::VAR) {
			vars.insert(e);
		}
	}
}

/* Collect the variables used in the given terms and return. */

template <class InputIterator>
		void collect_vars(InputIterator first, InputIterator last,
			set<elem> &vars) {
	for(; first != last; first++) {
		collect_vars(*first, vars);
	}
}

/* Collect the variables used in the head and the positive terms of the
 * given rule and return. */

void collect_vars(const raw_rule &rr, set<elem> &vars) {
	collect_vars(rr.h[0], vars);
	for(const raw_term &tm : rr.b[0]) {
		collect_vars(tm, vars);
	}
}

/* If rr1 and rr2 are both conjunctive queries with negation, check that
 * rr1 is contained by rr2. Do this using the Levy-Sagiv test. */

bool driver::cqnc(const raw_rule &rr1, const raw_rule &rr2) {
	// Check that rules have correct format
	if(!(is_cqn(rr1) && is_cqn(rr2) &&
		get_relation_info(rr1.h[0]) == get_relation_info(rr2.h[0]))) return false;
	
	o::dbg() << "CQNC Testing if " << rr1 << " <= " << rr2 << endl;
	
	// Get dictionary for generating fresh symbols
	dict_t &old_dict = tbl->get_dict();
	
	set<elem> vars;
	collect_vars(rr1, vars);
	vector<set<elem>> partition;
	
	// Do the Levy-Sagiv test
	bool contained = partition_iter(vars, partition,
		[&](const vector<set<elem>> &partition) -> bool {
			// Print the current partition
			o::dbg() << "Testing partition: ";
			for(const set<elem> &s : partition) {
				o::dbg() << "{";
				for(const elem &e : s) {
					o::dbg() << e << ", ";
				}
				o::dbg() << "}, ";
			}
			o::dbg() << endl;
			
			// Create new dictionary so that symbols created for these tests
			// do not affect final program
			dict_t d;
			d.op = old_dict.op;
			d.cl = old_dict.cl;

			// Map each variable to a fresh symbol according to the partition
			map<elem, elem> subs;
			for(const set<elem> &part : partition) {
				elem pvar = elem::fresh_sym(d);
				for(const elem &e : part) {
					subs[e] = pvar;
				}
			}
			raw_rule subbed = freeze_rule(rr1, subs, d);
			set<raw_term> canonical, canonical_negative;
			// Separate the positive and negative subgoals. Note the symbols
			// supplied to the subgoals.
			for(raw_term &rt : subbed.b[0]) {
				if(rt.neg) {
					rt.neg = false;
					canonical_negative.insert(rt);
					rt.neg = true;
				} else {
					canonical.insert(rt);
				}
			}
			// Print the canonical database
			o::dbg() << "Current canonical Database: ";
			for(const raw_term &rt : canonical) {
				o::dbg() << rt << ", ";
			}
			o::dbg() << endl;
			// Does canonical database make all the subgoals of subbed true?
			for(raw_term &rt : subbed.b[0]) {
				if(rt.neg) {
					// If the term in the rule is negated, we need to make sure
					// that it is not in the canonical database.
					rt.neg = false;
					if(canonical.find(rt) != canonical.end()) {
						o::dbg() << "Current canonical database causes its source query to be inconsistent."
							<< endl;
						return true;
					}
					rt.neg = true;
				}
			}
			// Collect the symbols/literals from the freeze map
			set<elem> symbol_set;
			for(const auto &[elm, sym] : subs) {
				symbol_set.insert(sym);
				// Finer control over elements in the universe is required to
				// make this algorithm work with unsafe negations. In
				// particular, we need need to control over which characters and
				// numbers are in the domain.
				if(sym.type == elem::SYM) {
					d.get_sym(sym.e);
				}
			}
			// Get all the relations used in both queries
			set<rel_info> rels;
			for(const raw_term &rt : rr1.b[0]) {
				rels.insert(get_relation_info(rt));
			}
			for(const raw_term &rt : rr2.b[0]) {
				rels.insert(get_relation_info(rt));
			}
			// Now we need to get the largest superset of our canonical
			// database
			set<raw_term> superset;
			for(const rel_info &ri : rels) {
				vector<elem> tuple;
				product_iter(symbol_set, tuple, get<1>(ri),
					[&](const vector<elem> tuple) -> bool {
						vector<elem> nterm_e = { get<0>(ri), elem_openp };
						for(const elem &e : tuple) {
							nterm_e.push_back(e);
						}
						nterm_e.push_back(elem_closep);
						raw_term nterm(nterm_e);
						superset.insert(nterm);
						return true;
					});
			}
			// Remove the frozen negative subgoals
			for(const raw_term &rt : canonical_negative) {
				superset.erase(rt);
			}
			// Now need to through all the supersets of our canonical database
			// and check that they yield the frozen head.
			return power_iter(superset, canonical,
				[&](const set<raw_term> ext) -> bool {
					raw_prog test_prog;
					test_prog.r.push_back(rr2);
					set<raw_term> res;
					tables::run_prog(ext, test_prog, d, opts, ir, res);
					return res.find(subbed.h[0]) != res.end();
				});
		});

	if(contained) {
		o::dbg() << "True: " << rr1 << " <= " << rr2 << endl;
		return true;
	} else {
		o::dbg() << "False: " << rr1 << " <= " << rr2 << endl;
		return false;
	}
}

/* If the given query is conjunctive, go through its terms and see if
 * removing one of them can produce a query that f determines to be
 * equivalent. If this is the case, modify the input query and indicate
 * that this has happened through the return flag. */

template<typename F> bool driver::try_minimize(raw_rule &rr, const F &f) {
	if(is_cqn(rr)) {
		vector<raw_term> heads1 = rr.h, bodie1 = rr.b[0],
			heads2 = rr.h, bodie2 = rr.b[0];
		// Let's see if we can remove a body term from the rule without
		// affecting its behavior
		for(size_t i = 0; i < bodie1.size(); i++) {
			// bodie2 is currently equal to bodie1
			bodie2.erase(bodie2.begin() + i);
			// bodie2 missing element i, meaning that rule 2 contains rule 1
			// Construct our candidate replacement rule
			raw_rule rr2(heads2, bodie2);
			if(f(rr2, rr)) {
				// successful if condition implies rule 1 contains rule 2, hence
				// rule 1 = rule 2
				rr = rr2;
				return true;
			}
			bodie2.insert(bodie2.begin() + i, bodie1[i]);
			// bodie2 is currently equal to bodie1
		}
	}
	return false;
}

/* Go through the program and removed those queries that the function f
 * determines to be subsumed by others. While we're at it, minimize
 * (i.e. subsume a query with its part) the shortlisted queries to
 * reduce time cost of future subsumptions. This function does not
 * respect order, so it should only be used on an unordered stratum. */

template<typename F>
		void driver::subsume_queries(raw_prog &rp, const F &f) {
	vector<raw_rule> reduced_rules;
	for(raw_rule &rr : rp.r) {
		bool subsumed = false;
		
		for(auto nrr = reduced_rules.begin(); nrr != reduced_rules.end();) {
			if(f(rr, *nrr)) {
				// If the current rule is contained by a rule in reduced rules,
				// then move onto the next rule in the outer loop
				subsumed = true;
				break;
			} else if(f(*nrr, rr)) {
				// If current rule contains that in reduced rules, then remove
				// the subsumed rule from reduced rules
				nrr = reduced_rules.erase(nrr);
			} else {
				// Neither rule contains the other. Move on.
				nrr++;
			}
		}
		if(!subsumed) {
			// Do the maximal amount of query minimization on the query we are
			// about to admit. This should reduce the time cost of future
			// subsumptions.
			while(try_minimize(rr, f));
			// If the current rule has not been subsumed, then it needs to be
			// represented in the reduced rules.
			reduced_rules.push_back(rr);
		}
	}
	rp.r = reduced_rules;
}

#ifdef WITH_Z3

/* Check query containment for rules of the given program using theorem prover Z3
  and remove subsumed rules. */

void driver::qc_z3 (raw_prog &raw_p, const raw_term &false_term) {
	z3_context ctx;
	// Sort rules by relation name and then by tml arity
	auto sort_rp = [](const raw_rule& r1, const raw_rule& r2) {
		if(r1.h[0].e[0] == r2.h[0].e[0])
			return r1.h[0].arity < r2.h[0].arity;
		else return r1.h[0].e[0] < r2.h[0].e[0];
	};
	sort(raw_p.r.begin(), raw_p.r.end(), sort_rp);
	// Lambda for checking comparability of rules
	auto same_cat = [](const raw_rule& r1, const raw_rule& r2) {
	return r1.h[0].e[0] == r2.h[0].e[0] &&
		r1.h[0].arity == r2.h[0].arity;
	};
	// Check query containment in comparable rules
	for (auto selected = raw_p.r.begin(); selected != raw_p.r.end();) {
		for (auto compared = selected + 1; compared != raw_p.r.end();) {
			// Advance selected iterator such that rules are comparable
			bool isEndReached = false;
			while(!isEndReached &&
					!same_cat(*selected, *compared)) {
				selected = compared;
				compared = selected + 1;
				isEndReached = compared == raw_p.r.end();
			} if (isEndReached) break;
			// Check rules for containment
			if (check_qc_z3(*selected, *compared, false_term, ctx)) {
				selected = raw_p.r.erase(selected);
				continue;
			} else if(check_qc_z3(*compared, *selected, false_term, ctx))
				compared = raw_p.r.erase(compared);
			else ++compared;
		}
		++selected;
	}
}

/* Initialize an empty context that can then be populated with TML to Z3
 * conversions. uninterp_sort will be used for all Z3 relation arguments
 * and bool_sort is the "return" type of all relations. */

z3_context::z3_context() : solver(context),
		uninterp_sort(context.uninterpreted_sort("Type")),
		bool_sort(context.bool_sort()), head_rename(context) {
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
			domain.push_back(uninterp_sort);
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
	else {
		const z3::expr &ndecl =
			context.constant(el.to_str().c_str(), uninterp_sort);
		var_to_decl.emplace(make_pair(el, ndecl));
		return ndecl;
	}
}

/* Construct a formula that constrains the head variables. The
 * constraints are of two sorts: the first equate pairwise identical
 * head variables to each other, and the second equate literals to their
 * unique Z3 equivalent. Also exports a mapping of each head element to
 * the Z3 head variable it has been assigned to. */

z3::expr z3_context::z3_head_constraints(const raw_term &head,
		map<elem, z3::expr> &body_rename) {
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
			// Pushing head variables
			vars_of_rel.push_back(arg_to_z3(*el));
		}
		return rel_to_z3(rel)(vars_of_rel);
	} else if(rel.extype == raw_term::EQ) {
		return arg_to_z3(rel.e[0]) == arg_to_z3(rel.e[2]);
	} else assert(false); //should never reach here
}

/* Make a fresh Z3 constant. */

z3::expr z3_context::fresh_constant() {
	return z3::expr(context,
		Z3_mk_fresh_const(context, nullptr, uninterp_sort));
}

/* Given a formula tree, output the equivalent Z3 expression using and
 * updating the mappings in the context as necessary. */

z3::expr z3_context::tree_to_z3(const sprawformtree &t,
		const raw_term &false_term, dict_t &dict) {
	switch(t->type) {
		case elem::AND:
			return tree_to_z3(t->l, false_term, dict) &&
				tree_to_z3(t->r, false_term, dict);
		case elem::ALT:
			return tree_to_z3(t->l, false_term, dict) ||
				tree_to_z3(t->r, false_term, dict);
		case elem::NOT:
			return !tree_to_z3(t->l, false_term, dict);
		case elem::EXISTS: {
			const elem &qvar = *t->l->el;
			// Obtain original Z3 binding this quantified variable
			z3::expr normal_const = arg_to_z3(qvar);
			// Use a fresh Z3 binding for this quantified variable
			z3::expr &temp_const = var_to_decl.at(qvar) = fresh_constant();
			// Make quantified expression
			z3::expr qexpr = exists(temp_const,
				tree_to_z3(t->r, false_term, dict));
			// Restore original binding for quantified variable
			var_to_decl.at(qvar) = normal_const;
			return qexpr;
		} case elem::FORALL: {
			const elem &qvar = *t->l->el;
			// Obtain original Z3 binding this quantified variable
			z3::expr normal_const = arg_to_z3(qvar);
			// Use a fresh Z3 binding for this quantified variable
			z3::expr &temp_const = var_to_decl.at(qvar) = fresh_constant();
			// Make quantified expression
			z3::expr qexpr = forall(temp_const,
				tree_to_z3(t->r, false_term, dict));
			// Restore original binding for quantified variable
			var_to_decl.at(qvar) = normal_const;
			return qexpr;
		} case elem::IMPLIES: case elem::COIMPLIES: case elem::UNIQUE:
			// Process the expanded formula instead
			return tree_to_z3(expand_formula_node(t, dict), false_term, dict);
		case elem::NONE:
			if(*t == false_term) return context.bool_val(false);
			else return term_to_z3(*t->rt);
		default:
			assert(false); //should never reach here
	}
}

/* Given a rule, output the body of this rule converted to the
 * corresponding Z3 expression. Caches the conversion in the context in
 * case the same rule is needed in future. */

z3::expr z3_context::rule_to_z3(const raw_rule &rr,
		const raw_term &false_term, dict_t &dict) {
	if(auto decl = rule_to_decl.find(rr); decl != rule_to_decl.end())
		return decl->second;
	// create map from bound_vars
	map<elem, z3::expr> body_rename;
	z3::expr restr = z3_head_constraints(rr.h[0], body_rename);
	// Collect bound variables of rule and restrictions from constants in head
	set<elem> free_vars;
	vector<elem> bound_vars(rr.h[0].e.begin() + 2, rr.h[0].e.end() - 1);
	collect_free_vars(rr.get_prft(false_term), bound_vars, free_vars);
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
	// Construct z3 expression from rule
	z3::expr formula = tree_to_z3(rr.get_prft(false_term), false_term, dict);
	// Now undo the global head mapping for future constructions
	for(auto &[el, constant] : var_backup) var_to_decl.at(el) = constant;
	z3::expr decl = restr && (ex_quant_vars.empty() ?
		formula : z3::exists(ex_quant_vars, formula));
	rule_to_decl.emplace(make_pair(rr, decl));
	return decl;
}

/* Checks if r1 is contained in r2 or vice versa.
 * Returns false if rules are not comparable or not contained.
 * Returns true if r1 is contained in r2. */

bool driver::check_qc_z3(const raw_rule &r1, const raw_rule &r2,
		const raw_term &false_term, z3_context &ctx) {
	if (!(is_query(r1, false_term) && is_query(r2, false_term)))
		return false;
	// Check if rules are comparable
	if (! (r1.h[0].e[0] == r2.h[0].e[0] &&
	    	r1.h[0].arity == r2.h[0].arity)) return 0;
	// Get head variables for z3
	z3::expr_vector bound_vars(ctx.context);
	for (uint_t i = 0; i != r1.h[0].e.size() - 3; ++i)
		bound_vars.push_back(ctx.globalHead_to_z3(i));
	// Rename head variables on the fly such that they match
	// on both rules
	dict_t &dict = tbl->get_dict();
	z3::expr rule1 = ctx.rule_to_z3(r1, false_term, dict);
	z3::expr rule2 = ctx.rule_to_z3(r2, false_term, dict);
	ctx.solver.push();
	// Add r1 => r2 to solver
	if (bound_vars.empty()) ctx.solver.add(!z3::implies(rule1, rule2));
	else ctx.solver.add(!z3::forall(bound_vars,z3::implies(rule1, rule2)));
	bool res = ctx.solver.check() == z3::unsat;
	ctx.solver.pop();
	return res;
}

#endif

void driver::simplify_formulas(raw_prog &rp, const raw_term &false_term) {
	for(raw_rule &rr : rp.r) {
		if(rr.is_form()) {
			rr.set_prft(raw_form_tree::simplify(rr.prft, false_term));
		}
	}
}

/* Make relations mapping list ID's to their heads and tails. Domain's
 * first argument is the relation into which it should put the domain it
 * creates, its second argument is the domain size of of its tuple
 * elements, and its third argument is the maximum tuple length. */

bool driver::transform_domains(raw_prog &rp, const directive& drt) {
	o::dbg() << "Generating domain for: " << drt << endl;
	dict_t &d = tbl->get_dict();
	// Ensure that we're working on a DOMAIN directive
	if(drt.type != directive::EDOMAIN) return false;
	// The relation to contain the evaled relation is the first symbol
	// between the parentheses
	elem out_rel = drt.domain_sym;
	// This transformation will automatically generate non-negative
	// numbers up to this limit for inclusion in domain
	int_t gen_limit = drt.limit_num.num;
	// The maximum arity of the desired domain is the first symbol
	// between the inner parentheses
	int_t max_arity = drt.arity_num.num;
	// The number of distinct lists of elements less than gen_limit and
	// with length less than max_limit
	int_t max_id = gen_limit == 1 ? max_arity + 1 :
		(pow(gen_limit, max_arity + 1) - 1) / (gen_limit - 1);
	
	// Initialize the symbols, variables, and operators used in the
	// domain creation rule
	elem lt_elem(elem::LT, d.get_lexeme("<")),
		leq_elem(elem::LEQ, d.get_lexeme("<=")),
		plus_elem(elem::ARITH, t_arith_op::ADD, d.get_lexeme("+")),
		equals_elem(elem::EQ, d.get_lexeme("=")),
		list_id = elem::fresh_var(d), list_fst = elem::fresh_var(d),
		list_rst = elem::fresh_var(d), pred_id = elem::fresh_var(d),
		divisor_x_quotient = gen_limit == 1 ? list_rst : elem::fresh_var(d);

	// Make two relations for manipulating domains, the fst relation
	// relates a list ID to its head, and the rst relation relates a
	// list ID to its tail.
	raw_term fst_head({concat(out_rel, "_fst"), elem_openp, list_id,
		list_fst, elem_closep});
	raw_term rst_head({concat(out_rel, "_rst"), elem_openp, list_id,
		list_rst, elem_closep});

	// The body of the fst and rst rules. Since lists are encoded by
	// multiplying each element by the exponent of some base.
	// Euclidean division is required to extract list elements from a
	// given ID.
	vector<raw_term> bodie = {
		// 0 < list_id
		raw_term(raw_term::LEQ, {list_id, leq_elem, elem(0)}).negate(),
		// list_id < max_id
		raw_term(raw_term::LEQ, {elem(max_id), leq_elem, list_id}).negate(),
		// 0 <= list_fst
		raw_term(raw_term::LEQ, {elem(0), leq_elem, list_fst}),
		// list_fst < gen_limit
		raw_term(raw_term::LEQ, {elem(gen_limit), leq_elem, list_fst}).negate(),
		// 0 <= list_rst
		raw_term(raw_term::LEQ, {elem(0), leq_elem, list_rst}),
		// list_rst < list_id
		raw_term(raw_term::LEQ, {list_id, leq_elem, list_rst}).negate(),
		// pred_id + 1 = list_id
		raw_term(raw_term::ARITH, t_arith_op::ADD, {pred_id, plus_elem,
			elem(1), equals_elem, list_id}),
		// divisor_x_quotient + list_fst = pred_id
		raw_term(raw_term::ARITH, t_arith_op::ADD, {divisor_x_quotient,
			plus_elem, list_fst, equals_elem, pred_id})
		};
	// Multiplication seems to cause the solver to hang. Since the
	// divisor is the value of gen_limit, we can express divisor *
	// quotient by repeated addition, or for smaller BDDs, by repeated
	// doubling.
	elem quotient_elem = divisor_x_quotient;
	for(int_t quotient = gen_limit; quotient > 1;) {
		// If current quotient is odd, then it will need to be expressed
		// by doubling something and adding the divisor to it
		if(quotient % 2 == 1) {
			elem new_quotient_elem = elem::fresh_var(d);
			// new_quotient_elem + list_rst = quotient_elem
			bodie.push_back(raw_term(raw_term::ARITH, t_arith_op::ADD,
				{new_quotient_elem, plus_elem, list_rst, equals_elem, quotient_elem}));
			quotient_elem = new_quotient_elem;
			quotient --;
		}
		// If current quotient is more than or equal to 2, then it can
		// be expressed by doubling something
		if(quotient / 2 > 0) {
			elem new_quotient_elem =
				quotient / 2 == 1 ? list_rst : elem::fresh_var(d);
			// new_quotient_elem + new_quotient_elem = quotient_elem
			bodie.push_back(raw_term(raw_term::ARITH, t_arith_op::ADD,
				{new_quotient_elem, plus_elem, new_quotient_elem, equals_elem,
					quotient_elem}));
			quotient_elem = new_quotient_elem;
			quotient /= 2;
		}
	}
	// Finally create the domain rules
	rp.r.push_back(raw_rule({fst_head, rst_head}, bodie));
	// Also make the nil list
	rp.r.push_back(raw_rule(raw_term(
		{ concat(out_rel, "_nil"), elem_openp, elem(0), elem_closep })));
	// To prevent spurious (i.e. purely modular) solutions to the
	// modular equation defining lists, we should artificially
	// increase the modulus to a number which the arithmetic
	// operations cannot reach (due to their bounds).
	rp.r.push_back(raw_rule(raw_term(
		{ concat(out_rel, "_mod"), elem_openp, elem(gen_limit * max_id),
			elem_closep })));

	// Lists are sometimes used to encode interpreter memory. In this
	// scenario, it is useful to treat the longest lists as possible
	// memory states
	elem current_list = elem::fresh_var(d), next_list = elem::fresh_var(d);
	// The relation that will contain all the longest lists
	raw_term max_head({ concat(out_rel, "_max"),
		elem_openp, current_list, elem_closep });
	// The body essentially ensures that the given list has the given
	// number of nodes. Note that node values are ignored here.
	vector<raw_term> max_body;
	for(int_t i = 0; i < max_arity; i++) {
		max_body.push_back(raw_term({ concat(out_rel, "_rst"),
			elem_openp, current_list, next_list, elem_closep }));
		current_list = next_list;
		next_list = elem::fresh_var(d);
	}
	// Not strictly necessary. Makes sure that the list end occurs
	// after the arity_max nodes.
	max_body.push_back(raw_term({ concat(out_rel, "_nil"),
		elem_openp, current_list, elem_closep }));
	// Create the longest list rule.
	rp.r.push_back(raw_rule(max_head, max_body));
	// Successfully executed directive
	o::dbg() << "Generated domain for: " << drt << endl;
	return true;
}

/* In the case that the argument is a variable, get the symbol
 * associated with it and return that. If there is no such association,
 * make one. */

elem driver::quote_elem(const elem &e, map<elem, elem> &variables,
		dict_t &d) {
	if(variables.find(e) != variables.end()) {
		return variables[e];
	} else {
		// Since the current variable lacks a designated substitute,
		// make one and record the mapping.
		return variables[e] = (e.type == elem::VAR ? elem::fresh_sym(d) : e);
	}
}

/* In the case that the argument is a variable, get the symbol
 * associated with it and return that. If there is no such association,
 * make one such that it uses the lowest 0-based index. */

elem driver::numeric_quote_elem(const elem &e,
		map<elem, elem> &variables) {
	if(variables.find(e) != variables.end()) {
		return variables[e];
	} else {
		// Since the current variable lacks a designated substitute,
		// make one and record the mapping.
		return variables[e] = (e.type == elem::VAR ? elem(int_t(variables.size())) : e);
	}
}

/* Iterate through terms and associate each unique variable with unique
 * fresh symbol. */

raw_rule driver::freeze_rule(raw_rule rr,
		map<elem, elem> &freeze_map, dict_t &d) {
	for(raw_term &tm : rr.h) {
		if(tm.extype == raw_term::REL) {
			for(size_t i = 2; i < tm.e.size() - 1; i++) {
				tm.e[i] = quote_elem(tm.e[i], freeze_map, d);
			}
		}
	}
	for(vector<raw_term> &bodie : rr.b) {
		for(raw_term &tm : bodie) {
			if(tm.extype == raw_term::REL) {
				for(size_t i = 2; i < tm.e.size() - 1; i++) {
					tm.e[i] = quote_elem(tm.e[i], freeze_map, d);
				}
			}
		}
	}
	return rr;
}

/* Takes a raw term and returns its quotation within a relation of the
 * given name. The names of variable elements within the raw term are
 * added to the variables map. */

elem driver::quote_term(const raw_term &head, const elem &rel_name,
		const elem &domain_name, raw_prog &rp, map<elem, elem> &variables,
		int_t &part_count) {
	// Get dictionary for generating fresh symbols
	dict_t &d = tbl->get_dict();
	elem term_id(part_count++);
	if(head.extype == raw_term::REL) {
		elem elems_id = elem::fresh_var(d), tags_id = elem::fresh_var(d),
			elems_hid = elems_id, tags_hid = tags_id;
		vector<raw_term> params_body, param_types_body;
		for(size_t param_idx = 2; param_idx < head.e.size() - 1; param_idx ++) {
			elem next_elems_id = elem::fresh_var(d),
				next_tags_id = elem::fresh_var(d);
			params_body.push_back(raw_term({concat(domain_name, "_fst"), elem_openp,
				elems_id, numeric_quote_elem(head.e[param_idx], variables),
				elem_closep}));
			params_body.push_back(raw_term({concat(domain_name, "_rst"), elem_openp,
				elems_id, next_elems_id, elem_closep}));
			param_types_body.push_back(raw_term({concat(domain_name, "_fst"), elem_openp,
				tags_id, elem(int_t(head.e[param_idx].type == elem::VAR)), elem_closep}));
			param_types_body.push_back(raw_term({concat(domain_name, "_rst"), elem_openp,
				tags_id, next_tags_id, elem_closep}));
			elems_id = next_elems_id;
			tags_id = next_tags_id;
		}
		params_body.push_back(raw_term({concat(domain_name, "_nil"), elem_openp,
			elems_id, elem_closep}));
		param_types_body.push_back(raw_term({concat(domain_name, "_nil"), elem_openp,
			tags_id, elem_closep}));
		// Add metadata to quoted term: term signature, term id, term name
		rp.r.push_back(raw_rule(raw_term({concat(rel_name, "_type"), elem_openp,
			term_id, elem(QTERM), elem_closep })));
		rp.r.push_back(raw_rule(raw_term({concat(rel_name, "_term_relation"),
			elem_openp, term_id, head.e[0], elem_closep })));
		rp.r.push_back(raw_rule(raw_term({concat(rel_name, "_term_params"),
			elem_openp, term_id, elems_hid, elem_closep }), params_body));
		rp.r.push_back(raw_rule(raw_term({concat(rel_name, "_term_param_types"),
			elem_openp, term_id, tags_hid, elem_closep }), param_types_body));
	} else if(head.extype == raw_term::EQ) {
		// Add metadata to quoted term: term signature, term id, term name
		vector<elem> quoted_term_e = {rel_name, elem_openp, elem(QEQUALS),
			term_id, numeric_quote_elem(head.e[0], variables),
			numeric_quote_elem(head.e[2], variables),
			int_t(head.e[0].type == elem::VAR), int_t(head.e[2].type == elem::VAR),
			elem_closep };
		rp.r.push_back(raw_rule(raw_term(quoted_term_e)));
	}
	if(head.neg) {
		// If this term is actually negated, then we'll make a parent for
		// this node and return its id
		elem neg_id(part_count++);
		rp.r.push_back(raw_rule(raw_term({concat(rel_name, "_type"), elem_openp,
			neg_id, elem(QNOT), elem_closep})));
		rp.r.push_back(raw_rule(raw_term({concat(rel_name, "_not_body"), elem_openp,
			neg_id, term_id, elem_closep})));
		return neg_id;
	} else {
		return term_id;
	}
}

/* Recursively quotes the given formula. Say that the output relation
 * name is q, quote_formula will populate it according to the following
 * schema:
 * <quote>_type(<node ID> <node type>).
 *
 * For <node type> = RULE
 * 	<quote>_rule_head(<node ID> <head ID>).
 * 	<quote>_rule_body(<node ID> <body ID>).
 * For <node type> = TERM
 * 	<quote>_term_relation(<node ID> <term relation>).
 * 	<quote>_term_params(<node ID> <term parameter list>).
 * 	<quote>_term_param_types(<node ID> <term param type list>).
 * For <node type> = AND
 * 	<quote>_and_left(<node ID> <left node ID>).
 * 	<quote>_and_right(<node ID> <right node ID>).
 * For <node type> = ALT
 * 	<quote>_alt_left(<node ID> <left node ID>).
 * 	<quote>_alt_right(<node ID> <right node ID>).
 * For <node type> = NOT
 * 	<quote>_not_body(<node ID> <body node ID>).
 * For <node type> = FORALL
 * 	<quote>_forall_var(<node ID> <variable ID>).
 * 	<quote>_forall_body(<node ID> <body node ID>).
 * For <node type> = EXISTS
 * 	<quote>_exists_var(<node ID> <variable ID>).
 * 	<quote>_exists_body(<node ID> <body node ID>).
 * For <node type> = FACT
 *  <quote>_fact_term(<node ID> <term ID>).
 */

elem driver::quote_formula(const sprawformtree &t, const elem &rel_name,
		const elem &domain_name, raw_prog &rp, map<elem, elem> &variables,
		int_t &part_count) {
	// Get dictionary for generating fresh symbols
	dict_t &d = tbl->get_dict();
	const elem part_id = elem(part_count++);
	switch(t->type) {
		case elem::IMPLIES:
			rp.r.push_back(raw_rule(raw_term({concat(rel_name, "_type"),
				elem_openp, part_id, elem(QIMPLIES), elem_closep })));
			rp.r.push_back(raw_rule(raw_term({concat(rel_name, "_implies_left"),
				elem_openp, part_id,
				quote_formula(t->l, rel_name, domain_name, rp, variables, part_count),
				elem_closep })));
			rp.r.push_back(raw_rule(raw_term({concat(rel_name, "_implies_right"),
				elem_openp, part_id,
				quote_formula(t->r, rel_name, domain_name, rp, variables, part_count),
				elem_closep })));
			break;
		case elem::COIMPLIES:
			rp.r.push_back(raw_rule(raw_term({concat(rel_name, "_type"),
				elem_openp, part_id, elem(QCOIMPLIES), elem_closep })));
			rp.r.push_back(raw_rule(raw_term({concat(rel_name, "_coimplies_left"),
				elem_openp, part_id,
				quote_formula(t->l, rel_name, domain_name, rp, variables, part_count),
				elem_closep })));
			rp.r.push_back(raw_rule(raw_term({concat(rel_name, "_coimplies_right"),
				elem_openp, part_id,
				quote_formula(t->r, rel_name, domain_name, rp, variables, part_count),
				elem_closep })));
			break;
		case elem::AND:
			rp.r.push_back(raw_rule(raw_term({concat(rel_name, "_type"),
				elem_openp, part_id, elem(QAND), elem_closep })));
			rp.r.push_back(raw_rule(raw_term({concat(rel_name, "_and_left"),
				elem_openp, part_id,
				quote_formula(t->l, rel_name, domain_name, rp, variables, part_count),
				elem_closep })));
			rp.r.push_back(raw_rule(raw_term({concat(rel_name, "_and_right"),
				elem_openp, part_id,
				quote_formula(t->r, rel_name, domain_name, rp, variables, part_count),
				elem_closep })));
			break;
		case elem::ALT:
			rp.r.push_back(raw_rule(raw_term({concat(rel_name, "_type"),
				elem_openp, part_id, elem(QALT), elem_closep })));
			rp.r.push_back(raw_rule(raw_term({concat(rel_name, "_alt_left"),
				elem_openp, part_id,
				quote_formula(t->l, rel_name, domain_name, rp, variables, part_count),
				elem_closep })));
			rp.r.push_back(raw_rule(raw_term({concat(rel_name, "_alt_right"),
				elem_openp, part_id,
				quote_formula(t->r, rel_name, domain_name, rp, variables, part_count),
				elem_closep })));
			break;
		case elem::NOT:
			rp.r.push_back(raw_rule(raw_term({concat(rel_name, "_type"),
				elem_openp, part_id, elem(QNOT), elem_closep })));
			rp.r.push_back(raw_rule(raw_term({concat(rel_name, "_not_body"),
				elem_openp, part_id,
				quote_formula(t->l, rel_name, domain_name, rp, variables, part_count),
				elem_closep })));
			break;
		case elem::EXISTS: {
			elem qvar = quote_elem(*(t->l->el), variables, d);
			rp.r.push_back(raw_rule(raw_term({concat(rel_name, "_type"),
				elem_openp, part_id, elem(QEXISTS), elem_closep })));
			rp.r.push_back(raw_rule(raw_term({concat(rel_name, "_exists_var"),
				elem_openp, part_id, qvar, elem_closep })));
			rp.r.push_back(raw_rule(raw_term({concat(rel_name, "_exists_body"),
				elem_openp, part_id,
				quote_formula(t->r, rel_name, domain_name, rp, variables, part_count),
				elem_closep })));
			break;
		} case elem::UNIQUE: {
			elem qvar = quote_elem(*(t->l->el), variables, d);
			rp.r.push_back(raw_rule(raw_term({concat(rel_name, "_type"),
				elem_openp, part_id, elem(QUNIQUE), elem_closep })));
			rp.r.push_back(raw_rule(raw_term({concat(rel_name, "_unique_var"),
				elem_openp, part_id, qvar, elem_closep })));
			rp.r.push_back(raw_rule(raw_term({concat(rel_name, "_unique_body"),
				elem_openp, part_id,
				quote_formula(t->r, rel_name, domain_name, rp, variables, part_count),
				elem_closep })));
			break;
		} case elem::NONE: {
			return quote_term(*t->rt, rel_name, domain_name, rp, variables, part_count);
			break;
		} case elem::FORALL: {
			elem qvar = quote_elem(*(t->l->el), variables, d);
			rp.r.push_back(raw_rule(raw_term({concat(rel_name, "_type"),
				elem_openp, part_id, elem(QFORALL), elem_closep })));
			rp.r.push_back(raw_rule(raw_term({concat(rel_name, "_forall_var"),
				elem_openp, part_id, qvar, elem_closep })));
			rp.r.push_back(raw_rule(raw_term({concat(rel_name, "_forall_body"),
				elem_openp, part_id,
				quote_formula(t->r, rel_name, domain_name, rp, variables, part_count),
				elem_closep })));
			break;
		} default:
			assert(false); //should never reach here
	}
	return part_id;
}

/* Returns a symbol formed by concatenating the given string to the
 * given symbol. Used for refering to sub relations. */

elem driver::concat(const elem &rel, string suffix) {
	// Get dictionary for generating fresh symbols
	dict_t &d = tbl->get_dict();
	// Make lexeme from concatenating rel's lexeme with the given suffix
	return elem(elem::SYM,
		d.get_lexeme(lexeme2str(rel.e) + to_string_t(suffix)));
}

/* Returns a lexeme formed by concatenating the given string to the
 * given lexeme. Used for refering to sub relations. */

lexeme driver::concat(const lexeme &rel, string suffix) {
	// Get dictionary for generating fresh symbols
	dict_t &d = tbl->get_dict();
	// Make lexeme from concatenating rel's lexeme with the given suffix
	return d.get_lexeme(lexeme2str(rel) + to_string_t(suffix));
}

/* Quote the given rule and put its quotation into the given raw_prog
 * under a relation given by rel_name. */

vector<elem> driver::quote_rule(const raw_rule &rr,
		const elem &rel_name, const elem &domain_name, raw_prog &rp,
		int_t &part_count, const raw_term &false_term) {
	// Maintain a list of the variable substitutions:
	map<elem, elem> variables;
	vector<elem> rule_ids;
	
	// Facts and rules have different representations in quotations. This
	// is because they are interpreted differently: facts are placed in
	// the 0th database whilst rules are fired on each iteration.
	if(rr.is_fact()) {
		for(size_t gidx = 0; gidx < rr.h.size(); gidx++) {
			const elem term_id = quote_term(rr.h[gidx], rel_name, domain_name, rp,
				variables, part_count);
			const elem rule_id = elem(part_count++);
			rp.r.push_back(raw_rule(raw_term({concat(rel_name, "_type"), elem_openp,
				rule_id, elem(QFACT), elem_closep })));
			rp.r.push_back(raw_rule(raw_term({concat(rel_name, "_fact_term"), elem_openp,
				rule_id, term_id, elem_closep })));
			rule_ids.push_back(rule_id);
		}
	} else {
		const elem body_id = quote_formula(rr.get_prft(false_term), rel_name, domain_name,
			rp, variables, part_count);
		for(size_t gidx = 0; gidx < rr.h.size(); gidx++) {
			const elem head_id = quote_term(rr.h[gidx], rel_name, domain_name, rp,
				variables, part_count);
			const elem rule_id = elem(part_count++);
			rp.r.push_back(raw_rule(raw_term({concat(rel_name, "_type"), elem_openp,
				rule_id, elem(QRULE), elem_closep })));
			rp.r.push_back(raw_rule(raw_term({concat(rel_name, "_rule_head"), elem_openp,
				rule_id, head_id, elem_closep })));
			rp.r.push_back(raw_rule(raw_term({concat(rel_name, "_rule_body"), elem_openp,
				rule_id, body_id, elem_closep })));
			rule_ids.push_back(rule_id);
		}
	}
	return rule_ids;
}

/* Put the quotation of the given program into a relation of the given
 * name in the given program. */

void driver::quote_prog(const raw_prog nrp, const elem &rel_name,
		const elem &domain_name, raw_prog &rp, const raw_term &false_term) {
	int_t part_count = 0;
	for(size_t ridx = 0; ridx < nrp.r.size(); ridx++) {
		quote_rule(nrp.r[ridx], rel_name, domain_name, rp, part_count,
			false_term);
	}
}

/* Parse an STR elem into a raw_prog. */

raw_prog driver::read_prog(elem prog, const raw_prog &rp) {
	lexeme prog_str = {prog.e[0]+1, prog.e[1]-1};
	input *prog_in = dynii.add_string(lexeme2str(prog_str));
	prog_in->prog_lex();
	raw_prog nrp;
	nrp.builtins = rp.builtins;
	nrp.parse(prog_in, tbl->get_dict());
	const strs_t strs;
	transform(nrp, strs);
	return nrp;
}

/* Make a relation representing the code given in the quotation. Quote's
 * first argument is the relation into which it should put the quotation
 * it creates, and it's second argument is the program to quote. */

bool driver::transform_quotes(raw_prog &rp, const raw_term &false_term,
		const directive &drt) {
	if(drt.type != directive::QUOTE) return false;
	o::dbg() << "Generating quotation for: " << drt << endl;
	// The relation to contain the evaled relation is the first symbol
	// between the parentheses
	elem out_rel = drt.quote_sym;
	// The relation containing the quotation arity is the second symbol
	// between the parentheses
	elem domain_sym = drt.domain_sym;
	// The formal symbol representing the quotation relation is the
	// third symbol between the parentheses
	elem quote_str = drt.quote_str;

	if(quote_str.type == elem::STR && quote_str.e[1] > quote_str.e[0] &&
			*quote_str.e[0] == '`') {
		raw_prog nrp = read_prog(quote_str, rp);
		// Create the quotation relation
		quote_prog(nrp, out_rel, domain_sym, rp, false_term);
	}
	// Indicate success
	o::dbg() << "Generated quotation for: " << drt << endl;
	return true;
}

/* An Imhof-style interpreter can be inconvenient to debug because
 * its output tuples are encoded into numbers using modular arithmetic.
 * This transformation creates codecs for interpreters so that it's
 * easier to inspect and manipulate them.
 *
 * Codec takes four arguments: the name of the relation that will
 * contain the encodings/decodings of interpreter outputs, the formal
 * name of a relation containing the domain of the interpreter, the
 * formal name of the relation containing the interpreter, and the
 * maximum arity of the domain. */

bool driver::transform_codecs(raw_prog &rp, const directive &drt) {
	if(drt.type != directive::CODEC) return false;
	o::dbg() << "Generating codec for: " << drt << endl;
	// The relation to contain the evaled relation is the first symbol
	// between the parentheses
	elem codec_rel = drt.codec_sym;
	// The relation containing the quotation arity is the second symbol
	// between the parentheses
	elem domain_sym = drt.domain_sym;
	// The formal symbol representing the output relation is the
	// third symbol between the parentheses
	elem out_sym = drt.eval_sym;
	// The number representing the maximum arity of relations in the
	// quotation is the fourth symbol between the parentheses
	int_t max_arity = drt.arity_num.num;
	// Get dictionary for generating fresh variables
	dict_t &d = tbl->get_dict();

	// Create the symbols and variables that will feature heavily in
	// the terms to be created below
	elem decode_tmp_rel = concat(codec_rel, "__decode"),
		name_var = elem::fresh_var(d), timestep_var = elem::fresh_var(d),
		next_timestep_var = elem::fresh_var(d), params_var = elem::fresh_var(d);

	// Create the terms that will feature heavily in the rules to be
	// created below
	raw_term tick({ concat(out_sym, "_tick"), elem_openp, elem_closep }),
		tock({ concat(out_sym, "_tock"), elem_openp, elem_closep }),
		fixpoint({ concat(out_sym, "_fixpoint"), elem_openp, timestep_var,
			next_timestep_var, elem_closep }),
		dec_databases({ concat(out_sym, "_databases"), elem_openp,
			timestep_var, name_var, params_var, elem_closep }),
		enc_databases({ concat(out_sym, "_databases"), elem_openp,
			elem(0), name_var, params_var, elem_closep });

	// Make variables for each head and tail in a linked list
	vector<elem> params_vars, param_vars;
	for(int_t i = 0; i < max_arity; i++) {
		params_vars.push_back(elem::fresh_var(d));
		param_vars.push_back(elem::fresh_var(d));
	}

	// Create rules to decode the contents of the interpreter's
	// database into a temporary relation on each tick
	for(int_t i = 0; i <= max_arity; i++) {
		vector<elem> decode_tmp_elems = { decode_tmp_rel,
			elem_openp, name_var };
		for(int_t j = 0; j < i; j++) {
			decode_tmp_elems.push_back(param_vars[j]);
		}
		decode_tmp_elems.push_back(elem_closep);
		raw_term decode_tmp_head(decode_tmp_elems);
		raw_rule decode_tmp_rule(decode_tmp_head, { fixpoint,
			dec_databases, tick });
		// Here we decode the number representing a list into its
		// various heads and tails
		elem current_params_var = params_var;
		for(int_t j = 0; j < i; j++) {
			decode_tmp_rule.b[0].push_back(raw_term(
				{concat(domain_sym, "_fst"), elem_openp, current_params_var,
					param_vars[j], elem_closep}));
			decode_tmp_rule.b[0].push_back(raw_term(
				{concat(domain_sym, "_rst"), elem_openp, current_params_var,
					params_vars[j], elem_closep}));
			current_params_var = params_vars[j];
		}
		decode_tmp_rule.b[0].push_back(raw_term(
			{concat(domain_sym, "_nil"), elem_openp, current_params_var,
				elem_closep}));
		// Add the temporary decoding rule
		rp.r.push_back(decode_tmp_rule);
	}

	// Prepare the rules that will clear the decoder and temporary
	// decoder relations
	raw_rule tick_clear, tock_clear;
	tick_clear.b = {{tick}};
	tock_clear.b = {{tock}};

	// Make a rule to copy the temporary decoder relation into the
	// decoder relation on each tock
	for(int_t i = 0; i <= max_arity; i++) {
		// Make the terms to capture a temporary decoder relation entry
		// and to insert a decoder relation entry
		vector<elem>
			decode_elems = { concat(codec_rel, "_decode"), elem_openp, name_var },
			decode_tmp_elems = { decode_tmp_rel, elem_openp, name_var };
		for(int_t j = 0; j < i; j++) {
			decode_elems.push_back(param_vars[j]);
			decode_tmp_elems.push_back(param_vars[j]);
		}
		decode_elems.push_back(elem_closep);
		decode_tmp_elems.push_back(elem_closep);
		raw_term decode_head(decode_elems),
			decode_tmp_head(decode_tmp_elems);
		// Make the rule to do the copying and add it to the program
		raw_rule decode_rule(decode_head, { decode_tmp_head, tock });
		rp.r.push_back(decode_rule);

		// Build up the rules that will clear the decoder and temporary
		// decoder relations
		tick_clear.h.push_back(decode_head.negate());
		tock_clear.h.push_back(decode_tmp_head.negate());
	}

	// Now add the clearing rules to the final program
	rp.r.push_back(tick_clear);
	rp.r.push_back(tock_clear);

	// Make rules that take decoded terms and add them to the step 0
	// database of the given interpreter on each tock
	for(int_t i = 0; i <= max_arity; i++) {
		// The decoded terms will be coming from a <codec>_encode
		// relation
		vector<elem> encode_elems = { concat(codec_rel, "_encode"),
			elem_openp, name_var };
		for(int_t j = 0; j < i; j++) {
			encode_elems.push_back(param_vars[j]);
		}
		encode_elems.push_back(elem_closep);
		raw_term encode_head(encode_elems);
		// Make and add the rule that will add a decoded term of the
		// given arity into the step 0 database of the interpreter.
		raw_rule encode_rule(enc_databases, { encode_head, tock });
		// Make the group of terms that will compute the encoding of
		// the decoded tuple
		elem current_params_var = params_var;
		for(int_t j = 0; j < i; j++) {
			encode_rule.b[0].push_back(raw_term(
				{concat(domain_sym, "_fst"), elem_openp, current_params_var,
					param_vars[j], elem_closep}));
			encode_rule.b[0].push_back(raw_term(
				{concat(domain_sym, "_rst"), elem_openp, current_params_var,
					params_vars[j], elem_closep}));
			current_params_var = params_vars[j];
		}
		encode_rule.b[0].push_back(raw_term(
			{concat(domain_sym, "_nil"), elem_openp, current_params_var,
				elem_closep}));
		rp.r.push_back(encode_rule);
	}
	// Indicate success
	o::dbg() << "Generated codec for: " << drt << endl;
	return true;
}

/* If eval is used, take its four arguments: the name of the relation
 * that will contain the outputs of the original TML program, the formal
 * name of the relation containing the quoted program's domain, the
 * formal name of the relation containing a representation of a TML
 * program, and the number of steps of the quoted program that should be
 * simulated. Note that the evaled relation will only depend on the
 * relation's program arity and its name - not its entries. Note also
 * that the bulk of this function is autogenerated by calling this
 * interepreter on eval.tml using the flag --program_gen (which in turn
 * is implemented by the generate_cpp function). */

bool driver::transform_evals(raw_prog &rp, const directive &drt) {
	if(drt.type != directive::EVAL) return false;
	o::dbg() << "Generating eval for: " << drt << endl;
	// The relation to contain the evaled relation is the first symbol
	// between the parentheses
	elem out_rel = drt.eval_sym;
	// The relation containing the quotation arity is the second symbol
	// between the parentheses
	elem domain_sym = drt.domain_sym;
	// The formal symbol representing the quotation relation is the
	// third symbol between the parentheses
	elem quote_sym = drt.quote_sym;
	// The number representing how many database steps to interpret is
	// the fourth symbol between the parentheses
	int_t timeout = drt.timeout_num.num;
	// Get dictionary for generating fresh variables
	dict_t &d = tbl->get_dict();

	{
		elem e0(elem::SYM, t_arith_op::NOP, concat(out_rel.e, "_tick"));
		elem e1(elem::OPENP, t_arith_op::NOP, d.get_lexeme("("));
		elem e2(elem::CLOSEP, t_arith_op::NOP, d.get_lexeme(")"));
		raw_term rt3(raw_term::REL, t_arith_op::NOP, {e0, e1, e2, });
		rt3.neg = false;
		raw_term rt7(raw_term::REL, t_arith_op::NOP, {e0, e1, e2, });
		rt7.neg = false;
		sprawformtree ft6 = std::make_shared<raw_form_tree>(rt7);
		sprawformtree ft5 = std::make_shared<raw_form_tree>(elem::NOT, ft6);
		elem e10(elem::SYM, t_arith_op::NOP, concat(out_rel.e, "_tock"));
		raw_term rt11(raw_term::REL, t_arith_op::NOP, {e10, e1, e2, });
		rt11.neg = false;
		sprawformtree ft9 = std::make_shared<raw_form_tree>(rt11);
		sprawformtree ft8 = std::make_shared<raw_form_tree>(elem::NOT, ft9);
		sprawformtree ft4 = std::make_shared<raw_form_tree>(elem::AND, ft5, ft8);
		raw_rule rr12({rt3, }, ft4);
		raw_term rt13(raw_term::REL, t_arith_op::NOP, {e10, e1, e2, });
		rt13.neg = false;
		raw_term rt14(raw_term::REL, t_arith_op::NOP, {e0, e1, e2, });
		rt14.neg = true;
		raw_term rt16(raw_term::REL, t_arith_op::NOP, {e0, e1, e2, });
		rt16.neg = false;
		sprawformtree ft15 = std::make_shared<raw_form_tree>(rt16);
		raw_rule rr17({rt13, rt14, }, ft15);
		raw_term rt18(raw_term::REL, t_arith_op::NOP, {e0, e1, e2, });
		rt18.neg = false;
		raw_term rt19(raw_term::REL, t_arith_op::NOP, {e10, e1, e2, });
		rt19.neg = true;
		raw_term rt21(raw_term::REL, t_arith_op::NOP, {e10, e1, e2, });
		rt21.neg = false;
		sprawformtree ft20 = std::make_shared<raw_form_tree>(rt21);
		raw_rule rr22({rt18, rt19, }, ft20);
		elem e23(elem::SYM, t_arith_op::NOP, d.get_temp_sym(d.get_fresh_temp_sym(0)));
		elem e24(elem::VAR, t_arith_op::NOP, d.get_lexeme("?x"));
		raw_term rt25(raw_term::REL, t_arith_op::NOP, {e23, e1, e24, e2, });
		rt25.neg = false;
		elem e27(elem::SYM, t_arith_op::NOP, concat(domain_sym.e, "_fst"));
		elem e28(elem::VAR, t_arith_op::NOP, d.get_lexeme("?a"));
		raw_term rt29(raw_term::REL, t_arith_op::NOP, {e27, e1, e28, e24, e2, });
		rt29.neg = false;
		sprawformtree ft26 = std::make_shared<raw_form_tree>(rt29);
		raw_rule rr30({rt25, }, ft26);
		elem e31(elem::SYM, t_arith_op::NOP, d.get_temp_sym(d.get_fresh_temp_sym(0)));
		raw_term rt32(raw_term::REL, t_arith_op::NOP, {e31, e1, e24, e2, });
		rt32.neg = false;
		raw_term rt34(raw_term::REL, t_arith_op::NOP, {e27, e1, e24, e28, e2, });
		rt34.neg = false;
		sprawformtree ft33 = std::make_shared<raw_form_tree>(rt34);
		raw_rule rr35({rt32, }, ft33);
		raw_term rt36(raw_term::REL, t_arith_op::NOP, {e31, e1, e24, e2, });
		rt36.neg = false;
		elem e38(elem::SYM, t_arith_op::NOP, concat(domain_sym.e, "_nil"));
		raw_term rt39(raw_term::REL, t_arith_op::NOP, {e38, e1, e24, e2, });
		rt39.neg = false;
		sprawformtree ft37 = std::make_shared<raw_form_tree>(rt39);
		raw_rule rr40({rt36, }, ft37);
		elem e41(elem::SYM, t_arith_op::NOP, d.get_temp_sym(d.get_fresh_temp_sym(0)));
		elem e42(elem::VAR, t_arith_op::NOP, d.get_lexeme("?in"));
		elem e43(elem::VAR, t_arith_op::NOP, d.get_lexeme("?idx"));
		elem e44(elem::VAR, t_arith_op::NOP, d.get_lexeme("?out"));
		raw_term rt45(raw_term::REL, t_arith_op::NOP, {e41, e1, e42, e43, e44, e2, });
		rt45.neg = false;
		elem e54(elem::GT, t_arith_op::NOP, d.get_lexeme(">"));
		elem e55(int_t(0));
		raw_term rt56(raw_term::LEQ, t_arith_op::NOP, {e43, e54, e55, });
		rt56.neg = false;
		sprawformtree ft53 = std::make_shared<raw_form_tree>(rt56);
		sprawformtree ft52 = std::make_shared<raw_form_tree>(elem::NOT, ft53);
		elem e58(elem::VAR, t_arith_op::NOP, d.get_lexeme("?pred"));
		elem e59(elem::ARITH, t_arith_op::ADD, d.get_lexeme("+"));
		elem e60(int_t(1));
		elem e61(elem::EQ, t_arith_op::NOP, d.get_lexeme("="));
		raw_term rt62(raw_term::ARITH, t_arith_op::ADD, {e58, e59, e60, e61, e43, });
		rt62.neg = false;
		sprawformtree ft57 = std::make_shared<raw_form_tree>(rt62);
		sprawformtree ft51 = std::make_shared<raw_form_tree>(elem::AND, ft52, ft57);
		elem e64(elem::VAR, t_arith_op::NOP, d.get_lexeme("?in_hd"));
		raw_term rt65(raw_term::REL, t_arith_op::NOP, {e27, e1, e42, e64, e2, });
		rt65.neg = false;
		sprawformtree ft63 = std::make_shared<raw_form_tree>(rt65);
		sprawformtree ft50 = std::make_shared<raw_form_tree>(elem::AND, ft51, ft63);
		elem e67(elem::SYM, t_arith_op::NOP, concat(domain_sym.e, "_rst"));
		elem e68(elem::VAR, t_arith_op::NOP, d.get_lexeme("?in_tl"));
		raw_term rt69(raw_term::REL, t_arith_op::NOP, {e67, e1, e42, e68, e2, });
		rt69.neg = false;
		sprawformtree ft66 = std::make_shared<raw_form_tree>(rt69);
		sprawformtree ft49 = std::make_shared<raw_form_tree>(elem::AND, ft50, ft66);
		elem e71(elem::VAR, t_arith_op::NOP, d.get_lexeme("?out_hd"));
		raw_term rt72(raw_term::REL, t_arith_op::NOP, {e27, e1, e44, e71, e2, });
		rt72.neg = false;
		sprawformtree ft70 = std::make_shared<raw_form_tree>(rt72);
		sprawformtree ft48 = std::make_shared<raw_form_tree>(elem::AND, ft49, ft70);
		elem e74(elem::VAR, t_arith_op::NOP, d.get_lexeme("?out_tl"));
		raw_term rt75(raw_term::REL, t_arith_op::NOP, {e67, e1, e44, e74, e2, });
		rt75.neg = false;
		sprawformtree ft73 = std::make_shared<raw_form_tree>(rt75);
		sprawformtree ft47 = std::make_shared<raw_form_tree>(elem::AND, ft48, ft73);
		raw_term rt77(raw_term::REL, t_arith_op::NOP, {e41, e1, e68, e58, e74, e2, });
		rt77.neg = false;
		sprawformtree ft76 = std::make_shared<raw_form_tree>(rt77);
		sprawformtree ft46 = std::make_shared<raw_form_tree>(elem::AND, ft47, ft76);
		raw_rule rr78({rt45, }, ft46);
		raw_term rt79(raw_term::REL, t_arith_op::NOP, {e41, e1, e42, e55, e44, e2, });
		rt79.neg = false;
		raw_term rt85(raw_term::REL, t_arith_op::NOP, {e27, e1, e42, e64, e2, });
		rt85.neg = false;
		sprawformtree ft84 = std::make_shared<raw_form_tree>(rt85);
		raw_term rt87(raw_term::REL, t_arith_op::NOP, {e67, e1, e42, e68, e2, });
		rt87.neg = false;
		sprawformtree ft86 = std::make_shared<raw_form_tree>(rt87);
		sprawformtree ft83 = std::make_shared<raw_form_tree>(elem::AND, ft84, ft86);
		raw_term rt89(raw_term::REL, t_arith_op::NOP, {e23, e1, e71, e2, });
		rt89.neg = false;
		sprawformtree ft88 = std::make_shared<raw_form_tree>(rt89);
		sprawformtree ft82 = std::make_shared<raw_form_tree>(elem::AND, ft83, ft88);
		raw_term rt91(raw_term::REL, t_arith_op::NOP, {e27, e1, e44, e71, e2, });
		rt91.neg = false;
		sprawformtree ft90 = std::make_shared<raw_form_tree>(rt91);
		sprawformtree ft81 = std::make_shared<raw_form_tree>(elem::AND, ft82, ft90);
		raw_term rt93(raw_term::REL, t_arith_op::NOP, {e67, e1, e44, e68, e2, });
		rt93.neg = false;
		sprawformtree ft92 = std::make_shared<raw_form_tree>(rt93);
		sprawformtree ft80 = std::make_shared<raw_form_tree>(elem::AND, ft81, ft92);
		raw_rule rr94({rt79, }, ft80);
		elem e95(elem::SYM, t_arith_op::NOP, d.get_temp_sym(d.get_fresh_temp_sym(0)));
		elem e96(elem::VAR, t_arith_op::NOP, d.get_lexeme("?val"));
		raw_term rt97(raw_term::REL, t_arith_op::NOP, {e95, e1, e42, e43, e96, e2, });
		rt97.neg = false;
		raw_term rt105(raw_term::REL, t_arith_op::NOP, {e27, e1, e42, e64, e2, });
		rt105.neg = false;
		sprawformtree ft104 = std::make_shared<raw_form_tree>(rt105);
		raw_term rt107(raw_term::REL, t_arith_op::NOP, {e67, e1, e42, e68, e2, });
		rt107.neg = false;
		sprawformtree ft106 = std::make_shared<raw_form_tree>(rt107);
		sprawformtree ft103 = std::make_shared<raw_form_tree>(elem::AND, ft104, ft106);
		raw_term rt109(raw_term::REL, t_arith_op::NOP, {e95, e1, e68, e58, e96, e2, });
		rt109.neg = false;
		sprawformtree ft108 = std::make_shared<raw_form_tree>(rt109);
		sprawformtree ft102 = std::make_shared<raw_form_tree>(elem::AND, ft103, ft108);
		raw_term rt112(raw_term::LEQ, t_arith_op::NOP, {e43, e54, e55, });
		rt112.neg = false;
		sprawformtree ft111 = std::make_shared<raw_form_tree>(rt112);
		sprawformtree ft110 = std::make_shared<raw_form_tree>(elem::NOT, ft111);
		sprawformtree ft101 = std::make_shared<raw_form_tree>(elem::AND, ft102, ft110);
		raw_term rt114(raw_term::REL, t_arith_op::NOP, {e23, e1, e43, e2, });
		rt114.neg = false;
		sprawformtree ft113 = std::make_shared<raw_form_tree>(rt114);
		sprawformtree ft100 = std::make_shared<raw_form_tree>(elem::AND, ft101, ft113);
		raw_term rt116(raw_term::REL, t_arith_op::NOP, {e23, e1, e96, e2, });
		rt116.neg = false;
		sprawformtree ft115 = std::make_shared<raw_form_tree>(rt116);
		sprawformtree ft99 = std::make_shared<raw_form_tree>(elem::AND, ft100, ft115);
		raw_term rt118(raw_term::ARITH, t_arith_op::ADD, {e58, e59, e60, e61, e43, });
		rt118.neg = false;
		sprawformtree ft117 = std::make_shared<raw_form_tree>(rt118);
		sprawformtree ft98 = std::make_shared<raw_form_tree>(elem::AND, ft99, ft117);
		raw_rule rr119({rt97, }, ft98);
		raw_term rt120(raw_term::REL, t_arith_op::NOP, {e95, e1, e42, e55, e96, e2, });
		rt120.neg = false;
		raw_term rt124(raw_term::REL, t_arith_op::NOP, {e23, e1, e96, e2, });
		rt124.neg = false;
		sprawformtree ft123 = std::make_shared<raw_form_tree>(rt124);
		raw_term rt126(raw_term::REL, t_arith_op::NOP, {e27, e1, e42, e96, e2, });
		rt126.neg = false;
		sprawformtree ft125 = std::make_shared<raw_form_tree>(rt126);
		sprawformtree ft122 = std::make_shared<raw_form_tree>(elem::AND, ft123, ft125);
		raw_term rt128(raw_term::REL, t_arith_op::NOP, {e67, e1, e42, e68, e2, });
		rt128.neg = false;
		sprawformtree ft127 = std::make_shared<raw_form_tree>(rt128);
		sprawformtree ft121 = std::make_shared<raw_form_tree>(elem::AND, ft122, ft127);
		raw_rule rr129({rt120, }, ft121);
		elem e130(elem::SYM, t_arith_op::NOP, d.get_temp_sym(d.get_fresh_temp_sym(0)));
		elem e131(elem::VAR, t_arith_op::NOP, d.get_lexeme("?lst"));
		elem e132(elem::VAR, t_arith_op::NOP, d.get_lexeme("?inds"));
		elem e133(elem::VAR, t_arith_op::NOP, d.get_lexeme("?vals"));
		raw_term rt134(raw_term::REL, t_arith_op::NOP, {e130, e1, e131, e132, e133, e2, });
		rt134.neg = false;
		elem e141(elem::VAR, t_arith_op::NOP, d.get_lexeme("?inds_hd"));
		raw_term rt142(raw_term::REL, t_arith_op::NOP, {e27, e1, e132, e141, e2, });
		rt142.neg = false;
		sprawformtree ft140 = std::make_shared<raw_form_tree>(rt142);
		elem e144(elem::VAR, t_arith_op::NOP, d.get_lexeme("?inds_tl"));
		raw_term rt145(raw_term::REL, t_arith_op::NOP, {e67, e1, e132, e144, e2, });
		rt145.neg = false;
		sprawformtree ft143 = std::make_shared<raw_form_tree>(rt145);
		sprawformtree ft139 = std::make_shared<raw_form_tree>(elem::AND, ft140, ft143);
		elem e147(elem::VAR, t_arith_op::NOP, d.get_lexeme("?vals_hd"));
		raw_term rt148(raw_term::REL, t_arith_op::NOP, {e27, e1, e133, e147, e2, });
		rt148.neg = false;
		sprawformtree ft146 = std::make_shared<raw_form_tree>(rt148);
		sprawformtree ft138 = std::make_shared<raw_form_tree>(elem::AND, ft139, ft146);
		elem e150(elem::VAR, t_arith_op::NOP, d.get_lexeme("?vals_tl"));
		raw_term rt151(raw_term::REL, t_arith_op::NOP, {e67, e1, e133, e150, e2, });
		rt151.neg = false;
		sprawformtree ft149 = std::make_shared<raw_form_tree>(rt151);
		sprawformtree ft137 = std::make_shared<raw_form_tree>(elem::AND, ft138, ft149);
		raw_term rt153(raw_term::REL, t_arith_op::NOP, {e95, e1, e131, e141, e147, e2, });
		rt153.neg = false;
		sprawformtree ft152 = std::make_shared<raw_form_tree>(rt153);
		sprawformtree ft136 = std::make_shared<raw_form_tree>(elem::AND, ft137, ft152);
		raw_term rt155(raw_term::REL, t_arith_op::NOP, {e130, e1, e131, e144, e150, e2, });
		rt155.neg = false;
		sprawformtree ft154 = std::make_shared<raw_form_tree>(rt155);
		sprawformtree ft135 = std::make_shared<raw_form_tree>(elem::AND, ft136, ft154);
		raw_rule rr156({rt134, }, ft135);
		raw_term rt157(raw_term::REL, t_arith_op::NOP, {e130, e1, e131, e132, e133, e2, });
		rt157.neg = false;
		raw_term rt161(raw_term::REL, t_arith_op::NOP, {e31, e1, e131, e2, });
		rt161.neg = false;
		sprawformtree ft160 = std::make_shared<raw_form_tree>(rt161);
		raw_term rt163(raw_term::REL, t_arith_op::NOP, {e38, e1, e132, e2, });
		rt163.neg = false;
		sprawformtree ft162 = std::make_shared<raw_form_tree>(rt163);
		sprawformtree ft159 = std::make_shared<raw_form_tree>(elem::AND, ft160, ft162);
		raw_term rt165(raw_term::REL, t_arith_op::NOP, {e38, e1, e133, e2, });
		rt165.neg = false;
		sprawformtree ft164 = std::make_shared<raw_form_tree>(rt165);
		sprawformtree ft158 = std::make_shared<raw_form_tree>(elem::AND, ft159, ft164);
		raw_rule rr166({rt157, }, ft158);
		elem e167(elem::SYM, t_arith_op::NOP, d.get_temp_sym(d.get_fresh_temp_sym(0)));
		elem e168(elem::VAR, t_arith_op::NOP, d.get_lexeme("?chks"));
		raw_term rt169(raw_term::REL, t_arith_op::NOP, {e167, e1, e42, e168, e44, e2, });
		rt169.neg = false;
		raw_term rt177(raw_term::REL, t_arith_op::NOP, {e27, e1, e42, e64, e2, });
		rt177.neg = false;
		sprawformtree ft176 = std::make_shared<raw_form_tree>(rt177);
		raw_term rt179(raw_term::REL, t_arith_op::NOP, {e67, e1, e42, e68, e2, });
		rt179.neg = false;
		sprawformtree ft178 = std::make_shared<raw_form_tree>(rt179);
		sprawformtree ft175 = std::make_shared<raw_form_tree>(elem::AND, ft176, ft178);
		raw_term rt181(raw_term::REL, t_arith_op::NOP, {e27, e1, e168, e60, e2, });
		rt181.neg = false;
		sprawformtree ft180 = std::make_shared<raw_form_tree>(rt181);
		sprawformtree ft174 = std::make_shared<raw_form_tree>(elem::AND, ft175, ft180);
		elem e183(elem::VAR, t_arith_op::NOP, d.get_lexeme("?chks_tl"));
		raw_term rt184(raw_term::REL, t_arith_op::NOP, {e67, e1, e168, e183, e2, });
		rt184.neg = false;
		sprawformtree ft182 = std::make_shared<raw_form_tree>(rt184);
		sprawformtree ft173 = std::make_shared<raw_form_tree>(elem::AND, ft174, ft182);
		raw_term rt186(raw_term::REL, t_arith_op::NOP, {e27, e1, e44, e64, e2, });
		rt186.neg = false;
		sprawformtree ft185 = std::make_shared<raw_form_tree>(rt186);
		sprawformtree ft172 = std::make_shared<raw_form_tree>(elem::AND, ft173, ft185);
		raw_term rt188(raw_term::REL, t_arith_op::NOP, {e67, e1, e44, e74, e2, });
		rt188.neg = false;
		sprawformtree ft187 = std::make_shared<raw_form_tree>(rt188);
		sprawformtree ft171 = std::make_shared<raw_form_tree>(elem::AND, ft172, ft187);
		raw_term rt190(raw_term::REL, t_arith_op::NOP, {e167, e1, e68, e183, e74, e2, });
		rt190.neg = false;
		sprawformtree ft189 = std::make_shared<raw_form_tree>(rt190);
		sprawformtree ft170 = std::make_shared<raw_form_tree>(elem::AND, ft171, ft189);
		raw_rule rr191({rt169, }, ft170);
		raw_term rt192(raw_term::REL, t_arith_op::NOP, {e167, e1, e42, e168, e44, e2, });
		rt192.neg = false;
		raw_term rt198(raw_term::REL, t_arith_op::NOP, {e27, e1, e42, e64, e2, });
		rt198.neg = false;
		sprawformtree ft197 = std::make_shared<raw_form_tree>(rt198);
		raw_term rt200(raw_term::REL, t_arith_op::NOP, {e67, e1, e42, e68, e2, });
		rt200.neg = false;
		sprawformtree ft199 = std::make_shared<raw_form_tree>(rt200);
		sprawformtree ft196 = std::make_shared<raw_form_tree>(elem::AND, ft197, ft199);
		raw_term rt202(raw_term::REL, t_arith_op::NOP, {e27, e1, e168, e55, e2, });
		rt202.neg = false;
		sprawformtree ft201 = std::make_shared<raw_form_tree>(rt202);
		sprawformtree ft195 = std::make_shared<raw_form_tree>(elem::AND, ft196, ft201);
		raw_term rt204(raw_term::REL, t_arith_op::NOP, {e67, e1, e168, e183, e2, });
		rt204.neg = false;
		sprawformtree ft203 = std::make_shared<raw_form_tree>(rt204);
		sprawformtree ft194 = std::make_shared<raw_form_tree>(elem::AND, ft195, ft203);
		raw_term rt206(raw_term::REL, t_arith_op::NOP, {e167, e1, e68, e183, e44, e2, });
		rt206.neg = false;
		sprawformtree ft205 = std::make_shared<raw_form_tree>(rt206);
		sprawformtree ft193 = std::make_shared<raw_form_tree>(elem::AND, ft194, ft205);
		raw_rule rr207({rt192, }, ft193);
		raw_term rt208(raw_term::REL, t_arith_op::NOP, {e167, e1, e42, e168, e44, e2, });
		rt208.neg = false;
		raw_term rt212(raw_term::REL, t_arith_op::NOP, {e38, e1, e42, e2, });
		rt212.neg = false;
		sprawformtree ft211 = std::make_shared<raw_form_tree>(rt212);
		raw_term rt214(raw_term::REL, t_arith_op::NOP, {e38, e1, e168, e2, });
		rt214.neg = false;
		sprawformtree ft213 = std::make_shared<raw_form_tree>(rt214);
		sprawformtree ft210 = std::make_shared<raw_form_tree>(elem::AND, ft211, ft213);
		raw_term rt216(raw_term::REL, t_arith_op::NOP, {e38, e1, e44, e2, });
		rt216.neg = false;
		sprawformtree ft215 = std::make_shared<raw_form_tree>(rt216);
		sprawformtree ft209 = std::make_shared<raw_form_tree>(elem::AND, ft210, ft215);
		raw_rule rr217({rt208, }, ft209);
		elem e218(elem::SYM, t_arith_op::NOP, d.get_temp_sym(d.get_fresh_temp_sym(0)));
		raw_term rt219(raw_term::REL, t_arith_op::NOP, {e218, e1, e42, e168, e44, e2, });
		rt219.neg = false;
		raw_term rt227(raw_term::REL, t_arith_op::NOP, {e27, e1, e42, e64, e2, });
		rt227.neg = false;
		sprawformtree ft226 = std::make_shared<raw_form_tree>(rt227);
		raw_term rt229(raw_term::REL, t_arith_op::NOP, {e67, e1, e42, e68, e2, });
		rt229.neg = false;
		sprawformtree ft228 = std::make_shared<raw_form_tree>(rt229);
		sprawformtree ft225 = std::make_shared<raw_form_tree>(elem::AND, ft226, ft228);
		raw_term rt231(raw_term::REL, t_arith_op::NOP, {e27, e1, e168, e55, e2, });
		rt231.neg = false;
		sprawformtree ft230 = std::make_shared<raw_form_tree>(rt231);
		sprawformtree ft224 = std::make_shared<raw_form_tree>(elem::AND, ft225, ft230);
		raw_term rt233(raw_term::REL, t_arith_op::NOP, {e67, e1, e168, e183, e2, });
		rt233.neg = false;
		sprawformtree ft232 = std::make_shared<raw_form_tree>(rt233);
		sprawformtree ft223 = std::make_shared<raw_form_tree>(elem::AND, ft224, ft232);
		raw_term rt235(raw_term::REL, t_arith_op::NOP, {e27, e1, e44, e64, e2, });
		rt235.neg = false;
		sprawformtree ft234 = std::make_shared<raw_form_tree>(rt235);
		sprawformtree ft222 = std::make_shared<raw_form_tree>(elem::AND, ft223, ft234);
		raw_term rt237(raw_term::REL, t_arith_op::NOP, {e67, e1, e44, e74, e2, });
		rt237.neg = false;
		sprawformtree ft236 = std::make_shared<raw_form_tree>(rt237);
		sprawformtree ft221 = std::make_shared<raw_form_tree>(elem::AND, ft222, ft236);
		raw_term rt239(raw_term::REL, t_arith_op::NOP, {e218, e1, e68, e183, e74, e2, });
		rt239.neg = false;
		sprawformtree ft238 = std::make_shared<raw_form_tree>(rt239);
		sprawformtree ft220 = std::make_shared<raw_form_tree>(elem::AND, ft221, ft238);
		raw_rule rr240({rt219, }, ft220);
		raw_term rt241(raw_term::REL, t_arith_op::NOP, {e218, e1, e42, e168, e44, e2, });
		rt241.neg = false;
		raw_term rt247(raw_term::REL, t_arith_op::NOP, {e27, e1, e42, e64, e2, });
		rt247.neg = false;
		sprawformtree ft246 = std::make_shared<raw_form_tree>(rt247);
		raw_term rt249(raw_term::REL, t_arith_op::NOP, {e67, e1, e42, e68, e2, });
		rt249.neg = false;
		sprawformtree ft248 = std::make_shared<raw_form_tree>(rt249);
		sprawformtree ft245 = std::make_shared<raw_form_tree>(elem::AND, ft246, ft248);
		raw_term rt251(raw_term::REL, t_arith_op::NOP, {e27, e1, e168, e60, e2, });
		rt251.neg = false;
		sprawformtree ft250 = std::make_shared<raw_form_tree>(rt251);
		sprawformtree ft244 = std::make_shared<raw_form_tree>(elem::AND, ft245, ft250);
		raw_term rt253(raw_term::REL, t_arith_op::NOP, {e67, e1, e168, e183, e2, });
		rt253.neg = false;
		sprawformtree ft252 = std::make_shared<raw_form_tree>(rt253);
		sprawformtree ft243 = std::make_shared<raw_form_tree>(elem::AND, ft244, ft252);
		raw_term rt255(raw_term::REL, t_arith_op::NOP, {e218, e1, e68, e183, e44, e2, });
		rt255.neg = false;
		sprawformtree ft254 = std::make_shared<raw_form_tree>(rt255);
		sprawformtree ft242 = std::make_shared<raw_form_tree>(elem::AND, ft243, ft254);
		raw_rule rr256({rt241, }, ft242);
		raw_term rt257(raw_term::REL, t_arith_op::NOP, {e218, e1, e42, e168, e44, e2, });
		rt257.neg = false;
		raw_term rt261(raw_term::REL, t_arith_op::NOP, {e38, e1, e42, e2, });
		rt261.neg = false;
		sprawformtree ft260 = std::make_shared<raw_form_tree>(rt261);
		raw_term rt263(raw_term::REL, t_arith_op::NOP, {e38, e1, e168, e2, });
		rt263.neg = false;
		sprawformtree ft262 = std::make_shared<raw_form_tree>(rt263);
		sprawformtree ft259 = std::make_shared<raw_form_tree>(elem::AND, ft260, ft262);
		raw_term rt265(raw_term::REL, t_arith_op::NOP, {e38, e1, e44, e2, });
		rt265.neg = false;
		sprawformtree ft264 = std::make_shared<raw_form_tree>(rt265);
		sprawformtree ft258 = std::make_shared<raw_form_tree>(elem::AND, ft259, ft264);
		raw_rule rr266({rt257, }, ft258);
		elem e267(elem::SYM, t_arith_op::NOP, d.get_temp_sym(d.get_fresh_temp_sym(0)));
		elem e268(elem::VAR, t_arith_op::NOP, d.get_lexeme("?ts"));
		elem e269(elem::VAR, t_arith_op::NOP, d.get_lexeme("?id"));
		raw_term rt270(raw_term::REL, t_arith_op::NOP, {e267, e1, e268, e269, e44, e2, });
		rt270.neg = true;
		elem e271(elem::SYM, t_arith_op::NOP, concat(out_rel.e, "_databases"));
		elem e272(elem::VAR, t_arith_op::NOP, d.get_lexeme("?nts"));
		elem e273(elem::VAR, t_arith_op::NOP, d.get_lexeme("?name"));
		raw_term rt274(raw_term::REL, t_arith_op::NOP, {e271, e1, e272, e273, e44, e2, });
		rt274.neg = true;
		elem e275(elem::SYM, t_arith_op::NOP, concat(out_rel.e, "_fixpoint"));
		raw_term rt276(raw_term::REL, t_arith_op::NOP, {e275, e1, e268, e272, e2, });
		rt276.neg = true;
		raw_term rt278(raw_term::REL, t_arith_op::NOP, {e0, e1, e2, });
		rt278.neg = false;
		sprawformtree ft277 = std::make_shared<raw_form_tree>(rt278);
		raw_rule rr279({rt270, rt274, rt276, }, ft277);
		elem e280(elem::SYM, t_arith_op::NOP, d.get_temp_sym(d.get_fresh_temp_sym(0)));
		raw_term rt281(raw_term::REL, t_arith_op::NOP, {e280, e1, e268, e269, e44, e2, });
		rt281.neg = false;
		elem e286(elem::SYM, t_arith_op::NOP, d.get_temp_sym(d.get_fresh_temp_sym(0)));
		raw_term rt287(raw_term::REL, t_arith_op::NOP, {e286, e1, e268, e2, });
		rt287.neg = false;
		sprawformtree ft285 = std::make_shared<raw_form_tree>(rt287);
		elem e289(elem::SYM, t_arith_op::NOP, concat(quote_sym.e, "_type"));
		raw_term rt290(raw_term::REL, t_arith_op::NOP, {e289, e1, e269, e55, e2, });
		rt290.neg = false;
		sprawformtree ft288 = std::make_shared<raw_form_tree>(rt290);
		sprawformtree ft284 = std::make_shared<raw_form_tree>(elem::AND, ft285, ft288);
		elem e292(elem::SYM, t_arith_op::NOP, concat(domain_sym.e, "_max"));
		raw_term rt293(raw_term::REL, t_arith_op::NOP, {e292, e1, e44, e2, });
		rt293.neg = false;
		sprawformtree ft291 = std::make_shared<raw_form_tree>(rt293);
		sprawformtree ft283 = std::make_shared<raw_form_tree>(elem::AND, ft284, ft291);
		raw_term rt295(raw_term::REL, t_arith_op::NOP, {e0, e1, e2, });
		rt295.neg = false;
		sprawformtree ft294 = std::make_shared<raw_form_tree>(rt295);
		sprawformtree ft282 = std::make_shared<raw_form_tree>(elem::AND, ft283, ft294);
		raw_rule rr296({rt281, }, ft282);
		raw_term rt297(raw_term::REL, t_arith_op::NOP, {e280, e1, e268, e269, e44, e2, });
		rt297.neg = false;
		raw_term rt304(raw_term::REL, t_arith_op::NOP, {e286, e1, e268, e2, });
		rt304.neg = false;
		sprawformtree ft303 = std::make_shared<raw_form_tree>(rt304);
		elem e306(int_t(6));
		raw_term rt307(raw_term::REL, t_arith_op::NOP, {e289, e1, e269, e306, e2, });
		rt307.neg = false;
		sprawformtree ft305 = std::make_shared<raw_form_tree>(rt307);
		sprawformtree ft302 = std::make_shared<raw_form_tree>(elem::AND, ft303, ft305);
		elem e309(elem::SYM, t_arith_op::NOP, concat(quote_sym.e, "_not_body"));
		elem e310(elem::VAR, t_arith_op::NOP, d.get_lexeme("?qb"));
		raw_term rt311(raw_term::REL, t_arith_op::NOP, {e309, e1, e269, e310, e2, });
		rt311.neg = false;
		sprawformtree ft308 = std::make_shared<raw_form_tree>(rt311);
		sprawformtree ft301 = std::make_shared<raw_form_tree>(elem::AND, ft302, ft308);
		raw_term rt314(raw_term::REL, t_arith_op::NOP, {e267, e1, e268, e310, e44, e2, });
		rt314.neg = false;
		sprawformtree ft313 = std::make_shared<raw_form_tree>(rt314);
		sprawformtree ft312 = std::make_shared<raw_form_tree>(elem::NOT, ft313);
		sprawformtree ft300 = std::make_shared<raw_form_tree>(elem::AND, ft301, ft312);
		raw_term rt316(raw_term::REL, t_arith_op::NOP, {e292, e1, e44, e2, });
		rt316.neg = false;
		sprawformtree ft315 = std::make_shared<raw_form_tree>(rt316);
		sprawformtree ft299 = std::make_shared<raw_form_tree>(elem::AND, ft300, ft315);
		raw_term rt318(raw_term::REL, t_arith_op::NOP, {e0, e1, e2, });
		rt318.neg = false;
		sprawformtree ft317 = std::make_shared<raw_form_tree>(rt318);
		sprawformtree ft298 = std::make_shared<raw_form_tree>(elem::AND, ft299, ft317);
		raw_rule rr319({rt297, }, ft298);
		raw_term rt320(raw_term::REL, t_arith_op::NOP, {e280, e1, e268, e269, e44, e2, });
		rt320.neg = false;
		elem e327(int_t(7));
		raw_term rt328(raw_term::REL, t_arith_op::NOP, {e289, e1, e269, e327, e2, });
		rt328.neg = false;
		sprawformtree ft326 = std::make_shared<raw_form_tree>(rt328);
		elem e330(elem::SYM, t_arith_op::NOP, concat(quote_sym.e, "_and_left"));
		elem e331(elem::VAR, t_arith_op::NOP, d.get_lexeme("?ql"));
		raw_term rt332(raw_term::REL, t_arith_op::NOP, {e330, e1, e269, e331, e2, });
		rt332.neg = false;
		sprawformtree ft329 = std::make_shared<raw_form_tree>(rt332);
		sprawformtree ft325 = std::make_shared<raw_form_tree>(elem::AND, ft326, ft329);
		elem e334(elem::SYM, t_arith_op::NOP, concat(quote_sym.e, "_and_right"));
		elem e335(elem::VAR, t_arith_op::NOP, d.get_lexeme("?qr"));
		raw_term rt336(raw_term::REL, t_arith_op::NOP, {e334, e1, e269, e335, e2, });
		rt336.neg = false;
		sprawformtree ft333 = std::make_shared<raw_form_tree>(rt336);
		sprawformtree ft324 = std::make_shared<raw_form_tree>(elem::AND, ft325, ft333);
		raw_term rt338(raw_term::REL, t_arith_op::NOP, {e267, e1, e268, e331, e44, e2, });
		rt338.neg = false;
		sprawformtree ft337 = std::make_shared<raw_form_tree>(rt338);
		sprawformtree ft323 = std::make_shared<raw_form_tree>(elem::AND, ft324, ft337);
		raw_term rt340(raw_term::REL, t_arith_op::NOP, {e267, e1, e268, e335, e44, e2, });
		rt340.neg = false;
		sprawformtree ft339 = std::make_shared<raw_form_tree>(rt340);
		sprawformtree ft322 = std::make_shared<raw_form_tree>(elem::AND, ft323, ft339);
		raw_term rt342(raw_term::REL, t_arith_op::NOP, {e0, e1, e2, });
		rt342.neg = false;
		sprawformtree ft341 = std::make_shared<raw_form_tree>(rt342);
		sprawformtree ft321 = std::make_shared<raw_form_tree>(elem::AND, ft322, ft341);
		raw_rule rr343({rt320, }, ft321);
		raw_term rt344(raw_term::REL, t_arith_op::NOP, {e280, e1, e268, e269, e44, e2, });
		rt344.neg = false;
		elem e350(int_t(8));
		raw_term rt351(raw_term::REL, t_arith_op::NOP, {e289, e1, e269, e350, e2, });
		rt351.neg = false;
		sprawformtree ft349 = std::make_shared<raw_form_tree>(rt351);
		elem e353(elem::SYM, t_arith_op::NOP, concat(quote_sym.e, "_or_left"));
		raw_term rt354(raw_term::REL, t_arith_op::NOP, {e353, e1, e269, e331, e2, });
		rt354.neg = false;
		sprawformtree ft352 = std::make_shared<raw_form_tree>(rt354);
		sprawformtree ft348 = std::make_shared<raw_form_tree>(elem::AND, ft349, ft352);
		elem e356(elem::SYM, t_arith_op::NOP, concat(quote_sym.e, "_or_right"));
		raw_term rt357(raw_term::REL, t_arith_op::NOP, {e356, e1, e269, e335, e2, });
		rt357.neg = false;
		sprawformtree ft355 = std::make_shared<raw_form_tree>(rt357);
		sprawformtree ft347 = std::make_shared<raw_form_tree>(elem::AND, ft348, ft355);
		raw_term rt359(raw_term::REL, t_arith_op::NOP, {e267, e1, e268, e331, e44, e2, });
		rt359.neg = false;
		sprawformtree ft358 = std::make_shared<raw_form_tree>(rt359);
		sprawformtree ft346 = std::make_shared<raw_form_tree>(elem::AND, ft347, ft358);
		raw_term rt361(raw_term::REL, t_arith_op::NOP, {e0, e1, e2, });
		rt361.neg = false;
		sprawformtree ft360 = std::make_shared<raw_form_tree>(rt361);
		sprawformtree ft345 = std::make_shared<raw_form_tree>(elem::AND, ft346, ft360);
		raw_rule rr362({rt344, }, ft345);
		raw_term rt363(raw_term::REL, t_arith_op::NOP, {e280, e1, e268, e269, e44, e2, });
		rt363.neg = false;
		raw_term rt369(raw_term::REL, t_arith_op::NOP, {e289, e1, e269, e350, e2, });
		rt369.neg = false;
		sprawformtree ft368 = std::make_shared<raw_form_tree>(rt369);
		raw_term rt371(raw_term::REL, t_arith_op::NOP, {e353, e1, e269, e331, e2, });
		rt371.neg = false;
		sprawformtree ft370 = std::make_shared<raw_form_tree>(rt371);
		sprawformtree ft367 = std::make_shared<raw_form_tree>(elem::AND, ft368, ft370);
		raw_term rt373(raw_term::REL, t_arith_op::NOP, {e356, e1, e269, e335, e2, });
		rt373.neg = false;
		sprawformtree ft372 = std::make_shared<raw_form_tree>(rt373);
		sprawformtree ft366 = std::make_shared<raw_form_tree>(elem::AND, ft367, ft372);
		raw_term rt375(raw_term::REL, t_arith_op::NOP, {e267, e1, e268, e335, e44, e2, });
		rt375.neg = false;
		sprawformtree ft374 = std::make_shared<raw_form_tree>(rt375);
		sprawformtree ft365 = std::make_shared<raw_form_tree>(elem::AND, ft366, ft374);
		raw_term rt377(raw_term::REL, t_arith_op::NOP, {e0, e1, e2, });
		rt377.neg = false;
		sprawformtree ft376 = std::make_shared<raw_form_tree>(rt377);
		sprawformtree ft364 = std::make_shared<raw_form_tree>(elem::AND, ft365, ft376);
		raw_rule rr378({rt363, }, ft364);
		raw_term rt379(raw_term::REL, t_arith_op::NOP, {e280, e1, e268, e269, e44, e2, });
		rt379.neg = false;
		elem e392(int_t(2));
		raw_term rt393(raw_term::REL, t_arith_op::NOP, {e289, e1, e269, e392, e2, });
		rt393.neg = false;
		sprawformtree ft391 = std::make_shared<raw_form_tree>(rt393);
		elem e395(elem::SYM, t_arith_op::NOP, concat(quote_sym.e, "_term_relation"));
		raw_term rt396(raw_term::REL, t_arith_op::NOP, {e395, e1, e269, e273, e2, });
		rt396.neg = false;
		sprawformtree ft394 = std::make_shared<raw_form_tree>(rt396);
		sprawformtree ft390 = std::make_shared<raw_form_tree>(elem::AND, ft391, ft394);
		elem e398(elem::SYM, t_arith_op::NOP, concat(quote_sym.e, "_term_params"));
		elem e399(elem::VAR, t_arith_op::NOP, d.get_lexeme("?vars"));
		raw_term rt400(raw_term::REL, t_arith_op::NOP, {e398, e1, e269, e399, e2, });
		rt400.neg = false;
		sprawformtree ft397 = std::make_shared<raw_form_tree>(rt400);
		sprawformtree ft389 = std::make_shared<raw_form_tree>(elem::AND, ft390, ft397);
		elem e402(elem::SYM, t_arith_op::NOP, concat(quote_sym.e, "_term_param_types"));
		raw_term rt403(raw_term::REL, t_arith_op::NOP, {e402, e1, e269, e168, e2, });
		rt403.neg = false;
		sprawformtree ft401 = std::make_shared<raw_form_tree>(rt403);
		sprawformtree ft388 = std::make_shared<raw_form_tree>(elem::AND, ft389, ft401);
		raw_term rt405(raw_term::REL, t_arith_op::NOP, {e271, e1, e268, e273, e133, e2, });
		rt405.neg = false;
		sprawformtree ft404 = std::make_shared<raw_form_tree>(rt405);
		sprawformtree ft387 = std::make_shared<raw_form_tree>(elem::AND, ft388, ft404);
		raw_term rt407(raw_term::REL, t_arith_op::NOP, {e292, e1, e44, e2, });
		rt407.neg = false;
		sprawformtree ft406 = std::make_shared<raw_form_tree>(rt407);
		sprawformtree ft386 = std::make_shared<raw_form_tree>(elem::AND, ft387, ft406);
		elem e409(elem::VAR, t_arith_op::NOP, d.get_lexeme("?vars_s"));
		raw_term rt410(raw_term::REL, t_arith_op::NOP, {e167, e1, e399, e168, e409, e2, });
		rt410.neg = false;
		sprawformtree ft408 = std::make_shared<raw_form_tree>(rt410);
		sprawformtree ft385 = std::make_shared<raw_form_tree>(elem::AND, ft386, ft408);
		elem e412(elem::VAR, t_arith_op::NOP, d.get_lexeme("?vals_s"));
		raw_term rt413(raw_term::REL, t_arith_op::NOP, {e167, e1, e133, e168, e412, e2, });
		rt413.neg = false;
		sprawformtree ft411 = std::make_shared<raw_form_tree>(rt413);
		sprawformtree ft384 = std::make_shared<raw_form_tree>(elem::AND, ft385, ft411);
		raw_term rt415(raw_term::REL, t_arith_op::NOP, {e130, e1, e44, e409, e412, e2, });
		rt415.neg = false;
		sprawformtree ft414 = std::make_shared<raw_form_tree>(rt415);
		sprawformtree ft383 = std::make_shared<raw_form_tree>(elem::AND, ft384, ft414);
		elem e417(elem::VAR, t_arith_op::NOP, d.get_lexeme("?syms"));
		raw_term rt418(raw_term::REL, t_arith_op::NOP, {e218, e1, e399, e168, e417, e2, });
		rt418.neg = false;
		sprawformtree ft416 = std::make_shared<raw_form_tree>(rt418);
		sprawformtree ft382 = std::make_shared<raw_form_tree>(elem::AND, ft383, ft416);
		raw_term rt420(raw_term::REL, t_arith_op::NOP, {e218, e1, e133, e168, e417, e2, });
		rt420.neg = false;
		sprawformtree ft419 = std::make_shared<raw_form_tree>(rt420);
		sprawformtree ft381 = std::make_shared<raw_form_tree>(elem::AND, ft382, ft419);
		raw_term rt422(raw_term::REL, t_arith_op::NOP, {e0, e1, e2, });
		rt422.neg = false;
		sprawformtree ft421 = std::make_shared<raw_form_tree>(rt422);
		sprawformtree ft380 = std::make_shared<raw_form_tree>(elem::AND, ft381, ft421);
		raw_rule rr423({rt379, }, ft380);
		elem e424(elem::SYM, t_arith_op::NOP, d.get_temp_sym(d.get_fresh_temp_sym(0)));
		raw_term rt425(raw_term::REL, t_arith_op::NOP, {e424, e1, e268, e273, e44, e2, });
		rt425.neg = false;
		raw_term rt440(raw_term::REL, t_arith_op::NOP, {e289, e1, e269, e60, e2, });
		rt440.neg = false;
		sprawformtree ft439 = std::make_shared<raw_form_tree>(rt440);
		elem e442(elem::SYM, t_arith_op::NOP, concat(quote_sym.e, "_rule_head"));
		elem e443(elem::VAR, t_arith_op::NOP, d.get_lexeme("?qh"));
		raw_term rt444(raw_term::REL, t_arith_op::NOP, {e442, e1, e269, e443, e2, });
		rt444.neg = false;
		sprawformtree ft441 = std::make_shared<raw_form_tree>(rt444);
		sprawformtree ft438 = std::make_shared<raw_form_tree>(elem::AND, ft439, ft441);
		elem e446(elem::SYM, t_arith_op::NOP, concat(quote_sym.e, "_rule_body"));
		raw_term rt447(raw_term::REL, t_arith_op::NOP, {e446, e1, e269, e310, e2, });
		rt447.neg = false;
		sprawformtree ft445 = std::make_shared<raw_form_tree>(rt447);
		sprawformtree ft437 = std::make_shared<raw_form_tree>(elem::AND, ft438, ft445);
		raw_term rt449(raw_term::REL, t_arith_op::NOP, {e289, e1, e443, e392, e2, });
		rt449.neg = false;
		sprawformtree ft448 = std::make_shared<raw_form_tree>(rt449);
		sprawformtree ft436 = std::make_shared<raw_form_tree>(elem::AND, ft437, ft448);
		raw_term rt451(raw_term::REL, t_arith_op::NOP, {e395, e1, e443, e273, e2, });
		rt451.neg = false;
		sprawformtree ft450 = std::make_shared<raw_form_tree>(rt451);
		sprawformtree ft435 = std::make_shared<raw_form_tree>(elem::AND, ft436, ft450);
		raw_term rt453(raw_term::REL, t_arith_op::NOP, {e398, e1, e443, e399, e2, });
		rt453.neg = false;
		sprawformtree ft452 = std::make_shared<raw_form_tree>(rt453);
		sprawformtree ft434 = std::make_shared<raw_form_tree>(elem::AND, ft435, ft452);
		raw_term rt455(raw_term::REL, t_arith_op::NOP, {e402, e1, e443, e168, e2, });
		rt455.neg = false;
		sprawformtree ft454 = std::make_shared<raw_form_tree>(rt455);
		sprawformtree ft433 = std::make_shared<raw_form_tree>(elem::AND, ft434, ft454);
		raw_term rt457(raw_term::REL, t_arith_op::NOP, {e267, e1, e268, e310, e133, e2, });
		rt457.neg = false;
		sprawformtree ft456 = std::make_shared<raw_form_tree>(rt457);
		sprawformtree ft432 = std::make_shared<raw_form_tree>(elem::AND, ft433, ft456);
		raw_term rt459(raw_term::REL, t_arith_op::NOP, {e167, e1, e399, e168, e409, e2, });
		rt459.neg = false;
		sprawformtree ft458 = std::make_shared<raw_form_tree>(rt459);
		sprawformtree ft431 = std::make_shared<raw_form_tree>(elem::AND, ft432, ft458);
		elem e461(elem::VAR, t_arith_op::NOP, d.get_lexeme("?out_s"));
		raw_term rt462(raw_term::REL, t_arith_op::NOP, {e167, e1, e44, e168, e461, e2, });
		rt462.neg = false;
		sprawformtree ft460 = std::make_shared<raw_form_tree>(rt462);
		sprawformtree ft430 = std::make_shared<raw_form_tree>(elem::AND, ft431, ft460);
		raw_term rt464(raw_term::REL, t_arith_op::NOP, {e130, e1, e133, e409, e461, e2, });
		rt464.neg = false;
		sprawformtree ft463 = std::make_shared<raw_form_tree>(rt464);
		sprawformtree ft429 = std::make_shared<raw_form_tree>(elem::AND, ft430, ft463);
		raw_term rt466(raw_term::REL, t_arith_op::NOP, {e218, e1, e399, e168, e417, e2, });
		rt466.neg = false;
		sprawformtree ft465 = std::make_shared<raw_form_tree>(rt466);
		sprawformtree ft428 = std::make_shared<raw_form_tree>(elem::AND, ft429, ft465);
		raw_term rt468(raw_term::REL, t_arith_op::NOP, {e218, e1, e44, e168, e417, e2, });
		rt468.neg = false;
		sprawformtree ft467 = std::make_shared<raw_form_tree>(rt468);
		sprawformtree ft427 = std::make_shared<raw_form_tree>(elem::AND, ft428, ft467);
		raw_term rt470(raw_term::REL, t_arith_op::NOP, {e0, e1, e2, });
		rt470.neg = false;
		sprawformtree ft469 = std::make_shared<raw_form_tree>(rt470);
		sprawformtree ft426 = std::make_shared<raw_form_tree>(elem::AND, ft427, ft469);
		raw_rule rr471({rt425, }, ft426);
		elem e472(elem::SYM, t_arith_op::NOP, d.get_temp_sym(d.get_fresh_temp_sym(0)));
		raw_term rt473(raw_term::REL, t_arith_op::NOP, {e472, e1, e268, e273, e44, e2, });
		rt473.neg = false;
		raw_term rt490(raw_term::REL, t_arith_op::NOP, {e289, e1, e269, e60, e2, });
		rt490.neg = false;
		sprawformtree ft489 = std::make_shared<raw_form_tree>(rt490);
		elem e492(elem::VAR, t_arith_op::NOP, d.get_lexeme("?qnh"));
		raw_term rt493(raw_term::REL, t_arith_op::NOP, {e442, e1, e269, e492, e2, });
		rt493.neg = false;
		sprawformtree ft491 = std::make_shared<raw_form_tree>(rt493);
		sprawformtree ft488 = std::make_shared<raw_form_tree>(elem::AND, ft489, ft491);
		raw_term rt495(raw_term::REL, t_arith_op::NOP, {e446, e1, e269, e310, e2, });
		rt495.neg = false;
		sprawformtree ft494 = std::make_shared<raw_form_tree>(rt495);
		sprawformtree ft487 = std::make_shared<raw_form_tree>(elem::AND, ft488, ft494);
		raw_term rt497(raw_term::REL, t_arith_op::NOP, {e289, e1, e492, e306, e2, });
		rt497.neg = false;
		sprawformtree ft496 = std::make_shared<raw_form_tree>(rt497);
		sprawformtree ft486 = std::make_shared<raw_form_tree>(elem::AND, ft487, ft496);
		raw_term rt499(raw_term::REL, t_arith_op::NOP, {e309, e1, e492, e443, e2, });
		rt499.neg = false;
		sprawformtree ft498 = std::make_shared<raw_form_tree>(rt499);
		sprawformtree ft485 = std::make_shared<raw_form_tree>(elem::AND, ft486, ft498);
		raw_term rt501(raw_term::REL, t_arith_op::NOP, {e289, e1, e443, e392, e2, });
		rt501.neg = false;
		sprawformtree ft500 = std::make_shared<raw_form_tree>(rt501);
		sprawformtree ft484 = std::make_shared<raw_form_tree>(elem::AND, ft485, ft500);
		raw_term rt503(raw_term::REL, t_arith_op::NOP, {e395, e1, e443, e273, e2, });
		rt503.neg = false;
		sprawformtree ft502 = std::make_shared<raw_form_tree>(rt503);
		sprawformtree ft483 = std::make_shared<raw_form_tree>(elem::AND, ft484, ft502);
		raw_term rt505(raw_term::REL, t_arith_op::NOP, {e398, e1, e443, e399, e2, });
		rt505.neg = false;
		sprawformtree ft504 = std::make_shared<raw_form_tree>(rt505);
		sprawformtree ft482 = std::make_shared<raw_form_tree>(elem::AND, ft483, ft504);
		raw_term rt507(raw_term::REL, t_arith_op::NOP, {e402, e1, e443, e168, e2, });
		rt507.neg = false;
		sprawformtree ft506 = std::make_shared<raw_form_tree>(rt507);
		sprawformtree ft481 = std::make_shared<raw_form_tree>(elem::AND, ft482, ft506);
		raw_term rt509(raw_term::REL, t_arith_op::NOP, {e267, e1, e268, e310, e133, e2, });
		rt509.neg = false;
		sprawformtree ft508 = std::make_shared<raw_form_tree>(rt509);
		sprawformtree ft480 = std::make_shared<raw_form_tree>(elem::AND, ft481, ft508);
		raw_term rt511(raw_term::REL, t_arith_op::NOP, {e167, e1, e399, e168, e409, e2, });
		rt511.neg = false;
		sprawformtree ft510 = std::make_shared<raw_form_tree>(rt511);
		sprawformtree ft479 = std::make_shared<raw_form_tree>(elem::AND, ft480, ft510);
		raw_term rt513(raw_term::REL, t_arith_op::NOP, {e167, e1, e44, e168, e461, e2, });
		rt513.neg = false;
		sprawformtree ft512 = std::make_shared<raw_form_tree>(rt513);
		sprawformtree ft478 = std::make_shared<raw_form_tree>(elem::AND, ft479, ft512);
		raw_term rt515(raw_term::REL, t_arith_op::NOP, {e130, e1, e133, e409, e461, e2, });
		rt515.neg = false;
		sprawformtree ft514 = std::make_shared<raw_form_tree>(rt515);
		sprawformtree ft477 = std::make_shared<raw_form_tree>(elem::AND, ft478, ft514);
		raw_term rt517(raw_term::REL, t_arith_op::NOP, {e218, e1, e399, e168, e417, e2, });
		rt517.neg = false;
		sprawformtree ft516 = std::make_shared<raw_form_tree>(rt517);
		sprawformtree ft476 = std::make_shared<raw_form_tree>(elem::AND, ft477, ft516);
		raw_term rt519(raw_term::REL, t_arith_op::NOP, {e218, e1, e44, e168, e417, e2, });
		rt519.neg = false;
		sprawformtree ft518 = std::make_shared<raw_form_tree>(rt519);
		sprawformtree ft475 = std::make_shared<raw_form_tree>(elem::AND, ft476, ft518);
		raw_term rt521(raw_term::REL, t_arith_op::NOP, {e0, e1, e2, });
		rt521.neg = false;
		sprawformtree ft520 = std::make_shared<raw_form_tree>(rt521);
		sprawformtree ft474 = std::make_shared<raw_form_tree>(elem::AND, ft475, ft520);
		raw_rule rr522({rt473, }, ft474);
		elem e523(elem::SYM, t_arith_op::NOP, d.get_temp_sym(d.get_fresh_temp_sym(0)));
		raw_term rt524(raw_term::REL, t_arith_op::NOP, {e523, e1, e272, e273, e44, e2, });
		rt524.neg = false;
		raw_term rt527(raw_term::REL, t_arith_op::NOP, {e271, e1, e272, e273, e44, e2, });
		rt527.neg = false;
		sprawformtree ft526 = std::make_shared<raw_form_tree>(rt527);
		raw_term rt529(raw_term::REL, t_arith_op::NOP, {e0, e1, e2, });
		rt529.neg = false;
		sprawformtree ft528 = std::make_shared<raw_form_tree>(rt529);
		sprawformtree ft525 = std::make_shared<raw_form_tree>(elem::AND, ft526, ft528);
		raw_rule rr530({rt524, }, ft525);
		elem e531(elem::SYM, t_arith_op::NOP, d.get_temp_sym(d.get_fresh_temp_sym(0)));
		raw_term rt532(raw_term::REL, t_arith_op::NOP, {e531, e1, e268, e272, e2, });
		rt532.neg = false;
		elem e540(elem::LT, t_arith_op::NOP, d.get_lexeme("<"));
		raw_term rt541(raw_term::LEQ, t_arith_op::NOP, {e272, e540, e268, });
		rt541.neg = false;
		sprawformtree ft539 = std::make_shared<raw_form_tree>(rt541);
		sprawformtree ft538 = std::make_shared<raw_form_tree>(elem::NOT, ft539);
		raw_term rt543(raw_term::REL, t_arith_op::NOP, {e286, e1, e268, e2, });
		rt543.neg = false;
		sprawformtree ft542 = std::make_shared<raw_form_tree>(rt543);
		sprawformtree ft537 = std::make_shared<raw_form_tree>(elem::AND, ft538, ft542);
		raw_term rt545(raw_term::REL, t_arith_op::NOP, {e286, e1, e272, e2, });
		rt545.neg = false;
		sprawformtree ft544 = std::make_shared<raw_form_tree>(rt545);
		sprawformtree ft536 = std::make_shared<raw_form_tree>(elem::AND, ft537, ft544);
		raw_term rt547(raw_term::REL, t_arith_op::NOP, {e271, e1, e268, e273, e44, e2, });
		rt547.neg = false;
		sprawformtree ft546 = std::make_shared<raw_form_tree>(rt547);
		sprawformtree ft535 = std::make_shared<raw_form_tree>(elem::AND, ft536, ft546);
		raw_term rt550(raw_term::REL, t_arith_op::NOP, {e271, e1, e272, e273, e44, e2, });
		rt550.neg = false;
		sprawformtree ft549 = std::make_shared<raw_form_tree>(rt550);
		sprawformtree ft548 = std::make_shared<raw_form_tree>(elem::NOT, ft549);
		sprawformtree ft534 = std::make_shared<raw_form_tree>(elem::AND, ft535, ft548);
		raw_term rt552(raw_term::REL, t_arith_op::NOP, {e0, e1, e2, });
		rt552.neg = false;
		sprawformtree ft551 = std::make_shared<raw_form_tree>(rt552);
		sprawformtree ft533 = std::make_shared<raw_form_tree>(elem::AND, ft534, ft551);
		raw_rule rr553({rt532, }, ft533);
		raw_term rt554(raw_term::REL, t_arith_op::NOP, {e531, e1, e268, e272, e2, });
		rt554.neg = false;
		raw_term rt562(raw_term::LEQ, t_arith_op::NOP, {e272, e540, e268, });
		rt562.neg = false;
		sprawformtree ft561 = std::make_shared<raw_form_tree>(rt562);
		sprawformtree ft560 = std::make_shared<raw_form_tree>(elem::NOT, ft561);
		raw_term rt564(raw_term::REL, t_arith_op::NOP, {e286, e1, e268, e2, });
		rt564.neg = false;
		sprawformtree ft563 = std::make_shared<raw_form_tree>(rt564);
		sprawformtree ft559 = std::make_shared<raw_form_tree>(elem::AND, ft560, ft563);
		raw_term rt566(raw_term::REL, t_arith_op::NOP, {e286, e1, e272, e2, });
		rt566.neg = false;
		sprawformtree ft565 = std::make_shared<raw_form_tree>(rt566);
		sprawformtree ft558 = std::make_shared<raw_form_tree>(elem::AND, ft559, ft565);
		raw_term rt569(raw_term::REL, t_arith_op::NOP, {e271, e1, e268, e273, e44, e2, });
		rt569.neg = false;
		sprawformtree ft568 = std::make_shared<raw_form_tree>(rt569);
		sprawformtree ft567 = std::make_shared<raw_form_tree>(elem::NOT, ft568);
		sprawformtree ft557 = std::make_shared<raw_form_tree>(elem::AND, ft558, ft567);
		raw_term rt571(raw_term::REL, t_arith_op::NOP, {e271, e1, e272, e273, e44, e2, });
		rt571.neg = false;
		sprawformtree ft570 = std::make_shared<raw_form_tree>(rt571);
		sprawformtree ft556 = std::make_shared<raw_form_tree>(elem::AND, ft557, ft570);
		raw_term rt573(raw_term::REL, t_arith_op::NOP, {e0, e1, e2, });
		rt573.neg = false;
		sprawformtree ft572 = std::make_shared<raw_form_tree>(rt573);
		sprawformtree ft555 = std::make_shared<raw_form_tree>(elem::AND, ft556, ft572);
		raw_rule rr574({rt554, }, ft555);
		raw_term rt575(raw_term::REL, t_arith_op::NOP, {e280, e1, e268, e269, e44, e2, });
		rt575.neg = true;
		raw_term rt576(raw_term::REL, t_arith_op::NOP, {e424, e1, e268, e273, e44, e2, });
		rt576.neg = true;
		raw_term rt577(raw_term::REL, t_arith_op::NOP, {e472, e1, e268, e273, e44, e2, });
		rt577.neg = true;
		raw_term rt578(raw_term::REL, t_arith_op::NOP, {e523, e1, e272, e273, e44, e2, });
		rt578.neg = true;
		raw_term rt579(raw_term::REL, t_arith_op::NOP, {e531, e1, e268, e272, e2, });
		rt579.neg = true;
		raw_term rt581(raw_term::REL, t_arith_op::NOP, {e10, e1, e2, });
		rt581.neg = false;
		sprawformtree ft580 = std::make_shared<raw_form_tree>(rt581);
		raw_rule rr582({rt575, rt576, rt577, rt578, rt579, }, ft580);
		raw_term rt583(raw_term::REL, t_arith_op::NOP, {e286, e1, e268, e2, });
		rt583.neg = false;
		elem e587(elem::LEQ, t_arith_op::NOP, d.get_lexeme("<="));
		raw_term rt588(raw_term::LEQ, t_arith_op::NOP, {e55, e587, e268, });
		rt588.neg = false;
		sprawformtree ft586 = std::make_shared<raw_form_tree>(rt588);
		elem e591(timeout);
		raw_term rt592(raw_term::LEQ, t_arith_op::NOP, {e591, e540, e268, });
		rt592.neg = false;
		sprawformtree ft590 = std::make_shared<raw_form_tree>(rt592);
		sprawformtree ft589 = std::make_shared<raw_form_tree>(elem::NOT, ft590);
		sprawformtree ft585 = std::make_shared<raw_form_tree>(elem::AND, ft586, ft589);
		raw_term rt594(raw_term::ARITH, t_arith_op::ADD, {e268, e59, e55, e61, e268, });
		rt594.neg = false;
		sprawformtree ft593 = std::make_shared<raw_form_tree>(rt594);
		sprawformtree ft584 = std::make_shared<raw_form_tree>(elem::AND, ft585, ft593);
		raw_rule rr595({rt583, }, ft584);
		raw_term rt596(raw_term::REL, t_arith_op::NOP, {e271, e1, e55, e273, e44, e2, });
		rt596.neg = false;
		raw_term rt607(raw_term::REL, t_arith_op::NOP, {e289, e1, e269, e55, e2, });
		rt607.neg = false;
		sprawformtree ft606 = std::make_shared<raw_form_tree>(rt607);
		elem e609(elem::SYM, t_arith_op::NOP, concat(quote_sym.e, "_fact_term"));
		elem e610(elem::VAR, t_arith_op::NOP, d.get_lexeme("?qt"));
		raw_term rt611(raw_term::REL, t_arith_op::NOP, {e609, e1, e269, e610, e2, });
		rt611.neg = false;
		sprawformtree ft608 = std::make_shared<raw_form_tree>(rt611);
		sprawformtree ft605 = std::make_shared<raw_form_tree>(elem::AND, ft606, ft608);
		raw_term rt613(raw_term::REL, t_arith_op::NOP, {e289, e1, e610, e392, e2, });
		rt613.neg = false;
		sprawformtree ft612 = std::make_shared<raw_form_tree>(rt613);
		sprawformtree ft604 = std::make_shared<raw_form_tree>(elem::AND, ft605, ft612);
		raw_term rt615(raw_term::REL, t_arith_op::NOP, {e395, e1, e610, e273, e2, });
		rt615.neg = false;
		sprawformtree ft614 = std::make_shared<raw_form_tree>(rt615);
		sprawformtree ft603 = std::make_shared<raw_form_tree>(elem::AND, ft604, ft614);
		raw_term rt617(raw_term::REL, t_arith_op::NOP, {e398, e1, e610, e399, e2, });
		rt617.neg = false;
		sprawformtree ft616 = std::make_shared<raw_form_tree>(rt617);
		sprawformtree ft602 = std::make_shared<raw_form_tree>(elem::AND, ft603, ft616);
		raw_term rt619(raw_term::REL, t_arith_op::NOP, {e402, e1, e610, e168, e2, });
		rt619.neg = false;
		sprawformtree ft618 = std::make_shared<raw_form_tree>(rt619);
		sprawformtree ft601 = std::make_shared<raw_form_tree>(elem::AND, ft602, ft618);
		raw_term rt621(raw_term::REL, t_arith_op::NOP, {e31, e1, e44, e2, });
		rt621.neg = false;
		sprawformtree ft620 = std::make_shared<raw_form_tree>(rt621);
		sprawformtree ft600 = std::make_shared<raw_form_tree>(elem::AND, ft601, ft620);
		raw_term rt623(raw_term::REL, t_arith_op::NOP, {e218, e1, e399, e168, e417, e2, });
		rt623.neg = false;
		sprawformtree ft622 = std::make_shared<raw_form_tree>(rt623);
		sprawformtree ft599 = std::make_shared<raw_form_tree>(elem::AND, ft600, ft622);
		raw_term rt625(raw_term::REL, t_arith_op::NOP, {e218, e1, e44, e168, e417, e2, });
		rt625.neg = false;
		sprawformtree ft624 = std::make_shared<raw_form_tree>(rt625);
		sprawformtree ft598 = std::make_shared<raw_form_tree>(elem::AND, ft599, ft624);
		raw_term rt627(raw_term::REL, t_arith_op::NOP, {e10, e1, e2, });
		rt627.neg = false;
		sprawformtree ft626 = std::make_shared<raw_form_tree>(rt627);
		sprawformtree ft597 = std::make_shared<raw_form_tree>(elem::AND, ft598, ft626);
		raw_rule rr628({rt596, }, ft597);
		raw_term rt629(raw_term::REL, t_arith_op::NOP, {e271, e1, e272, e273, e44, e2, });
		rt629.neg = false;
		raw_term rt634(raw_term::ARITH, t_arith_op::ADD, {e268, e59, e60, e61, e272, });
		rt634.neg = false;
		sprawformtree ft633 = std::make_shared<raw_form_tree>(rt634);
		raw_term rt636(raw_term::REL, t_arith_op::NOP, {e286, e1, e268, e2, });
		rt636.neg = false;
		sprawformtree ft635 = std::make_shared<raw_form_tree>(rt636);
		sprawformtree ft632 = std::make_shared<raw_form_tree>(elem::AND, ft633, ft635);
		raw_term rt638(raw_term::REL, t_arith_op::NOP, {e424, e1, e268, e273, e44, e2, });
		rt638.neg = false;
		sprawformtree ft637 = std::make_shared<raw_form_tree>(rt638);
		sprawformtree ft631 = std::make_shared<raw_form_tree>(elem::AND, ft632, ft637);
		raw_term rt640(raw_term::REL, t_arith_op::NOP, {e10, e1, e2, });
		rt640.neg = false;
		sprawformtree ft639 = std::make_shared<raw_form_tree>(rt640);
		sprawformtree ft630 = std::make_shared<raw_form_tree>(elem::AND, ft631, ft639);
		raw_rule rr641({rt629, }, ft630);
		raw_term rt642(raw_term::REL, t_arith_op::NOP, {e271, e1, e272, e273, e44, e2, });
		rt642.neg = false;
		raw_term rt648(raw_term::ARITH, t_arith_op::ADD, {e268, e59, e60, e61, e272, });
		rt648.neg = false;
		sprawformtree ft647 = std::make_shared<raw_form_tree>(rt648);
		raw_term rt650(raw_term::REL, t_arith_op::NOP, {e286, e1, e268, e2, });
		rt650.neg = false;
		sprawformtree ft649 = std::make_shared<raw_form_tree>(rt650);
		sprawformtree ft646 = std::make_shared<raw_form_tree>(elem::AND, ft647, ft649);
		raw_term rt653(raw_term::REL, t_arith_op::NOP, {e472, e1, e268, e273, e44, e2, });
		rt653.neg = false;
		sprawformtree ft652 = std::make_shared<raw_form_tree>(rt653);
		sprawformtree ft651 = std::make_shared<raw_form_tree>(elem::NOT, ft652);
		sprawformtree ft645 = std::make_shared<raw_form_tree>(elem::AND, ft646, ft651);
		raw_term rt655(raw_term::REL, t_arith_op::NOP, {e523, e1, e268, e273, e44, e2, });
		rt655.neg = false;
		sprawformtree ft654 = std::make_shared<raw_form_tree>(rt655);
		sprawformtree ft644 = std::make_shared<raw_form_tree>(elem::AND, ft645, ft654);
		raw_term rt657(raw_term::REL, t_arith_op::NOP, {e10, e1, e2, });
		rt657.neg = false;
		sprawformtree ft656 = std::make_shared<raw_form_tree>(rt657);
		sprawformtree ft643 = std::make_shared<raw_form_tree>(elem::AND, ft644, ft656);
		raw_rule rr658({rt642, }, ft643);
		raw_term rt659(raw_term::REL, t_arith_op::NOP, {e271, e1, e272, e273, e44, e2, });
		rt659.neg = true;
		raw_term rt664(raw_term::ARITH, t_arith_op::ADD, {e268, e59, e60, e61, e272, });
		rt664.neg = false;
		sprawformtree ft663 = std::make_shared<raw_form_tree>(rt664);
		raw_term rt666(raw_term::REL, t_arith_op::NOP, {e286, e1, e268, e2, });
		rt666.neg = false;
		sprawformtree ft665 = std::make_shared<raw_form_tree>(rt666);
		sprawformtree ft662 = std::make_shared<raw_form_tree>(elem::AND, ft663, ft665);
		raw_term rt668(raw_term::REL, t_arith_op::NOP, {e472, e1, e268, e273, e44, e2, });
		rt668.neg = false;
		sprawformtree ft667 = std::make_shared<raw_form_tree>(rt668);
		sprawformtree ft661 = std::make_shared<raw_form_tree>(elem::AND, ft662, ft667);
		raw_term rt670(raw_term::REL, t_arith_op::NOP, {e10, e1, e2, });
		rt670.neg = false;
		sprawformtree ft669 = std::make_shared<raw_form_tree>(rt670);
		sprawformtree ft660 = std::make_shared<raw_form_tree>(elem::AND, ft661, ft669);
		raw_rule rr671({rt659, }, ft660);
		raw_term rt672(raw_term::REL, t_arith_op::NOP, {e267, e1, e268, e269, e44, e2, });
		rt672.neg = false;
		raw_term rt675(raw_term::REL, t_arith_op::NOP, {e280, e1, e268, e269, e44, e2, });
		rt675.neg = false;
		sprawformtree ft674 = std::make_shared<raw_form_tree>(rt675);
		raw_term rt677(raw_term::REL, t_arith_op::NOP, {e10, e1, e2, });
		rt677.neg = false;
		sprawformtree ft676 = std::make_shared<raw_form_tree>(rt677);
		sprawformtree ft673 = std::make_shared<raw_form_tree>(elem::AND, ft674, ft676);
		raw_rule rr678({rt672, }, ft673);
		raw_term rt679(raw_term::REL, t_arith_op::NOP, {e275, e1, e268, e272, e2, });
		rt679.neg = false;
		raw_term rt686(raw_term::LEQ, t_arith_op::NOP, {e272, e540, e268, });
		rt686.neg = false;
		sprawformtree ft685 = std::make_shared<raw_form_tree>(rt686);
		sprawformtree ft684 = std::make_shared<raw_form_tree>(elem::NOT, ft685);
		raw_term rt688(raw_term::REL, t_arith_op::NOP, {e286, e1, e268, e2, });
		rt688.neg = false;
		sprawformtree ft687 = std::make_shared<raw_form_tree>(rt688);
		sprawformtree ft683 = std::make_shared<raw_form_tree>(elem::AND, ft684, ft687);
		raw_term rt690(raw_term::REL, t_arith_op::NOP, {e286, e1, e272, e2, });
		rt690.neg = false;
		sprawformtree ft689 = std::make_shared<raw_form_tree>(rt690);
		sprawformtree ft682 = std::make_shared<raw_form_tree>(elem::AND, ft683, ft689);
		raw_term rt693(raw_term::REL, t_arith_op::NOP, {e531, e1, e268, e272, e2, });
		rt693.neg = false;
		sprawformtree ft692 = std::make_shared<raw_form_tree>(rt693);
		sprawformtree ft691 = std::make_shared<raw_form_tree>(elem::NOT, ft692);
		sprawformtree ft681 = std::make_shared<raw_form_tree>(elem::AND, ft682, ft691);
		raw_term rt695(raw_term::REL, t_arith_op::NOP, {e10, e1, e2, });
		rt695.neg = false;
		sprawformtree ft694 = std::make_shared<raw_form_tree>(rt695);
		sprawformtree ft680 = std::make_shared<raw_form_tree>(elem::AND, ft681, ft694);
		raw_rule rr696({rt679, }, ft680);
		raw_prog &rp697 = rp;
		rp697.r.insert(rp697.r.end(), { rr12, rr17, rr22, rr30, rr35, rr40, rr78, rr94, rr119, rr129, rr156, rr166, rr191, rr207, rr217, rr240, rr256, rr266, rr279, rr296, rr319, rr343, rr362, rr378, rr423, rr471, rr522, rr530, rr553, rr574, rr582, rr595, rr628, rr641, rr658, rr671, rr678, rr696, });
	}
	o::dbg() << "Generated eval for: " << drt << endl;
	return true;
}

/* Applies the given transformation on the given program in post-order.
 * I.e. the transformation is applied to the nested programs first and
 * then to the program proper. */

void driver::recursive_transform(raw_prog &rp,
		const function<void(raw_prog &)> &f) {
	for(raw_prog &np : rp.nps) {
		recursive_transform(np, f);
	}
	f(rp);
}

/* Checks if the relation the first rule belongs to precedes the
 * relation that the second rule belongs to. A relation precedes another
 * relation if its name precedes the other relation's name. In the case
 * of a tie, a relation precedes another relation if its arity is lower
 * than the other's. */

bool rule_relation_precedes(const raw_rule &rr1, const raw_rule &rr2) {
	if(rr1.h[0].e[0] == rr2.h[0].e[0]) {
		return rr1.h[0].e.size() < rr2.h[0].e.size();
	} else {
		return rr1.h[0].e[0] < rr2.h[0].e[0];
	}
}

/* Convenience function for creating most general rule head for the
 * given relation. */

raw_term driver::relation_to_term(const rel_info &ri) {
	// Get dictionary for generating fresh symbols
	dict_t &d = tbl->get_dict();
	
	vector<elem> els = { get<0>(ri), elem_openp };
	for(int_t i = 0; i < get<1>(ri); i++) {
		els.push_back(elem::fresh_var(d));
	}
	els.push_back(elem_closep);
	return raw_term(els);
}

/* Convenience function to condition the given rule with the given
 * condition term. */

raw_rule condition_rule(raw_rule rr, const raw_term &cond) {
	if(rr.b.empty()) {
		rr.b.push_back({cond});
	} else {
		for(vector<raw_term> &bodie : rr.b) {
			bodie.push_back(cond);
		}
	}
	return rr;
}

/* Rename the relations in the heads of the given rule to that given by
 * the supplied renaming map. */

raw_rule rename_rule(raw_rule rr, map<elem, elem> &rename_map) {
	for(raw_term &rt : rr.h) {
		auto jt = rename_map.find(rt.e[0]);
		if(jt != rename_map.end()) {
			rt.e[0] = jt->second;
		}
	}
	return rr;
}

/* Applies the given transformation to the given program in such a way
 * that it completes in a single step. Does this by separating the given
 * program into an execute and a writeback stage which serves to stop
 * the construction of the next database from interfering with the
 * execution of the current stage. */

void driver::step_transform(raw_prog &rp,
		const function<void(raw_prog &)> &f) {
	// Get dictionary for generating fresh symbols
	dict_t &d = tbl->get_dict();
	
	map<elem, elem> freeze_map;
	map<elem, elem> unfreeze_map;
	// Separate the internal rules used to execute the parts of the
	// transformation from the external rules used to expose the results
	// of computation.
	vector<raw_rule> int_prog;
	vector<raw_term> fact_prog;
	vector<raw_term> goal_prog;
	// Create a duplicate of each rule in the given program under a
	// generated alias.
	for(raw_rule rr : rp.r) {
		if(rr.type == raw_rule::GOAL) {
			// Separate out program goals as these are applied after
			// computation
			goal_prog.insert(goal_prog.end(), rr.h.begin(), rr.h.end());
			continue;
		}
		for(raw_term &rt : rr.h) {
			if(auto it = freeze_map.find(rt.e[0]); it != freeze_map.end()) {
				rt.e[0] = it->second;
			} else {
				elem frozen_elem = elem::fresh_temp_sym(d);
				// Store the mapping so that the derived portion of each
				// relation is stored in exactly one place
				unfreeze_map[frozen_elem] = rt.e[0];
				rt.e[0] = freeze_map[rt.e[0]] = frozen_elem;
			}
			rp.hidden_rels.insert({ rt.e[0].e, rt.arity });
		}
		if(rr.is_fact()) {
			// Separate out program facts as they need to be in database by
			// 0th step
			fact_prog.insert(fact_prog.end(), rr.h.begin(), rr.h.end());
		} else {
			int_prog.push_back(rr);
		}
	}
	// Apply the modifications from the above loop
	rp.r = int_prog;
	// Execute the transformation on the renamed rules.
	f(rp);

	// Partition the rules by relations
	typedef set<raw_rule> relation;
	map<rel_info, relation> rels;
	for(const raw_rule &rr : rp.r) {
		rels[get_relation_info(rr.h[0])].insert(rr);
	}
	map<const relation *, rel_info> rrels;
	for(const auto &[ri, r] : rels) {
		rrels[&r] = ri;
	}
	// Initialize the dependency lists
	map<const relation *, set<const relation *>> deps, rdeps;
	for(const auto &[k, v] : rels) {
		deps[&v] = {};
		rdeps[&v] = {};
	}
	// Make the adjacency lists based on rule dependency
	for(const auto &[k, v] : rels) {
		for(const raw_rule &rr : v) {
			for(const vector<raw_term> &bodie : rr.b) {
				for(const raw_term &rt : bodie) {
					rel_info target = get_relation_info(rt);
					if(rels.find(target) != rels.end()) {
						// Store the edges in both directions so that reverse
						// lookups are easy
						deps[&rels[target]].insert(&v);
						rdeps[&v].insert(&rels[target]);
					}
				}
			}
		}
	}
	// Topologically sort the relations
	vector<set<const relation *>> sorted;
	// Represents the relations that do not depend on other relations
	set<const relation *> current_level;
	for(const auto &[k, v] : rdeps) {
		if(v.empty()) {
			current_level.insert(k);
		}
	}
	// Kahn's algorithm: start from relations with no dependencies and
	// work our way up
	while(!current_level.empty()) {
		set<const relation *> next_level;
		for(const relation *n : current_level) {
			for(const relation *m : deps[n]) {
				rdeps[m].erase(n);
				if(rdeps[m].empty()) {
					next_level.insert(m);
				}
			}
			deps[n].clear();
		}
		sorted.push_back(current_level);
		current_level = next_level;
	}
	// If there are interdependencies between rules
	if(sorted.size() > 1) {
		rp.r.clear();
		// First add all the facts back into the sequenced program
		for(const raw_term &rt : fact_prog) {
			// If the fact is in a relation that is sequenced
			if(rels.find(get_relation_info(rt)) != rels.end()) {
				// Add it under its internal name, for we will create rule that
				// copies the internal relation to the external
				rp.r.push_back(raw_rule(rt));
			} else {
				// Add it under its external name because no rules will be
				// created to copy it
				rp.r.push_back(rename_rule(raw_rule(rt), unfreeze_map));
			}
		}
		// At each stage of TML execution, exactly one of the nullary facts
		// in this vector are asserted
		vector<elem> clock_states = { elem::fresh_temp_sym(d) };
		// Push the internal rules onto the program using conditioning to
		// control execution order
		for(const set<const relation *> v : sorted) {
			// Make a new clock state for the current stage
			const elem clock_state = elem::fresh_temp_sym(d);
			// If the previous state is asserted, then de-assert it and assert
			// this state
			rp.r.push_back(raw_rule(raw_term(clock_state, vector<elem>{}),
				{ raw_term(clock_states.back(), vector<elem>{}) }));
			rp.r.push_back(raw_rule(raw_term(clock_states.back(), vector<elem>{}).negate(),
				{ raw_term(clock_states.back(), vector<elem>{}) }));
			clock_states.push_back(clock_state);

			for(const relation *w : v) {
				raw_term general_head = relation_to_term(rrels[w]);
				// If the present relation does not correspond to a relation in
				// the original program, then clear the table so it does not
				// affect future stages.
				if(unfreeze_map.find(general_head.e[0]) == unfreeze_map.end()) {
					rp.r.push_back(raw_rule(general_head.negate(),
						{ general_head, raw_term(clock_states[0], vector<elem>{}) }));
				} else {
					// Update the external interface during the writeback stage
					// by copying the contents of the final temporary relation
					// back to the external interface.
					raw_term original_head = general_head;
					original_head.e[0] = unfreeze_map[general_head.e[0]];
					original_head.neg = general_head.neg = true;
					rp.r.push_back(condition_rule(raw_rule(original_head, general_head),
						raw_term(clock_states[0], vector<elem>{})));
					original_head.neg = general_head.neg = false;
					rp.r.push_back(condition_rule(raw_rule(original_head, general_head),
						raw_term(clock_states[0], vector<elem>{})));
				}
				for(raw_rule rr : *w) {
					// Condition everything in the current stage with the same
					// clock state
					rp.r.push_back(condition_rule(rr,
						raw_term(clock_state, vector<elem>{})));
				}
			}
		}
		// Start the clock ticking by asserting stage0, asserting stage1
		// if stage0 holds, and asserting the clock if stage0 holds but
		// stage1 does not.
		raw_term stage0(elem::fresh_temp_sym(d), vector<elem>{});
		raw_term stage1(elem::fresh_temp_sym(d), vector<elem>{});
		raw_term stage2(clock_states[0], vector<elem>{});
		rp.r.push_back(raw_rule(stage0));
		rp.r.push_back(raw_rule(stage1, stage0));
		rp.r.push_back(raw_rule(stage2, {stage0, stage1.negate()}));
		
		// Hide the clock states
		rp.hidden_rels.insert({ stage0.e[0].e, stage0.arity });
		rp.hidden_rels.insert({ stage1.e[0].e, stage1.arity });
		for(const elem &clock_state : clock_states) {
			rp.hidden_rels.insert({ clock_state.e, {0} });
		}
		
		if(clock_states.size() > 1) {
			// If the previous state is asserted, then de-assert it and assert
			// this state
			rp.r.push_back(raw_rule(raw_term(clock_states[0], vector<elem>{}),
				{ raw_term(clock_states.back(), vector<elem>{}) }));
			rp.r.push_back(raw_rule(raw_term(clock_states.back(), vector<elem>{}).negate(),
				{ raw_term(clock_states.back(), vector<elem>{}) }));
		}
	} else {
		// Add all program facts back
		for(const raw_term &rt : fact_prog) {
			rp.r.push_back(raw_rule(rt));
		}
		// If there are no interdepencies then we can just restore the
		// original rule names to the transformed program
		for(raw_rule &rr : rp.r) {
			rr = rename_rule(rr, unfreeze_map);
		}
	}
	// Add all program goals back
	for(const raw_term &rt : goal_prog) {
		rp.r.push_back(raw_rule(raw_rule::GOAL, rt));
	}
}

/* Iterate through the FOL rules and remove the outermost existential
 * quantifiers. Required because pure TML conversion assumes that
 * quantifier variables are only visible within their bodies. */

void driver::remove_redundant_exists(raw_prog &rp) {
	for(raw_rule &rr : rp.r) {
		if(rr.is_form()) {
			sprawformtree &prft = rr.prft;
			// Repeatedly strip outermost existential quantifier
			while(prft->type == elem::EXISTS) {
				prft = prft->r;
			}
		}
	}
}

/* Returns the difference between the two given sets. I.e. the second
 * set removed with multiplicity from the first. */

set<elem> set_difference(const multiset<elem> &s1,
		const set<elem> &s2) {
	set<elem> res;
	set_difference(s1.begin(), s1.end(), s2.begin(), s2.end(),
		inserter(res, res.end()));
	return res;
}

/* Returns the intersection of the two given sets. I.e. all the elems
 * that occur in both sets. */

set<elem> set_intersection(const set<elem> &s1, const set<elem> &s2) {
	set<elem> res;
	set_intersection(s1.begin(), s1.end(), s2.begin(), s2.end(),
		inserter(res, res.end()));
	return res;
}

/* Make a term with behavior equivalent to the supplied first order
 * logic formula with the given bound variables. This might involve
 * adding temporary relations to the given program. */

raw_term driver::to_pure_tml(const sprawformtree &t,
		raw_prog &rp, const set<elem> &fv) {
	// Get dictionary for generating fresh symbols
	dict_t &d = tbl->get_dict();
	const elem part_id = elem::fresh_temp_sym(d);

	switch(t->type) {
		case elem::IMPLIES: case elem::COIMPLIES: case elem::UNIQUE:
			// Process the expanded formula instead
			return to_pure_tml(expand_formula_node(t, d), rp, fv);
		case elem::AND: {
			// Collect all the conjuncts within the tree top
			vector<sprawformtree> ands;
			flatten_associative(elem::AND, t, ands);
			// Collect the free variables in each conjunct. The intersection
			// of variables between one and the rest is what will need to be
			// exported
			multiset<elem> all_vars(fv.begin(), fv.end());
			map<const sprawformtree, set<elem>> fvs;
			for(const sprawformtree &tree : ands) {
				fvs[tree] = collect_free_vars(tree);
				all_vars.insert(fvs[tree].begin(), fvs[tree].end());
			}
			vector<raw_term> terms;
			// And make a pure TML formula listing them
			for(const sprawformtree &tree : ands) {
				set<elem> nv = set_intersection(fvs[tree],
					set_difference(all_vars, fvs[tree]));
				terms.push_back(to_pure_tml(tree, rp, nv));
			}
			// Make the representative rule and add to the program
			raw_rule nr(raw_term(part_id, fv), terms);
			rp.r.push_back(nr);
			// Hide this new auxilliary relation
			rp.hidden_rels.insert({ nr.h[0].e[0].e, nr.h[0].arity });
			break;
		} case elem::ALT: {
			// Collect all the disjuncts within the tree top
			vector<sprawformtree> alts;
			flatten_associative(elem::ALT, t, alts);
			for(const sprawformtree &tree : alts) {
				// Make a separate rule for each disjunct
				raw_rule nr(raw_term(part_id, fv), to_pure_tml(tree, rp, fv));
				rp.r.push_back(nr);
				// Hide this new auxilliary relation
				rp.hidden_rels.insert({ nr.h[0].e[0].e, nr.h[0].arity });
			}
			break;
		} case elem::NOT: {
			return to_pure_tml(t->l, rp, fv).negate();
		} case elem::EXISTS: {
			// Make the proposition that is being quantified
			set<elem> nfv = fv;
			sprawformtree current_formula;
			set<elem> qvars;
			// Get all the quantified variables used in a sequence of
			// existential quantifiers
			for(current_formula = t;
					current_formula->type == elem::EXISTS;
					current_formula = current_formula->r) {
				qvars.insert(*(current_formula->l->el));
			}
			nfv.insert(qvars.begin(), qvars.end());
			// Convert the body occuring within the nested quantifiers into
			// pure TML
			raw_term nrt = to_pure_tml(current_formula, rp, nfv);
			// Make the rule corresponding to this existential formula
			for(const elem &e : qvars) {
				nfv.erase(e);
			}
			raw_rule nr(raw_term(part_id, nfv), nrt);
			rp.r.push_back(nr);
			// Hide this new auxilliary relation
			rp.hidden_rels.insert({ nr.h[0].e[0].e, nr.h[0].arity });
			return raw_term(part_id, nfv);
		} case elem::NONE: {
			return *t->rt;
		} case elem::FORALL: {
			sprawformtree current_formula;
			set<elem> qvars;
			// Get all the quantified variables used in a sequence of
			// existential quantifiers
			for(current_formula = t;
					current_formula->type == elem::FORALL;
					current_formula = current_formula->r) {
				qvars.insert(*(current_formula->l->el));
			}
			// The universal quantifier is logically equivalent to the
			// following (forall ?x forall ?y = ~ exists ?x exists ?y ~)
			sprawformtree equiv_formula =
				make_shared<raw_form_tree>(elem::NOT, current_formula);
			for(const elem &qvar : qvars) {
				equiv_formula = make_shared<raw_form_tree>(elem::EXISTS,
					make_shared<raw_form_tree>(qvar), equiv_formula);
			}
			return to_pure_tml(make_shared<raw_form_tree>(elem::NOT,
				equiv_formula), rp, fv);
		} default:
			assert(false); //should never reach here
	}
	return raw_term(part_id, fv);
}

/* Convert every rule in the given program to pure TML rules. Rules with
 * multiple heads are also converted to multiple rules with single
 * heads. */

void driver::to_pure_tml(raw_prog &rp) {
	// Convert all FOL formulas to P-DATALOG
	for(int_t i = rp.r.size() - 1; i >= 0; i--) {
		raw_rule rr = rp.r[i];
		if(rr.is_form()) {
			rr.set_b({{to_pure_tml(rr.prft, rp, collect_free_vars(rr))}});
		}
		rp.r[i] = rr;
	}
	// Split rules with multiple heads and delete those with 0 heads
	for(auto it = rp.r.begin(); it != rp.r.end();) {
		if(it->h.size() != 1) {
			// 0 heads are effectively eliminated, and multiple heads are
			// split up.
			const raw_rule rr = *it;
			it = rp.r.erase(it);
			for(const raw_term &rt : rr.h) {
				it = rp.r.insert(it, raw_rule(rt, rr.b));
			}
		} else {
			// Leave the single-headed rules alone.
			it++;
		}
	}
}

/* If the given term belongs to a hidden relation, record its relation
 * in signatures and record the given rule's dependency on this term's
 * relation. */

void record_hidden_relation(const raw_prog &rp, raw_rule &rr,
		const raw_term &rt, set<signature> &signatures,
		map<signature, set<raw_rule *>> &dependants) {
	if(rt.extype == raw_term::REL) {
		if(signature sig = get_signature(rt); has(rp.hidden_rels, sig)) {
			dependants[sig].insert(&rr);
			signatures.insert(sig);
		}
	}
}

/* Update the variable usage map by 1 (see below) for each distinct
 * variable occuring in the given term. Record the distinct variables in
 * the given pointer if it is not null. Note that the update is 2 for
 * symbols as they are treated as a unique variable with a separate
 * equality contraint to fix it to a particular symbol. */

void record_variable_usage(const raw_term &rt,
		map<elem, int_t> &var_usages, set<elem> *relevant_vars) {
	set<elem> unique_vars;
	for(const elem &e : rt.e) unique_vars.insert(e);
	signature body_signature = get_signature(rt);
	if(relevant_vars)
		for(const elem &e : rt.e) relevant_vars->insert(e);
	for(const elem &e : unique_vars)
		var_usages[e] += e.type == elem::VAR ? 1 : 2;
}

/* There are four kinds of rules to deal with: those in which the
 * signature being modified occurs only within the body, those in which
 * it occurs only within the head, and those within which it occurs in
 * both. If it only occurs in the head, then the use of each head
 * variable should be 0/1, as this would allow all the head variables to
 * be eliminated without affecting computation. If it only occurs in the
 * body, then the use of each variable occuring in terms of the
 * signature being modified should be set to the number of separate
 * terms that use the variable. This way all those variables occuring
 * only in one term and hence do not affect the satisfiability of the
 * current rule nor the derived term can be eliminated. If it occurs in
 * both, then the occurence of variables in the head can be ignored
 * because this does not affect the rule's satisfiability and because we
 * want these variables to be eliminatable. However the number of
 * separate terms the variables occuring in terms corresponding to the
 * signature under modification should still be recorded as this does
 * affect satisfiability. */

ints calculate_variable_usage(const signature &sig,
		const map<signature, set<raw_rule *>> &dependants) {
	// This variable stores the number of separate terms each
	// position of the given relation is simultaneously used in.
	// Important for determining whether a given position is
	// eliminatable.
	ints uses(sig.second[0], 1);
	// The eliminatability of a relation position is entirely
	// determined by how it is used in the rules that depend on its
	// relation
	for(const raw_rule *rr : dependants.at(sig)) {
		map<elem, int_t> var_usages;
		// Record the variables occuring in the head if the head
		// relation is distinct from the one currently being modified.
		// Variable exportation would prevent us from deleting this
		// variable in the body.
		const raw_term &head = rr->h[0];
		const signature &head_signature = get_signature(head);
		if(sig != head_signature)
			record_variable_usage(head, var_usages, nullptr);
		// The set of all the variables use by terms of this relation
		// occuring in the body. If no such terms exist, then the term
		// of this relation must occur in the head, in which case every
		// position of this relation could be eliminatable.
		set<elem> relevant_vars;
		// Now record also the number of separate conjuncts each
		// variable occurs in whilst populating relevant_vars according
		// to its specification.
		if(!rr->b.empty()) for(const raw_term &rt : rr->b[0])
			record_variable_usage(rt, var_usages,
				get_signature(rt) == sig ? &relevant_vars : nullptr);
		// Now eliminate the irrelevant variables. These are the
		// variables that do not affect the current rule's
		// satisfiability through terms of the relation currently being
		// minimized.
		if(sig == head_signature)
			for(auto &[var, count] : var_usages)
				if(!has(relevant_vars, var)) count = 0;
		// Now assign the most pessimistic variable usages to each position
		// in the signature under modification.
		if(head.extype == raw_term::REL && sig == head_signature)
			for(size_t i = 0; i < head.e.size() - 3; i++)
				uses[i] = max(uses[i], var_usages[head.e[i+2]]);
		if(!rr->b.empty()) for(const raw_term &rt : rr->b[0])
			if(rt.extype == raw_term::REL && sig == make_pair(rt.e[0].e, rt.arity))
				for(size_t i = 0; i < rt.e.size() - 3; i++)
					uses[i] = max(uses[i], var_usages[rt.e[i+2]]);
	}
	return uses;
}

/* Delete the elements of the given term that have a usage of equal to
 * one if the term's signature equals the one supplied. Otherwise if
 * there is a usage equal to one, then add the term's signature to
 * pending because it may have a contraction after the given signature
 * is done. */

void contract_term(raw_term &rt, const elem &new_rel, const ints &uses,
		const signature &sig, set<signature> &pending_signatures,
		raw_prog &rp) {
	if(rt.extype == raw_term::REL &&
			find(uses.begin(), uses.end(), 1) != uses.end()) {
		signature body_signature = get_signature(rt);
		if(sig == body_signature) {
			rt.e[0] = new_rel;
			for(int_t i = uses.size() - 1; i >= 0; i--)
				if(uses[i] == 1) rt.e.erase(rt.e.begin() + 2 + i);
			rt.calc_arity(nullptr);
			if(auto it = pending_signatures.find(sig); it != pending_signatures.end()) {
				pending_signatures.erase(it);
				pending_signatures.insert(get_signature(rt));
			}
		} else if(has(rp.hidden_rels, body_signature)) {
			pending_signatures.insert(body_signature);
		}
	}
}

/* Eliminate unused elements of hidden relations. Do these by
 * identifying those relation elements that neither participate in
 * term conjunction nor are exported to visible relation. */

void driver::eliminate_dead_variables(raw_prog &rp) {
	// Get dictionary for generating fresh symbols
	dict_t &d = tbl->get_dict();
	// Before we can eliminate relation positions, we need to know what
	// rules depend on each relation. Knowing the dependants will allow us
	// to determine whether a certain position is significant, and if so
	// correct the call-sites to match the declaration.
	set<signature> pending_signatures;
	map<signature, set<raw_rule *>> dependants;
	for(raw_rule &rr : rp.r) {
		record_hidden_relation(rp, rr, rr.h[0], pending_signatures, dependants);
		if(!rr.b.empty()) for(const raw_term &rt : rr.b[0])
			record_hidden_relation(rp, rr, rt, pending_signatures, dependants);
	}
	// While there are still signatures to check for reducibility, grab
	// the entire set and try to reduce each relation making a note of
	// affected relations when successful.
	while(!pending_signatures.empty()) {
		// Grab pending signatures
		set<pair<lexeme, ints>> current_signatures = move(pending_signatures);
		for(const signature &sig : current_signatures) {
			// Calculate variable usages so we can know what to eliminate
			ints uses = calculate_variable_usage(sig, dependants);
			
			// Move forward only if there is something to contract
			if(find(uses.begin(), uses.end(), 1) != uses.end()) {
				// Print active variable usages for debugging purposes
				o::dbg() << "Contracting " << sig.first << " using [";
				const char *sep = "";
				for(int_t count : uses) {
					o::dbg() << sep << count;
					sep = ", ";
				}
				o::dbg() << "]" << endl;
				
				// Now consistently eliminate certain positions and prepare the
				// next round. Rename the relation after the eliminations in
				// case the new signature coincides with an already existing
				// one.
				elem new_rel = elem::fresh_temp_sym(d);
				for(raw_rule *rr : dependants.at(sig)) {
					contract_term(rr->h[0], new_rel, uses, sig, pending_signatures, rp);
					if(!rr->b.empty()) for(raw_term &rt : rr->b[0])
						contract_term(rt, new_rel, uses, sig, pending_signatures, rp);
				}
				// New signature consists of every variable used more than once
				signature new_sig(new_rel.e,
					{(int_t) count_if(uses.begin(), uses.end(), [](int_t x) { return x > 1; })});
				// Update the dependencies
				dependants[new_sig] = move(dependants.at(sig));
				dependants.erase(sig);
				rp.hidden_rels.insert(new_sig);
			}
		}
	}
	o::dbg() << endl;
}

void collect_free_vars(const vector<vector<raw_term>> &b,
		vector<elem> &bound_vars, set<elem> &free_vars) {
	for(const vector<raw_term> &bodie : b) {
		for(const raw_term &rt : bodie) {
			collect_free_vars(rt, bound_vars, free_vars);
		}
	}
}

set<elem> collect_free_vars(const vector<vector<raw_term>> &b) {
	vector<elem> bound_vars;
	set<elem> free_vars;
	collect_free_vars(b, bound_vars, free_vars);
	return free_vars;
}

/* Collect all the variables that are free in the given rule. */

void collect_free_vars(const raw_rule &rr, set<elem> &free_vars) {
	vector<elem> bound_vars = {};
	for(const raw_term &rt : rr.h) {
		collect_free_vars(rt, bound_vars, free_vars);
	}
	if(rr.is_form()) {
		collect_free_vars(rr.prft, bound_vars, free_vars);
	} else {
		collect_free_vars(rr.b, bound_vars, free_vars);
	}
}

set<elem> collect_free_vars(const raw_rule &rr) {
	set<elem> free_vars;
	collect_free_vars(rr, free_vars);
	return free_vars;
}

/* Collect all the variables that are free in the given term. */

set<elem> collect_free_vars(const raw_term &t) {
	set<elem> free_vars;
	vector<elem> bound_vars = {};
	collect_free_vars(t, bound_vars, free_vars);
	return free_vars;
}

void collect_free_vars(const raw_term &t, vector<elem> &bound_vars,
		set<elem> &free_vars) {
	set<elem> term_vars;
	// Get all the variables used in t
	collect_vars(t, term_vars);
	// If the variable is bound by some quantifier, then it cannot be free
	for(const elem &bv : bound_vars) term_vars.erase(bv);
	// Now term_vars only has free variables; add those to free_vars
	for(const elem &tv : term_vars) free_vars.insert(tv);
}

/* Collect all the variables that are free in the given tree. */

set<elem> collect_free_vars(const sprawformtree &t) {
	set<elem> free_vars;
	vector<elem> bound_vars = {};
	collect_free_vars(t, bound_vars, free_vars);
	return free_vars;
}

void collect_free_vars(const sprawformtree &t, vector<elem> &bound_vars,
		set<elem> &free_vars) {
	switch(t->type) {
		case elem::IMPLIES: case elem::COIMPLIES: case elem::AND:
		case elem::ALT:
			collect_free_vars(t->l, bound_vars, free_vars);
			collect_free_vars(t->r, bound_vars, free_vars);
			break;
		case elem::NOT:
			collect_free_vars(t->l, bound_vars, free_vars);
			break;
		case elem::EXISTS: case elem::UNIQUE: case elem::FORALL: {
			elem elt = *(t->l->el);
			bound_vars.push_back(elt);
			collect_free_vars(t->r, bound_vars, free_vars);
			bound_vars.pop_back();
			break;
		} case elem::NONE: {
			collect_free_vars(*t->rt, bound_vars, free_vars);
			break;
		} default:
			assert(false); //should never reach here
	}
}

/* It is sometimes desirable to embed a large amount of TML code into
 * this C++ codebase. Unfortunately, manually writing C++ code to
 * generate a certain TML fragment can be tedious. This pseudo-
 * transformation takes TML code and automatically produces the C++ code
 * necessary to generate the TML code. This transformation is used to
 * embed TML interpreter written in TML into this codebase. */

// Generate C++ code to generate the given elem

string_t driver::generate_cpp(const elem &e, string_t &prog_constr,
		uint_t &cid, const string_t &dict_name,
		map<elem, string_t> &elem_cache) {
	if(elem_cache.find(e) != elem_cache.end()) {
		return elem_cache[e];
	}
	string_t e_name = to_string_t("e") + to_string_t(to_string(cid++).c_str());
	elem_cache[e] = e_name;
	if(e.type == elem::CHR) {
		prog_constr += to_string_t("elem ") + e_name +
			to_string_t("(char32_t(") + to_string_t(to_string(e.ch).c_str()) +
			to_string_t("));\n");
	} else if(e.type == elem::NUM) {
		prog_constr += to_string_t("elem ") + e_name + to_string_t("(int_t(") +
			to_string_t(to_string(e.num).c_str()) + to_string_t("));\n");
	} else {
		prog_constr += to_string_t("elem ") + e_name + to_string_t("(") +
			to_string_t(
				e.type == elem::NONE ? "elem::NONE" :
				e.type == elem::SYM ? "elem::SYM" :
				e.type == elem::NUM ? "elem::NUM" :
				e.type == elem::CHR ? "elem::CHR" :
				e.type == elem::VAR ? "elem::VAR" :
				e.type == elem::OPENP ? "elem::OPENP" :
				e.type == elem::CLOSEP ? "elem::CLOSEP" :
				e.type == elem::ALT ? "elem::ALT" :
				e.type == elem::STR ? "elem::STR" :
				e.type == elem::EQ ? "elem::EQ" :
				e.type == elem::NEQ ? "elem::NEQ" :
				e.type == elem::LEQ ? "elem::LEQ" :
				e.type == elem::GT ? "elem::GT" :
				e.type == elem::LT ? "elem::LT" :
				e.type == elem::GEQ ? "elem::GEQ" :
				e.type == elem::BLTIN ? "elem::BLTIN" :
				e.type == elem::NOT ? "elem::NOT" :
				e.type == elem::AND ? "elem::AND" :
				e.type == elem::OR ? "elem::OR" :
				e.type == elem::FORALL ? "elem::FORALL" :
				e.type == elem::EXISTS ? "elem::EXISTS" :
				e.type == elem::UNIQUE ? "elem::UNIQUE" :
				e.type == elem::IMPLIES ? "elem::IMPLIES" :
				e.type == elem::COIMPLIES ? "elem::COIMPLIES" :
				e.type == elem::ARITH ? "elem::ARITH" :
				e.type == elem::OPENB ? "elem::OPENB" :
				e.type == elem::CLOSEB ? "elem::CLOSEB" :
				e.type == elem::OPENSB ? "elem::OPENSB" :
				e.type == elem::CLOSESB ? "elem::CLOSESB" : "") + to_string_t(", ") +
			to_string_t(
				e.arith_op == t_arith_op::NOP ? "t_arith_op::NOP" :
				e.arith_op == t_arith_op::ADD ? "t_arith_op::ADD" :
				e.arith_op == t_arith_op::SUB ? "t_arith_op::SUB" :
				e.arith_op == t_arith_op::MULT ? "t_arith_op::MULT" :
				e.arith_op == t_arith_op::BITWAND ? "t_arith_op::BITWAND" :
				e.arith_op == t_arith_op::BITWOR ? "t_arith_op::BITWOR" :
				e.arith_op == t_arith_op::BITWXOR ? "t_arith_op::BITWXOR" :
				e.arith_op == t_arith_op::BITWNOT ? "t_arith_op::BITWNOT" :
				e.arith_op == t_arith_op::SHR ? "t_arith_op::SHR" :
				e.arith_op == t_arith_op::SHL ? "t_arith_op::SHL" : "") +
			to_string_t(", ") + dict_name + to_string_t(".get_lexeme(\"") +
			lexeme2str(e.e) + to_string_t("\"));\n");
	}
	return e_name;
}

// Generate the C++ code to generate the given raw_term

string_t driver::generate_cpp(const raw_term &rt, string_t &prog_constr,
		uint_t &cid, const string_t &dict_name,
		map<elem, string_t> &elem_cache) {
	vector<string_t> elem_names;
	for(const elem &e : rt.e) {
		elem_names.push_back(generate_cpp(e, prog_constr, cid, dict_name, elem_cache));
	}
	string_t rt_name = to_string_t("rt") + to_string_t(to_string(cid++).c_str());
	prog_constr += to_string_t("raw_term ") + rt_name + to_string_t("(") +
		to_string_t(
			rt.extype == raw_term::REL ? "raw_term::REL" :
			rt.extype == raw_term::EQ ? "raw_term::EQ" :
			rt.extype == raw_term::LEQ ? "raw_term::LEQ" :
			rt.extype == raw_term::BLTIN ? "raw_term::BLTIN" :
			rt.extype == raw_term::ARITH ? "raw_term::ARITH" :
			rt.extype == raw_term::CONSTRAINT ? "raw_term::CONSTRAINT" : "") +
		to_string_t(", ") + to_string_t(
			rt.arith_op == t_arith_op::NOP ? "t_arith_op::NOP" :
			rt.arith_op == t_arith_op::ADD ? "t_arith_op::ADD" :
			rt.arith_op == t_arith_op::SUB ? "t_arith_op::SUB" :
			rt.arith_op == t_arith_op::MULT ? "t_arith_op::MULT" :
			rt.arith_op == t_arith_op::BITWAND ? "t_arith_op::BITWAND" :
			rt.arith_op == t_arith_op::BITWOR ? "t_arith_op::BITWOR" :
			rt.arith_op == t_arith_op::BITWXOR ? "t_arith_op::BITWXOR" :
			rt.arith_op == t_arith_op::BITWNOT ? "t_arith_op::BITWNOT" :
			rt.arith_op == t_arith_op::SHR ? "t_arith_op::SHR" :
			rt.arith_op == t_arith_op::SHL ? "t_arith_op::SHL" : "") +
		to_string_t(", {");
	for(const string_t &en : elem_names) {
		prog_constr += en + to_string_t(", ");
	}
	prog_constr += to_string_t("});\n");
	prog_constr += rt_name + to_string_t(".neg = ") +
		to_string_t(rt.neg ? "true" : "false") + to_string_t(";\n");
	return rt_name;
}

// Generate the C++ code to generate the raw_form_tree

string_t driver::generate_cpp(const sprawformtree &t, string_t &prog_constr,
		uint_t &cid, const string_t &dict_name, map<elem, string_t> &elem_cache) {
	string_t ft_name = to_string_t("ft") + to_string_t(to_string(cid++).c_str());
	switch(t->type) {
		case elem::IMPLIES: case elem::COIMPLIES: case elem::AND:
		case elem::ALT: case elem::EXISTS: case elem::UNIQUE:
		case elem::FORALL: {
			string_t lft_name =
				generate_cpp(t->l, prog_constr, cid, dict_name, elem_cache);
			string_t rft_name = generate_cpp(t->r, prog_constr, cid, dict_name,
				elem_cache);
			string_t t_string = to_string_t(
				t->type == elem::IMPLIES ? "elem::IMPLIES" :
				t->type == elem::COIMPLIES ? "elem::COIMPLIES" :
				t->type == elem::AND ? "elem::AND" :
				t->type == elem::ALT ? "elem::ALT" :
				t->type == elem::EXISTS ? "elem::EXISTS" :
				t->type == elem::UNIQUE ? "elem::UNIQUE" :
				t->type == elem::FORALL ? "elem::FORALL" : "");
			prog_constr += to_string_t("sprawformtree ") + ft_name + to_string_t(" = "
				"std::make_shared<raw_form_tree>(") + t_string + to_string_t(", ") +
				lft_name + to_string_t(", ") + rft_name + to_string_t(");\n");
			break;
		} case elem::NOT: {
			string_t body_name = generate_cpp(t->l, prog_constr, cid, dict_name,
				elem_cache);
			prog_constr += to_string_t("sprawformtree ") + ft_name + to_string_t(" = "
				"std::make_shared<raw_form_tree>(elem::NOT, ") +
				body_name + to_string_t(");\n");
			break;
		} case elem::NONE: {
			string_t term_name = generate_cpp(*t->rt, prog_constr, cid, dict_name,
				elem_cache);
			prog_constr += to_string_t("sprawformtree ") + ft_name + to_string_t(" = "
				"std::make_shared<raw_form_tree>(") + term_name + to_string_t(");\n");
			break;
		} case elem::VAR: {
			string_t var_name = generate_cpp(*t->el, prog_constr, cid, dict_name,
				elem_cache);
			prog_constr += to_string_t("sprawformtree ") + ft_name + to_string_t(" = "
				"std::make_shared<raw_form_tree>(elem::VAR, ") +
				var_name + to_string_t(");\n");
			break;
		} default:
			assert(false); //should never reach here
	}
	return ft_name;
}

// Generate the C++ code to generate the given TML rule

string_t driver::generate_cpp(const raw_rule &rr, string_t &prog_constr,
		uint_t &cid, const string_t &dict_name,
		map<elem, string_t> &elem_cache, const raw_term &false_term) {
	vector<string_t> term_names;
	for(const raw_term &rt : rr.h) {
		term_names.push_back(
			generate_cpp(rt, prog_constr, cid, dict_name, elem_cache));
	}
	string_t prft_name = generate_cpp(rr.get_prft(false_term),
		prog_constr, cid, dict_name, elem_cache);
	string_t rule_name = to_string_t("rr") + to_string_t(to_string(cid++).c_str());
	prog_constr += to_string_t("raw_rule ") + rule_name + to_string_t("({");
	for(const string_t &tn : term_names) {
		prog_constr += tn + to_string_t(", ");
	}
	prog_constr += to_string_t("}, ");
	if(rr.is_fact()) {
		prog_constr += to_string_t("std::vector<raw_term> {}");
	} else {
		prog_constr += prft_name;
	}
	prog_constr += to_string_t(");\n");
	return rule_name;
}

// Generate the C++ code to generate the given TML program

string_t driver::generate_cpp(const raw_prog &rp, string_t &prog_constr,
		uint_t &cid, const string_t &dict_name,
		map<elem, string_t> &elem_cache, const raw_term &false_term) {
	vector<string_t> rule_names;
	for(const raw_rule &rr : rp.r) {
		rule_names.push_back(generate_cpp(rr, prog_constr, cid, dict_name,
			elem_cache, false_term));
	}
	string_t prog_name = to_string_t("rp") + to_string_t(to_string(cid++).c_str());
	prog_constr += to_string_t("raw_prog ") + prog_name + to_string_t(";\n");
	prog_constr += prog_name + to_string_t(".r.insert(") + prog_name +
		to_string_t(".r.end(), { ");
	for(const string_t &rn : rule_names) {
		prog_constr += rn + to_string_t(", ");
	}
	prog_constr += to_string_t("});\n");
	return prog_name;
}

/* Transform all the productions in the given program into pure TML
 * rules. Removes the original productions from the program and leaves
 * their pure TML equivalents behind. This function is only for
 * debugging purposes as the resulting raw_prog will not execute. */

bool driver::transform_grammar(raw_prog &rp) {
	form *tmp_form = nullptr;
	flat_prog p;
	
	if(ir->transform_grammar(rp.g, p, tmp_form)) {
		for(const vector<term> &rul : p) {
			vector<raw_term> bodie;
			for(size_t i = 1; i < rul.size(); i++) {
				bodie.push_back(ir->to_raw_term(rul[i]));
			}
			rp.r.push_back(raw_rule(ir->to_raw_term(rul[0]), bodie));
		}
		rp.g.clear();
		return true;
	} else {
		return false;
	}
}

bool driver::transform(raw_prog& rp, const strs_t& /*strtrees*/) {
	dict_t &d = tbl->get_dict();
	lexeme trel = { 0, 0 };
	// The false term is required to represent logical constants in FOL
	const raw_term false_term(elem::fresh_temp_sym(d), std::vector<elem> {});
	directives_load(rp, trel, false_term);
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
	get_all_vars(rp);
//	for (auto x : pd.strs)
//		if (!has(transformed_strings, x.first))
//			transform_string(x.second, rp.p[n], x.first),
//			transformed_strings.insert(x.first);
//	for (auto x : strtrees)
//		if (!has(transformed_strings, x.first))
//			transform_string(x.second, rp.p[n], x.first),
//			transformed_strings.insert(x.first);
	if (!rp.g.empty()) //{
		if (pd.strs.size() > 1)
			return throw_runtime_error(err_one_input);
//		else transform_grammar(rp.p[n], pd.strs.begin()->first,
//			pd.strs.begin()->second.size());
//	}
//	if (opts.enabled("sdt"))
//		for (raw_prog& p : rp.p)
//			p = transform_sdt(move(p));
	static set<raw_prog *> transformed_progs;
	if(transformed_progs.find(&rp) == transformed_progs.end()) {
		transformed_progs.insert(&rp);
		DBG(o::dbg() << "Pre-Transformation Program:" << endl << endl << rp << endl;)
		if(opts.enabled("program-gen")) {
			uint_t cid = 0;
			string_t rp_generator;
			map<elem, string_t> elem_cache;
			o::dbg() << "Generating Program Generator ..." << endl << endl;
			generate_cpp(rp, rp_generator, cid, to_string_t("d"), elem_cache,
				false_term);
			o::dbg() << "Program Generator:" << endl << endl
				<< to_string(rp_generator) << endl;
		}
#ifdef WITH_Z3
		if(opts.enabled("qc-subsume-z3")){
			o::dbg() << "Query containment subsumption using z3" << endl;
			simplify_formulas(rp, false_term);
			remove_redundant_exists(rp);
			z3_context z3_ctx;
			subsume_queries(rp,
				[&](const raw_rule &rr1, const raw_rule &rr2)
					{return check_qc_z3(rr1, rr2, false_term, z3_ctx);});
			o::dbg() << "Reduced program: " << endl << endl << rp << endl;
		}
#endif
		if(opts.enabled("cqnc-subsume") || opts.enabled("cqc-subsume") ||
				opts.enabled("cqc-factor") || opts.enabled("split-rules") ||
				opts.enabled("pure-tml")) {
			o::dbg() << "Simplifying Program ..." << endl << endl;
			simplify_formulas(rp, false_term);
			remove_redundant_exists(rp);
			o::dbg() << "Simplified Program:" << endl << endl << rp << endl;
			step_transform(rp, [&](raw_prog &rp) {
				// This transformation is a prerequisite to the CQC and binary
				// transformations, hence its more general activation condition.
				o::dbg() << "Converting to Pure TML ..." << endl << endl;
				to_pure_tml(rp);
				o::dbg() << "Pure TML Program:" << endl << endl << rp << endl;
				
				if(opts.enabled("cqnc-subsume")) {
					o::dbg() << "Subsuming using CQNC test ..." << endl << endl;
					subsume_queries(rp,
						[this](const raw_rule &rr1, const raw_rule &rr2)
							{return cqnc(rr1, rr2);});
					o::dbg() << "CQNC Subsumed Program:" << endl << endl << rp
						<< endl;
				}
				if(opts.enabled("cqc-subsume")) {
					o::dbg() << "Subsuming using CQC test ..." << endl << endl;
					subsume_queries(rp,
						[this](const raw_rule &rr1, const raw_rule &rr2)
							{return cqc(rr1, rr2);});
					o::dbg() << "CQC Subsumed Program:" << endl << endl << rp
						<< endl;
				}
				if(opts.enabled("cqc-factor")) {
					o::dbg() << "Factoring queries using CQC test ..." << endl
						<< endl;
					factor_rules(rp);
					o::dbg() << "Factorized Program:" << endl << endl << rp
						<< endl;
				}
				if(opts.enabled("split-rules")) {
					// Though this is a binary transformation, rules will become
					// ternary after timing guards are added
					o::dbg() << "Converting rules to unary form ..." << endl
						<< endl;
					transform_bin(rp);
					o::dbg() << "Binary Program:" << endl << endl << rp << endl;
				}
			});
			o::dbg() << "Step Transformed Program:" << endl << endl << rp
				<< endl;
			o::dbg() << "Eliminating dead variables ..." << endl << endl;
			eliminate_dead_variables(rp);
			o::dbg() << "Stripped TML Program:" << endl << endl << rp << endl;
		}
	}
//	if (trel[0]) transform_proofs(rp.p[n], trel);
	//o::out()<<rp.p[n]<<endl;
//	if (pd.bwd) rp.p.push_back(transform_bwd(rp.p[n]));
	for (auto& np : rp.nps) if (!transform(np, pd.strs)) return false;
	return true;
}

void driver::output_pl(const raw_prog& p) const {
	if (opts.enabled("xsb"))     print_xsb(o::to("xsb"), p);
	if (opts.enabled("swipl"))   print_swipl(o::to("swipl"), p);
	if (opts.enabled("souffle")) print_souffle(o::to("souffle"), p);
}

bool driver::prog_run(raw_prog& p, size_t steps, size_t break_on_step) {
//	pd.clear();
//	DBG(o::out() << "original program:"<<endl<<p;)
//	strtrees.clear(), get_dict_stats(rp.p[n]), add_rules(rp.p[n]);
	clock_t start, end;
	size_t step = nsteps();
	raw_prog::last_id = 0; // reset rp id counter;
	measure_time_start();
	if (opts.enabled("guards")) {
		tbl->transform_guards(p);
		if (opts.enabled("transformed")) o::to("transformed")
			<< "# after transform_guards:\n" << p << endl << endl;
	} else if (raw_prog::require_guards)
		return error = true,
			throw_runtime_error("Conditional statements require "
				"-g (-guards) option enabled.");
	bool fp = false;
	
	
	if (opts.enabled("bitunv")) {
		typechecker tc(p, true);
		if(tc.tcheck()) {
			bit_univ bu(tbl->get_dict(), opts.get_int("bitorder"));
			raw_prog brawp;
			bu.btransform(p, brawp);
			fp = tbl->run_prog(brawp, pd.strs, steps, break_on_step);
		}
	}
	else fp = tbl->run_prog(p, pd.strs, steps, break_on_step);
	o::ms() << "# elapsed: ";
	measure_time_end();
	if (tbl->error) error = true;
	pd.elapsed_steps = nsteps() - step;
//	for (auto x : prog->strtrees_out)
//		strtrees.emplace(x.first, get_trees(prog->pd.strtrees[x.first],
//					x.second, prog->rng.bits));
	return fp;
}

bool driver::add(input* in) {
	if (!rp.parse(in, tbl->get_dict())) return !(error = true);
	transform(rp.p, pd.strs);
	return true;
}

template <typename T>
void driver::list(std::basic_ostream<T>& os, size_t /*n*/) {
	os << rp.p << endl;
}
template void driver::list(std::basic_ostream<char>&, size_t);
template void driver::list(std::basic_ostream<wchar_t>&, size_t);

void driver::restart() {
	pd.n = 0;
	pd.start_step = nsteps();
	running = true;
}

bool driver::run(size_t steps, size_t break_on_step) {
	if (!running) restart();
	if (nsteps() == pd.start_step) {
		//transform(rp.p, pd.strs);
		//for (const string& s : str_bltins)
		//	rp.p.builtins.insert(get_lexeme(s));
		output_pl(rp.p);
	}
	if (opts.disabled("run") && opts.disabled("repl")) return true;
	bool fp = prog_run(rp.p, steps, break_on_step);
	if (fp) result = true;
	return fp;
}

bool driver::step(size_t steps, size_t break_on_step) {
	return run(steps, break_on_step);
}

template <typename T>
void driver::info(std::basic_ostream<T>& os) {
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

driver::driver(string s, const options &o) : rp(), opts(o) {

	// inject inputs from opts to driver and dict (needed for archiving)
	dict.set_inputs(ii = opts.get_inputs());
	dict.set_bitunv(opts.enabled("bitunv"));
	if (!ii) return;
	if (s.size()) opts.parse(strings{ "-ie", s });
	rt_options to;

	to.bproof            = opts.enabled("proof");
	to.optimize          = opts.enabled("optimize");
	to.print_transformed = opts.enabled("t");
	to.apply_regexpmatch = opts.enabled("regex");
	to.fp_step           = opts.enabled("fp");
	if(auto semantics_opt = opts.get("semantics"))
		to.semantics = semantics_opt->get_enum(map<string, enum semantics>
			{{"3pfp", semantics::pfp3}, {"pfp", semantics::pfp}});
	to.show_hidden       = opts.enabled("show-hidden");
	to.bitunv			 = opts.enabled("bitunv");
	to.bitorder          = opts.get_int("bitorder");

	//dict belongs to driver and is referenced by ir_builder and tables
	ir = new ir_builder(dict, to);
	tbl = new tables(dict, to, ir);
	ir->dynenv = tbl;
	ir->printer = tbl; //by now leaving printer component in tables, to be rafactored

	set_print_step(opts.enabled("ps"));
	set_print_updates(opts.enabled("pu"));
	set_populate_tml_update(opts.enabled("tml_update"));
	set_regex_level(opts.get_int("regex-level"));

	current_input = ii->first();
	if (current_input && !add(current_input)) return;
	read_inputs();
}

driver::driver(FILE *f, const options &o) : driver(input::file_read_text(f),o){}
driver::driver(string_t s, const options& o)    : driver(to_string(s), o) {}
driver::driver(const char *s, const options &o) : driver(string(s), o) {}
driver::driver(ccs   s, const options &o)       : driver(string_t(s), o) {}
driver::driver(const options &o)                : driver(string(), o) {}
driver::driver(string s)                        : driver(s, options()) {}
driver::driver(FILE *f)                         : driver(f, options()) {}
driver::driver(string_t s)                      : driver(to_string(s)) {}
driver::driver(const char *s)                   : driver(s, options()) {}
driver::driver(ccs s)                           : driver(string_t(s)) {}

driver::~driver() {
	if (tbl) delete tbl;
	if (ir) delete ir;
	for (auto x : strs_allocated) free((char *)x);
}
