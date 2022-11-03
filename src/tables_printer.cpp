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

#include "driver.h"

template <typename T>
void driver::out_goals(std::basic_ostream<T> os) {
	if (ts.goals.size()) {
		bdd_handles trues, falses, undefineds;
		// TODO Change this, fixpoint should be computed before
		// requesting to output the goals.
		if(compute_fixpoint(trues, falses, undefineds)) {
			for (term t : ts.goals) {
				ts.decompress(ts.trues[t.tab], t.tab, 
					[&os, &ir](const term& r) {
						os << ir.to_raw_term(r) << '.\n'; 
					});
			}
		}
	}
}

template <typename T>
void driver::out_fixpoint(std::basic_ostream<T> os) {
	bdd_handles trues, falses, undefineds;
	// TODO Change this, fixpoint should be computed before
	// requesting to output the fixpoint.
	if(compute_fixpoint(trues, falses, undefineds)) {
		for(ntable n = 0; n < (ntable)trues.size(); n++) {
			if(opts.show_hidden || !tbls[n].hidden) {
				decompress(trues[n], n, [&os, this](const term& r) {
					tp.notify_output(r);
				});
			}
		}
		return true;
	} else return false;
}

template <typename T>
void driver::out_proof(std::basic_ostream<T> os) {
	// Fact proofs are stored by level
	proof p(levels.size());
	set<term> s;
	// Record the facts covered by each goal
	for (term t : goals) {
		if(t.neg) {
			t.neg = false;
			// Collect all relation facts not matched by goal
			decompress(htrue % (from_fact(t) && tbls[t.tab].t), t.tab,
				[&](term t) { t.neg = true; if(is_term_valid(t)) s.insert(t); }, t.size());
		} else {
			// Collect all relation facts matched by goal
			decompress(tbls[t.tab].t && from_fact(t), t.tab,
				[&s](const term& t) { s.insert(t); }, t.size());
		}
	}
	// Explicitly add rules to carry facts between steps so that the proof tree
	// will capture proofs by carry. Record where the implicit rules start to
	// enable their removal.
	const size_t explicit_rule_count = rules.size();
	for(size_t i = 0; i < tbls.size(); i++) {
		// Make the positive identity rule for this table
		rules.push_back(new_identity_rule(i, false));
		// Make the negative identity rule for this table
		rules.push_back(new_identity_rule(i, true));
	}
	// Auxilliary variable for get_proof
	set<pair<term, size_t>> refuted;
	// Get all proofs for each covered fact
	for (const term& g : s)
		if (opts.bproof != proof_mode::none)
			get_proof(g, p, levels.size() - 1, refuted, explicit_rule_count),
			get_forest(g, p);
		else os << ir_handler->to_raw_term(g) << '.' << endl;

	// Print proofs
	if (opts.bproof != proof_mode::none) print(os, p);
	// Remove the auxilliary rules we created as they are no longer needed
	rules.resize(explicit_rule_count);
	return goals.size() || opts.bproof != proof_mode::none;	
}
