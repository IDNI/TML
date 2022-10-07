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

#ifndef _TABLES_PRINTING_H_
#define _TABLES_PRINSTING_H_

#include "tables.h"
#include "ir_builder.h"
#include "dict.h"

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

void driver::out_fixpoint(std::basic_ostream<T> os) {
	bdd_handles trues, falses, undefineds;
	// TODO Change this, fixpoint should be computed before
	// requesting to output the fixpoint.
	if(compute_fixpoint(trues, falses, undefineds)) {
		for(ntable n = 0; n < (ntable)trues.size(); n++) {
			if(opts.show_hidden || !tbls[n].hidden) {
				decompress(trues[n], n, [&os, this](const term& r) {
					#ifdef REMOVE_IR_BUILDER_FROM_TABLES
					tp.notify_output(r);
					#else
					os << ir_handler->to_raw_term(r) << '.' << endl; 
					#endif // REMOVE_IR_BUILDER_FROM_TABLES
				});
			}
		}
		return true;
	} else return false;
}

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

/* 
template <typename T>
class out: public tables::visitor {
private:
	ir_builder &ir;
	std::basic_stream<T> &os;

	void visit(const table &t) const override {
		os << (t.hidden ? "@":"") << (t.idbltin > -1 ? " builtin\n" : "\n");
		for (auto r : t.r) os << "#\t\t", visit(rules[r]);
	}

	void visit(const rule &r) const override {
		os << ir.to_raw_term(r.t) << " :- ";
		for (auto it = r.begin(); it != r.end(); ++it) {
			for (size_t n = 0; n != (*it)->bltins.size(); ++n) {
				os << ir.to_raw_term((*it)->bltins[n]) <<
					(n == (*it)->bltins.size() - 1
						? it == r.end() - 1 ? "" : "; "
						: ", ");
			}
			if ((*it)->bltins.size())
				os << ((*it)->t.size() ? ", " : ".");
			for (size_t n = 0; n != (*it)->t.size(); ++n) {
				os << ir.to_raw_term((*it)->t[n]) <<
					(n == (*it)->t.size() - 1
						? it == r.end()-1 ? "." : "; "
						: ", ");
			}
		}
		os << std::endl;
	}

	void visit(const witness &w) const override {
		os << '[' << w.rl << ',' << w.al << "] ";
		for (const term& t : w.b) 
			os << ir.to_raw_term(t) << ", " << '.';
	}

	void visit(const proof &p) override {
		for (size_t n = 0; n != p.size(); ++n)
			for (const auto& x : p[n]) {
				for (const auto& y : x.second)
					os << n << ' ' << ir.to_raw_term(x.first)
					<< " :- " << y;
			};	
	}

	void visit(const proof_elem &e) override {
		if ( e.rl != (size_t)-1 ) os << '[' << e.rl << ',' << e.al << "] ";
		for (const auto& b : e.b)
			os << b.first << ' ' << ir.to_raw_term(b.second) << "\n";
	}
public:
	out(ir_builder &ir, std::basic_stream<T> os) : os(os), ir(ir) {}: 

	void visit(const tables &ts) override {
		os << "# " << ts.size() << " tables:\n";
		for (size_t n = 0; n != ts.size(); ++n)
			os << "# " << n << " ", visit(ts[n]);
		os << "# -\n";
	}

};

template <typename T>
class out_goals: public tables::visitor {
private:
	ir_builder &ir;
	std::basic_stream<T> &os;

public:
	out_goals(ir_builder &ir, std::basic_stream<T> os) : os(os), ir(ir) {}: 

	void visit(const tables &ts) override {
		if (ts.goals.size()) {
			bdd_handles trues, falses, undefineds;
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

};

template <typename T>
class out_fixpoint: public tables::visitor {
private:
	ir_builder &ir;
	std::basic_stream<T> &os;

public:
	out_fixpoint(ir_builder &ir, std::basic_stream<T> os) : os(os), ir(ir) {}: 

	void visit(const tables &ts) override {
		for(ntable n = 0; n < (ntable)trues.size(); n++) {
			if(opts.show_hidden || !tbls[n].hidden) {
				decompress(trues[n], n, [&os, &ir](const term& r) {
					os << ir.to_raw_term(r) << '.\n'; });
			}
		}
	}

};


template <typename T>
class out_proof: public tables::visitor {
private:
	ir_builder &ir;
	std::basic_stream<T> &os;

	gnode* tables::get_forest(const term& t, proof& p ) {

		std::map<term, gnode*> tg;
		gnode* root =  nullptr;
		for(int i =p.size()-1; i >=0; i-- )
			if( p[i].find(t) != p[i].end() ) {
				if( tg.find(t) == tg.end() ) {
					root = new gnode(i,t);
					tg[t] = root;
					build_graph(tg, p, *root);
					break;
				}
			}
		if(root) {
			static int count=0;
			string sppfname = to_string(count++);
			sppfname += "sppf";

			set<gnode*> v;
			std::wstringstream ss;
			std::wofstream file(sppfname + ".dot");
			print_dot(ss, *root, v);
			file << L"digraph {" << endl<< ss.str() << endl<<L"}"<<endl;
			file.close();

			v.clear(), ss.str(L""), ss.clear();
			root->binarise();
			print_dot(ss, *root, v);
			std::wofstream binfile(sppfname + "binarised.dot");
			binfile << L"digraph {" << endl<< ss.str() << endl<<L"}"<<endl;
			binfile.close();
		}
		return root;
	}

	/* Get the proofs of the given term occuring at the given level stemming
	* directly from a DNF rule head. Do this by querying the corresponding
	* instrumentation facts. They will tell us which rules derived the given fact
	* and under which instantiation of the existential quantifiers they were
	* derived. Note that the instrumented fact may correspond to this fact derived
	* at a different level, so we do need to check that the facts that it suggests
	* exist do actually exist at the previous level. Otherwise that proof must be
	* discarded. Counter-examples from rules beyond the explicit rule count are
	* silenced. */

/*	bool tables::get_dnf_proofs(const term& q, proof& p, const size_t level,
			set<pair<term, size_t>> &refuted, const size_t explicit_rule_count) {
		// A set of negative facts that are enough to prevent q from being derived.
		// Evidence for a negative fact.
		proof_elem not_exists_proof;
		not_exists_proof.rl = not_exists_proof.al = 0;
		// Find the rules corresponding to this fact. Loop backwards so that implicit
		// carry rules are found first. This matters only when generating proof trees.
		for(size_t rule_idx = rules.size(); rule_idx-- > 0; ) {
			rule &rul = rules[rule_idx];
			if(rul.tab != q.tab) continue;
			for(size_t alt_idx = 0; alt_idx < rul.size(); alt_idx++) {
				alt &alte = *rul[alt_idx];
				// Lookup the variable instantiations of this alternative from its levels
				// structure if we are trying to prove existence. If not trying to prove
				// existence, then we need to consider all possible instantiations to prove
				// that there are no counter-examples.
				const bool exists_mode = q.neg == rul.neg;
				// If we are in partial mode, do not bother to show that the negation of
				// this present fact could not have been derived.
				if(!exists_mode && (opts.bproof == proof_mode::partial_tree ||
					opts.bproof == proof_mode::partial_forest)) continue;
				spbdd_handle var_domain = exists_mode ? alte.levels[level] : htrue;
				decompress(addtail(rul.eq && from_fact(q), q.size(), alte.varslen) &&
						var_domain, q.tab, [&](const term& t) {
					// If we are only generating proof trees and already have a proof of
					// this fact then do not investigate other proofs.
					if(exists_mode && (opts.bproof == proof_mode::tree ||
						opts.bproof == proof_mode::partial_tree) &&
						p[level].find(q) != p[level].end()) return;
					// Ensure term validity as BDD may contain illegal values
					if(!is_term_valid(t)) return;
					
					// Now we want to substitute the variable instantiations into the
					// rule body. If all these body terms were true, then we have enough to
					// prove the fact q.
					proof_elem exists_proof;
					exists_proof.rl = rule_idx;
					exists_proof.al = 0;
					for(term body_tm : alte.t) {
						for(int_t &arg : body_tm) {
							auto var_sub = alte.vm.find(arg);
							// Replace argument with substitution if present
							if(var_sub != alte.vm.end()) arg = t[var_sub->second];
						}
						exists_proof.b.push_back({level-1, body_tm});
					}
					// Now to prove that the a positive fact q is true, we want to prove
					// that all the body terms are true using the levels structure. If we
					// cannot prove them, then the truth proof under construction must be
					// discarded. And to be able to prove a negative fact true, we want to
					// show that the negation of a body term is true.
					
					// Indicates whether all body terms are true 
					bool exists_proof_valid = true;
					for(auto &[body_level, body_tm] : exists_proof.b) {
						term negated_body_tm = body_tm;
						negated_body_tm.neg = !negated_body_tm.neg;
						// If we are trying to prove a positive fact, then we need a proof of
						// each body term. If we are trying to prove a negative fact, we need
						// a proof of a negation of a body term.
						if(get_proof(exists_mode ? body_tm : negated_body_tm, p, body_level,
								refuted, explicit_rule_count) != exists_mode) {
							if(exists_mode) {
								// If q head positive, then a body proof failed. So there cannot
								// exist an instantitation of variables in current rule to make
								// head q.
								exists_proof_valid = false;
							} else {
								// If q head negative, then we have just found a proof that this
								// variable instantiation cannot work.
								pair<nlevel, term> counter_example = {level-1, negated_body_tm};
								// Never present counter-examples from implicit rules and avoid
								// duplicating counter-examples.
								if(rule_idx < explicit_rule_count &&
										find(not_exists_proof.b.begin(), not_exists_proof.b.end(), counter_example) ==
										not_exists_proof.b.end()) {
									not_exists_proof.b.push_back(counter_example);
								}
							}
							break;
						}
					}
					if(exists_proof_valid && exists_mode) {
						// Add this proof as one of the many possible proving this positive fact
						p[level][q].insert(exists_proof);
					}
				}, alte.varslen);
			}
		}
		// During the course of positively establishing the given fact, we had to be
		// proving that its negation could not be proved. These proofs are stored in
		// not_exists_proof and need to be appended to every positive proof.
		set<proof_elem> augmented_witnesses;
		for(proof_elem witnes : p[level][q]) {
			// For all instantiations that could derive the negation of this fact,
			// consider the proof one of the body terms could not be satisfied.
			for(const auto &not_witness : not_exists_proof.b) {
				// Do not repeat witnesses for the statement that the negation of the main
				// fact cannot be derived.
				if(find(witnes.b.begin(), witnes.b.end(), not_witness) == witnes.b.end()) {
					witnes.b.push_back(not_witness);
				}
			}
			// Construct a new set of proof elements since this current set cannot be
			// modified on the fly
			augmented_witnesses.insert(witnes);
		}
		// Replace the unaugmented witnesses with augmented ones
		p[level][q] = augmented_witnesses;
		// Return true only if we have constructed at least one proof
		return p[level].find(q) != p[level].end();
	}
*/
	/* Get all the proofs of the given term occuring at the given level and put them
	* into the given proof object. Record the term and level in the absentee set
	* and return false if the given term does not actually occur at the given
	* level. Counter-examples from rules beyond the explicit rule count are
	* silenced. */
/*	bool get_proof(const term& q, proof& p, const size_t level,
			set<pair<term, size_t>> &refuted, const size_t explicit_rule_count) {
		// Grow the proof object until it can store proof for this level
		for(; p.size() <= level; p.push_back({}));
		// Check if this term has not already been proven at the given level
		if(p[level].find(q) != p[level].end()) return true;
		// Otherwise check if the term has not already been shown absent
		if(auto it = refuted.find({q, level}); it != refuted.end()) return false;
		// First ensure that this term can actually be proved. That is ensure that it
		// is present or not present in the relevant step database.
		int_t qsat = (levels[level][q.tab] && from_fact(q)) != hfalse;
		// If the fact is negative, then its presence in the database is
		// contradictory. If it is positive, then its absense from the database is
		// also contradictory.
		if(q.neg == qsat) { refuted.insert({ q, level }); return false; }
		// The proof for this fact may stem from a DNF rule's derivation. There may be
		// a multiplicity of these proofs. Get them.
		if(level > 0) get_dnf_proofs(q, p, level, refuted, explicit_rule_count);
		// Here we know that this fact is valid. Make sure that this fact at least has
		// empty witness set to represent self-evidence.
		p[level][q];
		return true;
	}

public:
	out_proof(ir_builder &ir, std::basic_stream<T> os) : os(os), ir(ir) {}: 

	void visit(const tables &ts) override {
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

};
*/
#endif // _TABLES_PRINTING_H_
