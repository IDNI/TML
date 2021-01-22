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
#include "tables.h"

using namespace std;

lexeme tables::lx_id(string name, int_t id, int_t id2) {
	static std::string __ = "__";
	std::stringstream ss;
	if (id  != -1) ss << __ << id;
	if (id2 != -1) ss << __ << id2;
	ss << __ << name << __;
	return dict.get_lexeme(ss.str());
}

// emplaces back a new 0ary term named lx into rts
void tables::__(vector<raw_term>& rts, const lexeme& lx, bool neg) {
	raw_term& rt = rts.emplace_back();
	rt.arity = { 0 };
	rt.e.emplace_back(elem::SYM, lx);
	rt.neg = neg;
}

// emplaces back a new term names as: __id__lx__ into rts
void tables::__(vector<raw_term>& rts, const string& lx, int_t id, bool neg) {
	__(rts, lx_id(lx, id), neg);
}

// emplaces back a new term named as: __id__id2__lx__ into rts
void tables::__(vector<raw_term>& rts, const string& lx, int_t id, int_t id2,
	bool neg)
{
	__(rts, lx_id(lx, id, id2), neg);
}

// transforms guards = facts into rules, adds state guards, transf. if and while
void tables::transform_guards(raw_prog& rp) {

	// initiate program by setting the id of the fixed point program to 0
	int_t prev_id = 0;
	__(rp.r.emplace_back().h, "fp", prev_id);

	for (auto& np : rp.nps)
		transform_facts(rp, np, prev_id);
	transform_guard_statements(rp, rp);

	// clean __N__fp__ facts from if true blocks
	for (int_t i = 0; i != prev_id+1; ++i)
		__(rp.r.emplace_back().h, "fp", i, true),
		__(rp.r.back().b.emplace_back(), "fp", i);

	// clean the last fp
	//__(rp.r.emplace_back().h, "fp", prev_id, true),
	//__(rp.r.back().b.emplace_back(), "fp", prev_id);

	// remove empty nested programs
	rp.nps.clear();
}

// transforms facts into rules = transform all nested programs into start, add,
// del, rule, true, false, curr and fp states and guard each add/del/rule
// statement with its state guard
void tables::transform_facts(raw_prog& trp, raw_prog& rp, int_t& prev_id) {
	int_t i = rp.id;

	for (auto& rule : rp.r) {
		bool is_form = rule.is_form();
		bool is_fact = !rule.b.size() && !is_form;
		if (is_fact) rule.b.emplace_back();		
		if (is_form) rule.prft->guard_lx = lx_id("rule", rp.id);
		else __(rule.b.back(), is_fact ? (rule.h[0].neg ? "del" : "add")
			: "rule", rp.id);
		trp.r.emplace_back(rule);
		//o::inf() << "transformed_rule: " << rule << endl;;
		
		// just move directives, productions and macros
		// (they are global so far - TODO)
	}
	if (rp.d.size()) trp.d.insert(trp.d.end(), rp.d.begin(), rp.d.end());
	if (rp.g.size()) trp.g.insert(trp.g.end(), rp.g.begin(), rp.g.end());
	if (rp.vm.size()) trp.vm.insert(trp.vm.end(), rp.vm.begin(), rp.vm.end());
	rp.r.clear();
	rp.d.clear();
	rp.g.clear();
	rp.vm.clear();

	raw_rule& r1 = trp.r.emplace_back();
	__(r1.h, "start", i);
	if (rp.guarded_by != -1) {
		//__(r1.h, "fp", rp.guarded_by, true);
		__(r1.h, "guard", rp.guarded_by, rp.id, true);
		__(r1.b.emplace_back(), "fp", rp.guarded_by);
		__(r1.b.back(), "guard", rp.guarded_by, rp.id);
	} else {
		__(r1.h, "fp", prev_id, true);
		__(r1.b.emplace_back(), "fp", prev_id);
	}

	raw_rule& r2 = trp.r.emplace_back();
	__(r2.h, "add", i);
	__(r2.h, "curr", i);
	__(r2.h, "start", i, true);
	__(r2.b.emplace_back(), "start", i);

	raw_rule& r3 = trp.r.emplace_back();
	__(r3.h, "del", i);
	__(r3.h, "add", i, true);
	__(r3.b.emplace_back(), "add", i);

	raw_rule& r4 = trp.r.emplace_back();
	__(r4.h, "rule", i);
	__(r4.h, "del", i, true);
	__(r4.b.emplace_back(), "del", i);

	raw_rule& r5 = trp.r.emplace_back();
	__(r5.h, "true", i);
	__(r5.h, "rule", i, true);
	__(r5.h, "fp", -1, true);
	__(r5.b.emplace_back(), "rule", i);
	__(r5.b.back(), "fp", -1);

	raw_rule& r6 = trp.r.emplace_back();
	__(r6.h, "false", i);
	__(r6.h, "true", i, true);
	__(r6.b.emplace_back(), "true", i);

	raw_rule& r7 = trp.r.emplace_back();
	__(r7.h, "fp", i);
	__(r7.h, "false", i, true);
	__(r7.b.emplace_back(), "false", i);

	raw_rule& r8 = trp.r.emplace_back();
	__(r8.h, "curr", i, true);
	__(r8.b.emplace_back(), "curr", i);
	__(r8.b.back(), "fp", i);

	prev_id = i;

	for (auto& prog : rp.nps) {		
		transform_facts(trp, prog, prev_id);
	}

	//o::inf() << "\t//transform_facts(trp, rp, prev_id), rp.id = " << i << " prev_id = " << prev_id << endl;
}

// transforms ifs and whiles
void tables::transform_guard_statements(raw_prog& trp, raw_prog& rp) {
	for (auto& c : rp.gs) {
		if (c.type == guard_statement::IF) {
			raw_rule& r1 = trp.r.emplace_back();
			__(r1.h, "guard", c.rp_id, c.true_rp_id),
			r1.prft = c.prft;
			r1.prft->guard_lx = lx_id("true", c.rp_id);
			raw_rule& r2 = trp.r.emplace_back();
			__(r2.h,                "guard", c.rp_id, c.false_rp_id),
			__(r2.b.emplace_back(), "guard", c.rp_id, c.true_rp_id, true),
			__(r2.b.back(),         "false", c.rp_id);
			 // clean fp states
			//raw_rule& r3 = trp.r.emplace_back();
			//__(r3.h,                "fp", c.true_rp_id, true),
			//__(r3.b.emplace_back(), "fp", c.true_rp_id);
			//raw_rule& r4 = trp.r.emplace_back();
			//__(r4.h,                "fp", c.false_rp_id, true),
			//__(r4.b.emplace_back(), "fp", c.false_rp_id);
		} else
		if (c.type == guard_statement::WHILE) {
			raw_rule& r = trp.r.emplace_back();
			__(r.h, "fp", c.rp_id);
			__(r.h, "start",      c.rp_id, true);
			__(r.h, "add",        c.rp_id, true);
			__(r.h, "del",        c.rp_id, true);
			__(r.h, "rule",       c.rp_id, true);
			__(r.h, "curr",       c.rp_id, true);
			r.prft = c.prft;
			r.prft->guard_lx = lx_id("curr", c.rp_id);
			r.prft->neg = true;
		}
	}
	for (auto& prog : rp.nps) transform_guard_statements(trp, prog);
}

