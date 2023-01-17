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

#include "ir_builder.h"

using namespace std;

namespace idni {

lexeme ir_builder::lx_id(string name, int_t id, int_t id2) {
	static std::string s = "__";
	std::stringstream ss;
	if (id  != -1) ss << s << id;
	if (id2 != -1) ss << s << id2;
	ss << s << name << s;
	return dict.get_lexeme(ss.str());
}

// emplaces back a new 0ary term named lx into rts
void ir_builder::iid(vector<raw_term>& rts, const lexeme& lx, bool neg) {
	raw_term& rt = rts.emplace_back();
	rt.arity = { 0 };
	rt.e.emplace_back(elem::SYM, lx);
	rt.neg = neg;
}

// emplaces back a new term names as: iididiidlxiid into rts
void ir_builder::iid(vector<raw_term>& rts, const string& lx, int_t id, bool neg) {
	iid(rts, lx_id(lx, id), neg);
}

// emplaces back a new term named as: iididiidid2iidlxiid into rts
void ir_builder::iid(vector<raw_term>& rts, const string& lx, int_t id, int_t id2,
	bool neg)
{
	iid(rts, lx_id(lx, id, id2), neg);
}

// transforms guards = facts into rules, adds state guards, transf. if and while
void ir_builder::transform_guards(raw_prog& rp) {
	// initiate program by setting the id of the fixed point program to 0
	int_t prev_id = 0;
	if (rp.r.size() || rp.nps.size()) // but only if not empty
		iid(rp.r.emplace_back().h, "fp", prev_id);
	for (auto& np : rp.nps)	transform_guards_program(rp, np, prev_id);
	transform_guard_statements(rp, rp);
	// remove empty nested programs
	rp.nps.clear();
}

// transforms a program into phases
// del, rule, true, false, curr and fp states and guard each add/del/rule
// statement with its state guard
void ir_builder::transform_guards_program(raw_prog& trp, raw_prog& rp,
	int_t& prev_id)
{
	vector<string> states = {
		"init", "start", "add", "del", "rule", "cond", "fp", "curr"
	};
	int_t id = rp.id;
	for (auto& rule : rp.r) {
		bool is_form = rule.is_form();
		bool is_fact = !rule.b.size() && !is_form;
		if (is_fact) rule.b.emplace_back();
		if (is_form) rule.prft->guard_lx = lx_id("rule", id);
		else iid(rule.b.back(), is_fact ? (rule.h[0].neg? "del" : "add")
			: "rule", id);
		trp.r.emplace_back(rule);
	}
	auto next_state = [&rp] (state_value state) -> state_value
	{
		switch (state) {
			case INIT: return START;
			case START: if(rp.has[ADDS])  {
				return ADDS; } [[fallthrough]];
			case ADDS:  if(rp.has[DELS])  {
				return DELS; } [[fallthrough]];
			case DELS:  if(rp.has[RULE]) {
				return RULE; } [[fallthrough]];
			case RULE:  if(rp.has[COND]) {
				return COND; } [[fallthrough]];
			case COND:
			default:return FP;
		}
	};
	state_value prev_state = rp.has[CURR] ? INIT : START;
	state_value state      = next_state(prev_state);
	trp.r.emplace_back();
	if (rp.guarded_by != -1) {
		bool is_false_rp = rp.true_rp_id != -1;
		if (!is_false_rp)
			iid(trp.r.back().h, "guard", rp.guarded_by, id, true);
		iid(trp.r.back().b.emplace_back(), "fp", rp.guarded_by);
		iid(trp.r.back().b.back(), "guard", rp.guarded_by, is_false_rp
			? rp.true_rp_id : id, is_false_rp);
	} else
		iid(trp.r.back().h, "fp", prev_id, true),
		iid(trp.r.back().b.emplace_back(), "fp", prev_id);
	iid(trp.r.back().h, states[state], id);

	if (rp.has[CURR]) iid(trp.r.back().h, "curr", id);
	while (state != FP) {
		prev_state = state;
		state = next_state(state);
		trp.r.emplace_back(),
		iid(trp.r.back().h, states[prev_state], id, true);
		iid(trp.r.back().b.emplace_back(), states[prev_state], id);
		if (prev_state == RULE)
			iid(trp.r.back().h, "fp", -1, true),
			iid(trp.r.back().b.back(), "fp", -1);
		iid(trp.r.back().h, states[state], id);
	};
	if (rp.has[CURR]) trp.r.emplace_back(),
		iid(trp.r.back().h, "curr", id, true),
		iid(trp.r.back().b.emplace_back(), "fp", id),
		iid(trp.r.back().b.back(), "curr", id);
	trp.r.emplace_back(),
		iid(trp.r.back().h, "fp", id, true),
		iid(trp.r.back().b.emplace_back(), "fp", id);
	prev_id = id;
	for (auto& prog : rp.nps) transform_guards_program(trp, prog, prev_id);
	// just move directives, productions and macros (always global scope)
	if (rp.d.size())  trp.d.insert( trp.d.end(), rp.d.begin(), rp.d.end());
	if (rp.g.size())  trp.g.insert( trp.g.end(), rp.g.begin(), rp.g.end());
	if (rp.macros.size())
		trp.macros.insert(trp.macros.end(), rp.macros.begin(),
		rp.macros.end());
	rp.r.clear(), rp.d.clear(), rp.g.clear(), rp.macros.clear();
}

// transforms ifs and whiles
void ir_builder::transform_guard_statements(raw_prog& trp, raw_prog& rp) {
	for (auto& c : rp.gs) {
		if (c.type == guard_statement::IF) {
			trp.r.emplace_back();
			iid(trp.r.back().h, "guard", c.rp_id, c.true_rp_id),
			trp.r.back().prft = c.prft;
			trp.r.back().prft->guard_lx = lx_id("cond", c.rp_id);
		} else
		if (c.type == guard_statement::WHILE) {
			if (!rp.has[ADDS] && !rp.has[DELS] &&
				!rp.has[RULE]) continue;
			trp.r.emplace_back();
			iid(trp.r.back().h, "curr",  c.rp_id, true);
			iid(trp.r.back().h, "start", c.rp_id, true);
			if (c.p_break_rp->has[ADDS])
				iid(trp.r.back().h, "add",   c.rp_id, true);
			if (c.p_break_rp->has[DELS])
				iid(trp.r.back().h, "del",   c.rp_id, true);
			if (c.p_break_rp->has[RULE])
				iid(trp.r.back().h, "rule",  c.rp_id, true);
			iid(trp.r.back().h, "fp",    c.rp_id);
			trp.r.back().prft = c.prft;
			trp.r.back().prft->guard_lx = lx_id("curr", c.rp_id);
			trp.r.back().prft->neg = true;
		}
	}
	for (auto& prog : rp.nps) transform_guard_statements(trp, prog);
}

} // idni namespace
