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

// transforms guards = facts into rules, adds state guards, transf. if and while
void tables::transform_guards(raw_prog& rp) {
	for (auto& np : rp.nps) transform_facts(np);
	transform_guard_statements(rp);
	if (!keep_guards) remove_guards(rp);
}

// emplaces back a new term structured as: __lx(__i) into rts
void tables::__(vector<raw_term>& rts, const lexeme& lx, int_t i, bool neg) {
	raw_term& rt = rts.emplace_back();
	rt.arity = { 1 };
	rt.e.emplace_back(elem::SYM, lx);
	rt.e.emplace_back(elem::OPENP,  dict.op);
	rt.e.emplace_back(elem::SYM,
		dict.get_lexeme(string("__").append(to_string_(i))));
	rt.e.emplace_back(elem::CLOSEP, dict.cl);
	rt.neg = neg;
}

// transforms facts into rules = transform all nested programs into init, start,
// add, del and rule states and guard each add/del/rule with its state guard
void tables::transform_facts(raw_prog& rp) {
	int_t i   = rp.id;
	static lexeme
		__init  = dict.get_lexeme("__init"),
		__start = dict.get_lexeme("__start"),
		__add   = dict.get_lexeme("__add"),
		__del   = dict.get_lexeme("__del"),
		__rule  = dict.get_lexeme("__rule"),
		__break = dict.get_lexeme("__break");

	for (auto& prog : rp.nps) transform_facts(prog);
	for (auto& rule : rp.r) if (!rule.is_form()) {
		bool is_fact = !rule.b.size();
		if (is_fact) rule.b.emplace_back();
		// adds program phase guard to each rule's body:
		// __add(__0) for positive facts) /
		// __del(__0) for negative facts) /
		// __rule(__0) for rules
		__(rule.b.back(), is_fact ? rule.h[0].neg ? __del : __add
			: __rule, rp.id);
		// add also ~__break(__0) which guards __break state
		__(rule.b.back(), __break, rp.id, true);
	}
	// __init(__0). # each nested program starts in the init phase
	__(rp.r.emplace_back().h, __init, i); // starts phase follows init phase
	// __start(__0), ~__init(__0) :- __init(__0), ~__break(__0).
	raw_rule& r1 = rp.r.emplace_back();
	r1.guarding = true;        // this rule guards execution of the current
	__(r1.h, __start, i);      // program. it is later guarded by
	__(r1.h, __init, i, true); // __true(__0) or __false(__0) for IF cond.
	__(r1.b.emplace_back(), __init, i);
	__(r1.b.back(), __break, i, true);
	// __add(__0), ~__start(__0)  :- __start(__0), ~__break(__0).
	raw_rule& r2 = rp.r.emplace_back();
	__(r2.h, __add, i);
	__(r2.h, __start, i, true);
	__(r2.b.emplace_back(), __start, i);
	__(r2.b.back(), __break, i, true);
	// __del(__0), ~__add(__0)  :- __add(__0), ~__break(__0).
	raw_rule& r3 = rp.r.emplace_back();
	__(r3.h, __del, i);
	__(r3.h, __add, i, true);
	__(r3.b.emplace_back(), __add, i);
	__(r3.b.back(), __break, i, true);
	// __rule(__0), ~__fact(__0)  :- __fact(__0), ~__break(__0).
	raw_rule& r4 = rp.r.emplace_back();
	__(r4.h, __rule, i);
	__(r4.h, __del, i, true);
	__(r4.b.emplace_back(), __del, i);
	__(r4.b.back(), __break, i, true);
}

// transforms ifs and whiles
void tables::transform_guard_statements(raw_prog& rp) {
	//COUT << "transform_guards " << &rp << endl;
	static lexeme
		__init  = dict.get_lexeme("__init"),
		__guard = dict.get_lexeme("__guard"),
		__true  = dict.get_lexeme("__true"),
		__false = dict.get_lexeme("__false"),
		__break = dict.get_lexeme("__break");

	function<void(const guard_statement&, raw_prog&, bool)> guard_prog;
	guard_prog = [this, &guard_prog]
		(const guard_statement& cond, raw_prog& rp, bool neg)
	{
		//COUT<<"guarding prog("<<rp.id<<") with guard("<<cond.id<<"/"<<(neg?"~":" ")<<"/"<<(int_t)cond.type<<")\n";
		if (cond.type == guard_statement::IF)
			for (auto& rule : rp.r) if (rule.guarding) {
				// add to the guarding body: __false/__true(__0)
				__(rule.b.back(), neg ? __false : __true,
					cond.id);
				break;
			}
		for (auto& prog : rp.nps) guard_prog(cond, prog, neg);
		if (cond.type == guard_statement::IF) {
			raw_rule& rr = rp.r.emplace_back();
			__(rr.h, neg ? __false : __true, cond.id);
			__(rr.b.emplace_back(), __guard, cond.id, neg);
			__(rr.b.back(), __init, rp.id);
		}
	};
	set<int_t> ifs;
	for (auto& cond : rp.gs) for (auto& prog : rp.nps)
		if (prog.grd.first == cond.id) {
			guard_prog(cond, prog, prog.grd.second);
			if (cond.type == guard_statement::WHILE)
				__(prog.r.emplace_back().h, __break, prog.id),
				prog.r.back().prft = cond.prft,
				prog.r.back().prft->neg = true;
			else if (ifs.find(cond.id) == ifs.end())
				__(rp.r.emplace_back().h, __guard, cond.id),
				rp.r.back().prft = cond.prft,
				ifs.insert(cond.id);
		}
	for (auto& prog : rp.nps) transform_guard_statements(prog);
}

void tables::remove_guards(raw_prog& rp) {
	strings guards = {
		"__init", "__start", "__add", "__del", "__rule",
		"__break", "__guard", "__true", "__false"
	};
	std::vector<raw_rule>& rules = rp.nps.emplace_back().r;
	for (auto g : guards) {
		lexeme lx = dict.get_lexeme(g);
		lexeme lv = dict.get_lexeme("?x");
		dict.get_var(lv);
		raw_term& rt = rules.emplace_back().h.emplace_back();
		rt.arity = { 1 };
		rt.e.emplace_back(elem::SYM, lx);
		rt.e.emplace_back(elem::OPENP, dict.op);
		rt.e.emplace_back(elem::VAR, lv);
		rt.e.emplace_back(elem::CLOSEP, dict.cl);
		rules.back().b.emplace_back().emplace_back() = rt;
		rt.neg = true;
	}
}

