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
#include <algorithm>
#include <random>
#include <list>
#include <algorithm>
#include <variant>
#include <memory>

#include "tables.h"
#include "dict.h"
#include "input.h"
#include "output.h"
using namespace std;

typedef tuple<size_t, size_t, size_t, int_t> skmemo;
typedef tuple<size_t, size_t, size_t, int_t> ekmemo;

map<skmemo, spbdd_handle> smemo;
map<ekmemo, spbdd_handle> ememo;
map<ekmemo, spbdd_handle> leqmemo;

//-----------------------------------------------------------------------------
//vars

template<typename T>
varmap tables::get_varmap(const term& h, const T& b, size_t &varslen, bool blt) {
	varmap m;
	varslen = h.size();
	for (size_t n = 0; n != h.size(); ++n)
		if (h[n] < 0 && !has(m, h[n])) m.emplace(h[n], n);
	if (blt) return m;
	for (const term& t : b)
		for (size_t n = 0; n != t.size(); ++n)
			if (t[n] < 0 && !has(m, t[n]))
				m.emplace(t[n], varslen++);
	return m;
}

void getvars(const term& t, set<int_t>& v) {
	for (int_t i : t) if (i < 0) v.insert(i);
}

void getvars(const vector<term>& t, set<int_t>& v) {
	for (const term& x : t) getvars(x, v);
}

//-----------------------------------------------------------------------------

spbdd_handle tables::leq_const(int_t c, size_t arg, size_t args, size_t bit)
	const
{
	if (!--bit)
		return	(c & 1) ? htrue :
			::from_bit(pos(0, arg, args), false);
	return (c & (1 << bit)) ?
		bdd_ite_var(pos(bit, arg, args), leq_const(c, arg, args, bit),
			htrue) :
		bdd_ite_var(pos(bit, arg, args), hfalse,
			leq_const(c, arg, args, bit));
}

spbdd_handle tables::leq_var(size_t arg1, size_t arg2, size_t args) const {
	static ekmemo x;
	static map<ekmemo, spbdd_handle>::const_iterator it;
	if ((it = leqmemo.find(x = { arg1, arg2, args, bits })) != leqmemo.end())
		return it->second;
	spbdd_handle r = leq_var(arg1, arg2, args, bits);
	return leqmemo.emplace(x, r), r;
}

spbdd_handle tables::leq_var(size_t arg1, size_t arg2, size_t args, size_t bit)
	const
{
	if (!--bit)
		return	bdd_ite(::from_bit(pos(0, arg2, args), true),
				htrue,
				::from_bit(pos(0, arg1, args), false));
	return	bdd_ite(::from_bit(pos(bit, arg2, args), true),
			bdd_ite_var(pos(bit, arg1, args),
				leq_var(arg1, arg2, args, bit), htrue),
			bdd_ite_var(pos(bit, arg1, args), hfalse,
				leq_var(arg1, arg2, args, bit)));
}

uints perm_init(size_t n) {
	uints p(n);
	while (n--) p[n] = n;
	return p;
}

spbdd_handle tables::add_bit(spbdd_handle x, size_t args) {
	uints perm = perm_init(args * bits);
	for (size_t n = 0; n != args; ++n)
		for (size_t k = 0; k != bits; ++k)
			perm[pos(k, n, args)] = pos(k+1, bits+1, n, args);
	bdd_handles v = { x ^ perm };
	for (size_t n = 0; n != args; ++n)
		v.push_back(::from_bit(pos(0, bits + 1, n, args), false));
	return bdd_and_many(move(v));
}

void tables::add_bit() {
	spbdd_handle x = hfalse;
	bdd_handles v;
	for (auto& x : tbls)
		x.t = add_bit(x.t, x.len);
	++bits;
}

spbdd_handle tables::from_sym(size_t pos, size_t args, int_t i) const {
	static skmemo x;
	static map<skmemo, spbdd_handle>::const_iterator it;
	if ((it = smemo.find(x = { i, pos, args, bits })) != smemo.end())
		return it->second;
	spbdd_handle r = htrue;
	for (size_t b = 0; b != bits; ++b) r = r && from_bit(b, pos, args, i);
	return smemo.emplace(x, r), r;
}

spbdd_handle tables::from_sym_eq(size_t p1, size_t p2, size_t args) const {
	static ekmemo x;
	// a typo should be ekmemo, all the same at the moment
	//static map<skmemo, spbdd_handle>::const_iterator it;
	static map<ekmemo, spbdd_handle>::const_iterator it;
	if ((it = ememo.find(x = { p1, p2, args, bits })) != ememo.end())
		return it->second;
	spbdd_handle r = htrue;
	for (size_t b = 0; b != bits; ++b)
		r = r && ::from_eq(pos(b, p1, args), pos(b, p2, args));
	return ememo.emplace(x, r), r;
}

spbdd_handle tables::from_fact(const term& t) {
	// TODO: memoize
	spbdd_handle r = htrue;
	static varmap vs;
	vs.clear();
	auto it = vs.end();
	for (size_t n = 0, args = t.size(); n != args; ++n)
		if (t[n] >= 0) r = r && from_sym(n, args, t[n]);
		else if (vs.end() != (it = vs.find(t[n])))
			r = r && from_sym_eq(n, it->second, args);
		else if (vs.emplace(t[n], n), !t.neg && !t.goal) {}
	return r;
}

//-----------------------------------------------------------------------------

uints tables::get_perm(const term& t, const varmap& m, size_t len) const {
	uints perm = perm_init(t.size() * bits);
	for (size_t n = 0, b; n != t.size(); ++n)
		if (t[n] < 0)
			for (b = 0; b != bits; ++b)
				perm[pos(b,n,t.size())] = pos(b,m.at(t[n]),len);
	return perm;
}

body tables::get_body(const term& t, const varmap& vm, size_t len) const {
	body b;
	b.neg = t.neg, b.tab = t.tab, b.perm = get_perm(t, vm, len),
	b.q = htrue, b.ex = bools(t.size() * bits, false);
	varmap m;
	auto it = m.end();
	for (size_t n = 0; n != t.size(); ++n)
		if (t[n] >= 0)
			b.q = b.q && from_sym(n, t.size(), t[n]),
			get_var_ex(n, t.size(), b.ex);
		else if (m.end() == (it = m.find(t[n]))) m.emplace(t[n], n);
		else b.q = b.q && from_sym_eq(n, it->second, t.size()),
			get_var_ex(n, t.size(), b.ex);
	return b;
}

bool tables::get_facts(const flat_prog& m) {
	// TODO: We need add and del in order to deal with negations in heads.
	// A couple of regression tests use negation in heads.
	// We should check whether this is a desirable feature.
	map<ntable, vector<const term*>> add, del;
	map<ntable, size_t> invert;
	map<ntable, pair<vector<size_t>, vector<size_t>>> inverses;
	// get facts by table
	for (const auto& r : m)
		if (r.size() != 1) continue;
		else if (r[0].goal) goals.insert(r[0]);
		else if (r[0].is_builtin()) fact_builtin(r[0]);
		else if (is_optimizable_fact(r[0]))
			(r[0].neg ? del: add)[r[0].tab].push_back(std::addressof(r[0])),
			invert[r[0].tab] = r[0].size();
	if (unsat || halt) return false;
	clock_t start{}, end;
	if (opts.optimize) measure_time_start();
	// Compute the inverse of pos for the collected facts
	for (auto& p: invert)
		inverses[p.first] = _inverse(bits, p.second);
	// Compute the bdds for the each table
	for (auto x: from_facts(add, inverses))
		tbls[x.first].t = x.second;
	for (auto x: from_facts(del, inverses))
		tbls[x.first].t = tbls[x.first].t % x.second;
	if (opts.optimize)
		(o::ms() << "# get_facts: "),
		measure_time_end();
	return true;
}
bool tables::is_optimizable_fact(const term& t) const {
	// For example: a. a(1 2 3). ~b. ~b(4 5 6).
	return t.size() == 0 || (t.size() >0 && t[0] >= 0);
}

map<ntable, spbdd_handle> tables::from_facts(
		map<ntable, vector<const term*>>& pending,
		const map<ntable, pair<vector<size_t>, vector<size_t>>>& inverses) const {
	map<ntable, spbdd_handle> p;
	for (auto t: pending)
		if (t.second.size() == 0) continue;
		else p[t.first] = from_facts(t.second, inverses.at(t.first));
	return p;
}
spbdd_handle tables::from_facts(
		vector<const term*>& pending,
		const pair<vector<size_t>, vector<size_t>>& inverse) const {
	if (pending.size() == 0) return htrue;
	// If the facts have no arguments, we return htrue regardless if
	// they correspond to a del or and call. They will be process
	// properly in get_facts.
	if (pending[0]->size() == 0) return htrue;
	// Otherwise, we prooceed with the radix sorting & building of
	// the bdd.
	return from_facts(pending, pending.begin(), pending.end(), 0, inverse);
}
spbdd_handle tables::from_facts(vector<const term*>& terms,
		vector<const term*>::iterator left,
		vector<const term*>::iterator right,
		const size_t& pos,
		const pair<vector<size_t>, vector<size_t>>& inverse) const {
	size_t max = max_pos(*left);
	if (pos == max) {
		#ifdef TYPE_RESOLUTION
		if (next(left) != right) return htrue;
		#endif
		return from_bit(left, inverse);
	}
	auto it = partition(left, right,
		[this, pos, inverse](const term* t) -> bool {
			return !bit(pos, t, inverse.first, inverse.second); });
	if (left == it)	return from_high(pos,
		from_facts(terms, it, right, pos +1, inverse) -> b);
	if (right == it) return from_low(pos,
		from_facts(terms, left, it, pos + 1, inverse) -> b);
	return from_high_and_low(pos,
		from_facts(terms, it, right, pos + 1, inverse) -> b,
		from_facts(terms, left, it, pos + 1, inverse) -> b);
}
spbdd_handle tables::from_bit(
		const vector<const term*>::iterator& current,
		const pair<vector<size_t>, vector<size_t>>& inverse) const {
	size_t max = max_pos(*current);
	size_t a = (*current)->size();
	size_t i = inverse.second.at(max);
	size_t b = inverse.first.at(max);
	return from_bit(b, i, a, (*current)->at(i));
}

bool tables::handler_eq(const term& t, const varmap& vm, const size_t vl,
		spbdd_handle &c) const {
	DBG(assert(t.size() == 2););
	spbdd_handle q = bdd_handle::T;
	if (t[0] == t[1]) return !(t.neg);
	if (t[0] >= 0 && t[1] >= 0) return !(t.neg == (t[0] == t[1]));
	if (t[0] < 0 && t[1] < 0)
		q = from_sym_eq(vm.at(t[0]), vm.at(t[1]), vl);
	else if (t[0] < 0)
		q = from_sym(vm.at(t[0]), vl, t[1]);
	else if (t[1] < 0)
		q = from_sym(vm.at(t[1]), vl, t[0]);
	c = t.neg ? c % q : (c && q);
	return true;
}

/* Add the constraint that the given variable is a number to the given
 * BDD. */

spbdd_handle tables::constrain_to_num(size_t var, size_t n_vars) const {
	// Numbers must have their lowest bits be 01.
	return ::from_bit(pos(1, var, n_vars),true) &&
		::from_bit(pos(0, var, n_vars),false);
}

bool tables::handler_leq(const term& t, const varmap& vm, const size_t vl,
		spbdd_handle &c) const {
	DBG(assert(t.size() == 2););
	spbdd_handle q = bdd_handle::T, numeric_constraint = bdd_handle::T;
	if (t[0] == t[1]) return !(t.neg);
	if (t[0] >= 0 && t[1] >= 0) return !(t.neg == (t[0] <= t[1]));
	if (t[0] < 0 && t[1] < 0) {
		q = leq_var(vm.at(t[0]), vm.at(t[1]), vl, bits);
		#ifndef TYPE_RESOLUTION
		numeric_constraint = constrain_to_num(vm.at(t[0]), vl) &&
			constrain_to_num(vm.at(t[1]), vl);
		#endif
	} else if (t[0] < 0) {
		q = leq_const(t[1], vm.at(t[0]), vl, bits);
		#ifndef TYPE_RESOLUTION
		numeric_constraint = constrain_to_num(vm.at(t[0]), vl);
		#endif
	} else if (t[1] < 0) {
		// 1 <= v1, v1 >= 1, ~(v1 <= 1) || v1==1.
		q = htrue % leq_const(t[0], vm.at(t[1]), vl, bits) ||
			from_sym(vm.at(t[1]), vl ,t[0]);
		#ifndef TYPE_RESOLUTION
		numeric_constraint = constrain_to_num(vm.at(t[1]), vl);
		#endif
	}
	// Enforce the numeric constraint regardless of whether this term is positive
	// or negated. This essentially forces any operands to inequalities to be
	// integers and guarantees that ?a<?b is safe iff ?a<=?b is safe.
	c = (t.neg ? c % q : (c && q)) && numeric_constraint;
	return true;
}

void tables::clear_memos() {
	smemo.clear(), ememo.clear(), leqmemo.clear();
}

#ifdef BIT_TRANSFORM
void tables::handler_bitunv(set<pair<body,term>>& b, const term& t, alt& a) {
	// TODO check if this could be done during transformation in 
	// transform_bitunv.cpp:357 and related lines.
	
	//FIXME: cannot be comparing strings at FWD
	string pred = bltins.aliases[t.tab];
	int_t idbltin = -1;
	term taux(t);

	if (pred.find("_EQ_") != std::string::npos)
		
		idbltin = t.tab;
	
	else if (pred.find("_LEQ_") != string::npos) {

		idbltin = t.tab;

		taux.extype = term::BLTIN;
		taux.idbltin = idbltin;
	}
	else if (pred.find("_PLUS_") != string::npos)

		idbltin = t.tab;

	else if (pred.find("_MULT_") != string::npos)

		idbltin = t.tab;

	else {
		b.insert({ get_body(t, a.vm, a.varslen), t });
		return;
	}

	//todo: check that idbltin is properly configured in builtins
	bltins.at(idbltin).body.getvars(taux, a.bltinvars, a.bltngvars, a.bltoutvars);
	a.bltins.push_back(taux);
}
#endif

void tables::get_alt(const term_set& al, const term& h, set<alt>& as, bool blt) {

	alt a;
	set<pair<body, term>> b;
	spbdd_handle leq = htrue, q;
	a.vm = get_varmap(h, al, a.varslen, blt);

	for (const term& t : al) {
		if (t.extype == term::REL) {
			#ifdef BIT_TRANSFORM
			handler_bitunv(b, t, a);
			#else
			b.insert({get_body(t, a.vm, a.varslen), t});
			#endif
		} else if (t.extype == term::EQ) {
			if (!handler_eq(t, a.vm, a.varslen, a.eq)) return;
		} else if (t.extype == term::LEQ) {
			if (!handler_leq(t, a.vm, a.varslen, leq)) return;
		} else if (t.extype == term::ARITH) {
			//arith constraint on leq
			if (!handler_arith(t,a.vm, a.varslen, leq)) return;
		} else if (!blt && t.extype == term::BLTIN) {
			bltins.at(t.idbltin).body.getvars(t,
				a.bltinvars, a.bltngvars, a.bltoutvars);
			a.bltins.push_back(t);
		}
	}
	if (a.bltinvars.size()) { // get grnd
		ints args;
		for (auto v : a.bltinvars) args.push_back(v);
		const term bt(false, -1, args, 0, -1);
		set<alt> as;
		get_alt(al, bt, as, true);
		assert(as.size() == 1);
		for (alt x : as) *(a.grnd = new alt) = x;
		// TODO should we grnd alt sharing? The code could be as follows
		// 	set<alt*, ptrcmp<alt>>::const_iterator ait;
		//	if ((ait = grnds.find(&x)) != grnds.end()) a.grnd = *ait;
		//	else *(a.grnd = new alt) = x, grnds.insert(a.grnd);
	}
	a.rng = leq;
	static set<body*, ptrcmp<body>>::const_iterator bit;
	body* y = 0;
	for (auto x : b) {
		a.t.push_back(x.second);
		if ((bit=bodies.find(&x.first)) != bodies.end())
			a.push_back(*bit);
		else *(y=new body) = x.first, a.push_back(y), bodies.insert(y);
		// collect bodies for builtins. these arn't grounded
		if (y) for (size_t n = 0; n != x.second.size(); ++n)
			if (x.second[n] < 0 && has(a.bltngvars, x.second[n]))
				a.varbodies.insert({ x.second[n], a.back() });
	}
	auto d = deltail(a.varslen, h.size());
	a.ex = d.first, a.perm = d.second, as.insert(a);
}

void tables::get_form(const term_set& al, const term& h, set<alt>& as) {
	#ifndef TYPE_RESOLUTION
	size_t bits_l = bits - 2;
	#else
	size_t bits_l = bits;
	#endif

	auto t0 = al.begin();
	DBG(assert(t0->extype == term::FORM1 || t0->extype == term::FORM2));
	alt a;
	a.f.reset(new(pnft));

	const term_set anull;
	size_t varsh;
	varmap vm = get_varmap(h, al, varsh), vmh;
	varmap tmpvm = vm;
	a.f->varslen_h = varsh;
	a.f->varslen = vm.size();

	// TODO review since d is not what is always needed to decrease.
	// if (vm.size() != 0 && h.size() != vm.size()) {
	//	size_t d = h.size() - vm.size();
	//	for (auto &v : vm)
	//		v.second = v.second - d;
	//	}

	if (t0->extype == term::FORM1)
		handler_form1(a.f, t0->qbf.get(), vm, vmh, true);
	else
		handler_formh(a.f, t0->qbf.get(), vm, vmh);

	if (a.f->perm.size() == 0) {
		term t; t.resize(a.f->varslen);
		for (auto &v : vm) t[v.second] = v.first;
		a.f->perm = get_perm(t, tmpvm, a.f->varslen, bits_l);
	}

	//TODO review to reach an arity-increment permutation to handle head constants
	if (a.f->ex_h.size() == 0) {
		auto d = deltail(a.f->varslen, tmpvm.size(), bits_l);
		a.f->ex_h = d.first, a.f->perm_h = d.second;
	}
	a.f->varslen_h = varsh;
	as.insert(a);
	return;
}

//review
void replace_rel(const map<ntable, ntable>& m, vector<term>& x) {
	auto it = m.end();
	for (term& t : x) if (m.end() != (it = m.find(t[0]))) t[0] = it->second;
}

void replace_rel(const map<ntable, ntable>& m, flat_prog& p) {
	flat_prog q(move(p));
	for (vector<term> v : q) replace_rel(m, v), p.insert(v);
}

bool tables::get_rules(flat_prog &p) {

	if (!get_facts(p)) return false;
	if (opts.optimize) bdd::gc();

	map<term, set<term_set>> m;
	for (const auto& x : p)
		if (x.size() == 1) m[x[0]] = {};
		else m[x[0]].insert(term_set(x.begin() + 1, x.end()));

	set<rule> rs;
	varmap::const_iterator it;
	set<alt*, ptrcmp<alt>>::const_iterator ait;
	alt* aa;
	for (auto x : m) {
		if (x.second.empty()) continue;
		set<int_t> hvars;
		const term &t = x.first;
		rule r;
		if (t.neg) datalog = false;
		varmap v;
		r.neg = t.neg, r.tab = t.tab, r.eq = htrue, r.t = t; //TODO: review why we replicate t variables in r
		for (size_t n = 0; n != t.size(); ++n)
			if (t[n] >= 0) get_sym(t[n], n, t.size(), r.eq);
			else if (v.end()==(it = v.find(t[n]))) v.emplace(t[n], n);
			else r.eq = r.eq && from_sym_eq(n, it->second, t.size());
		set<alt> as;
		r.len = t.size();

		for (const term_set& al : x.second)
			if (al.begin()->extype == term::FORM1 ||
					al.begin()->extype == term::FORM2)
				get_form(al, t, as);
			else
				get_alt(al, t, as);
		for (alt x : as)
			if ((ait = alts.find(&x)) != alts.end())
				r.push_back(*ait);
			else *(aa = new alt) = x, r.push_back(aa), alts.insert(aa);
		rs.insert(r);
	}
	for (rule r : rs)
		tbls[r.t.tab].r.push_back(rules.size()), rules.push_back(r);
	sort(rules.begin(), rules.end(), [this](const rule& x, const rule& y) {
			return tbls[x.tab].priority > tbls[y.tab].priority; });
	return true;
}

void tables::get_var_ex(size_t arg, size_t args, bools& b) const {
	for (size_t k = 0; k != bits; ++k) b[pos(k, arg, args)] = true;
}

void tables::get_sym(int_t sym, size_t arg, size_t args, spbdd_handle& r) const{
	for (size_t k = 0; k != bits; ++k) r = r && from_bit(k, arg, args, sym);
}



pair<bools, uints> tables::deltail(size_t len1, size_t len2) const {
	bools ex(len1 * bits, false);
	uints perm = perm_init(len1 * bits);
	for (size_t n = 0; n != len1; ++n)
		for (size_t k = 0; k != bits; ++k)
			if (n >= len2) ex[pos(k, n, len1)] = true;
			else perm[pos(k, n, len1)] = pos(k, n, len2);
	return { ex, perm };
}

uints tables::addtail(size_t len1, size_t len2) const {
	uints perm = perm_init(len1 * bits);
	for (size_t n = 0; n != len1; ++n)
		for (size_t k = 0; k != bits; ++k)
			perm[pos(k, n, len1)] = pos(k, n, len2);
	return perm;
}

spbdd_handle tables::addtail(cr_spbdd_handle x, size_t len1, size_t len2) const{
	if (len1 == len2) return x;
	return x ^ addtail(len1, len2);
}

spbdd_handle tables::body_query(body& b, size_t) {
	if (b.tlast && b.tlast->b == tbls[b.tab].t->b) return b.rlast;
	b.tlast = tbls[b.tab].t;
	return b.rlast = (b.neg ? bdd_and_not_ex_perm : bdd_and_ex_perm)
		(b.q, tbls[b.tab].t, b.ex, b.perm);
}

auto handle_cmp = [](const spbdd_handle& x, const spbdd_handle& y) {
	return x->b < y->b;
};

/* Compute the substitutions that satisfy the given alternative in the context
 * of the tables computed during the previous step. Do this by finding the
 * intersection (conjunction) of the substitutions satisfying each body term
 * and existentially quantifying out variables that will not be exported by the
 * head. */

spbdd_handle tables::alt_query(alt& a, size_t /*DBG(len)*/) {
	if (a.f) {
		bdd_handles f; //form
		formula_query(a.f, f);
		//TODO: complete for any type, only for ints by now
		if (a.f->ex_h.size() != 0 ) {
			#ifndef TYPE_RESOLUTION
			append_num_typebits(f[0], a.f->varslen_h);
			#endif
			a.rlast = f[0];
		} else a.rlast = f[0] == hfalse ? hfalse : htrue;
		return a.rlast;
	}

	bdd_handles v1 = { a.rng, a.eq };

	for (size_t n = 0; n != a.size(); ++n) {
		spbdd_handle x = body_query(*a[n], a.varslen);
		if (hfalse == x) {
			// Move tuhis failing alternative to first position under the assumption
			// that it is likely to fail again and that we should not have to evaluate
			// the other bodies to find out.
			a.insert(a.begin(), a[n]), a.erase(a.begin() + n + 1);
			// Update the levels structure with the current database for proof trees
			if (opts.bproof != proof_mode::none) a.levels.emplace(nstep, hfalse);
			// If this body term is false, no more iterations are required to
			// determine that this alternative is false
			return hfalse;
		} else v1.push_back(x);
	}

	// NOTE: for over bdd arithmetic (currently handled as a bltin, although may change)
	// In case arguments/ATOMS are the same than last iteration,
	// here is were it should be avoided to recompute.
	spbdd_handle xg = a.grnd ? alt_query(*(a.grnd), 0) : htrue; // vars grounding query
	body_builtins(xg, &a, v1);
	// Put subquery results into canonical form to aid in recognizing repetitions
	sort(v1.begin(), v1.end(), handle_cmp);
	// Now we must combine the v1 subquery results in order to get an overall
	// query result
	if (v1 == a.last) {
		// The case that conjuncts are exactly the same as last time
		if(opts.bproof != proof_mode::none)
			a.levels.emplace(nstep, a.unquantified_last);
	} else if (opts.bproof == proof_mode::none) {
		// The case where the conjuncts changed but do not have to produce proof
		a.last = move(v1);
		a.rlast = bdd_and_many_ex_perm(a.last, a.ex, a.perm);
	} else {
		// The case where the conjuncts changed and we will have to produce proof
		a.last = move(v1);
		// Following value is needed as it contains all body variable instantiations
		a.unquantified_last = bdd_and_many(a.last);
		a.levels.emplace(nstep, a.unquantified_last);
		a.rlast = bdd_permute_ex(a.unquantified_last, a.ex, a.perm);
	}
	return a.rlast;
}

bool table::commit(DBG(size_t /*bits*/)) {
	if (add.empty() && del.empty()) return false;
	spbdd_handle x;
	if (add.empty()) x = t % bdd_or_many(move(del));
	else if (del.empty()) add.push_back(t), x = bdd_or_many(move(add));
	else {
		// check for any intersection between add and del
		sort(add.begin(), add.end(), handle_cmp);
		sort(del.begin(), del.end(), handle_cmp);
		auto ita = add.begin(), itd = del.begin();
		while (ita != add.end() && itd != del.end())
			if (handle_cmp(*ita, *itd)) ita++;
			else if (!handle_cmp(*itd, *ita)) // contradiction
				return (add.clear(), del.clear()), unsat = true;
			else itd++;
		spbdd_handle a = bdd_or_many(move(add)),
			d = bdd_or_many(move(del));
		x = (t || a) % d;
	}
	return x != t && (t = x, true);
}


bool tables::print_updates_check() {
	if (!opts.pu_states.size()) return true;
	else for (auto tab : opts.pu_states)
		if (tbls[tab].t == htrue) return true;
	return false;
}

char tables::fwd(progress& p) noexcept {
	for (rule& r : rules) {
		bdd_handles v(r.size());
		spbdd_handle x;
		for (size_t n = 0; n != r.size(); ++n)
			v[n] = alt_query(*r[n], r.len);
		if (v == r.last) { if (datalog) continue; x = r.rlast; }
		else r.last = v, x = r.rlast = bdd_or_many(move(v)) && r.eq;
		if (x == hfalse) continue;
		(r.neg ? tbls[r.tab].del : tbls[r.tab].add).push_back(x);
		if (populate_tml_update || (print_updates && print_updates_check())) 
			p.notify_update(*this, x, r);
	}
	bool b = false;
	//TODO just temp ugly static, move this out of fwd/pass in, or in tables.
	static map<ntable, set<term>> mhits;
	for (ntable tab = 0; (size_t)tab != tbls.size(); ++tab) {
		table& tbl = tbls[tab];
		if (tbl.is_builtin()) {
			DBG(assert(tbl.del.empty());) // negated builtin fail
			if (!tbl.add.empty()) {
				head_builtin(tbl.add, tbl, tab);
				tbl.add.clear();
				if (unsat || halt) return true;
			}
		}
		bool changes = tbl.commit(DBG(bits));
		b |= changes;
		if (tbl.unsat) return unsat = true;
	}
	return b;
}

bdd_handles tables::get_front() const {
	bdd_handles r(tbls.size());
	for (ntable n = 0; n != (ntable)tbls.size(); ++n) r[n] = tbls.at(n).t;
	return r;
}

bool tables::contradiction_detected() {
	error = true, o::err() << err_contradiction << endl;
#ifdef WITH_EXCEPTIONS
	throw contradiction_exception();
#endif
	return false;
}

bool tables::infloop_detected() {
	error = true, o::err() << err_infloop << endl;
#ifdef WITH_EXCEPTIONS
	throw infloop_exception();
#endif
	return false;
}

/* If this sequence of databases has a generalized fixpoint and there are
 * undefined points in it belonging to a visible relation, then we have an
 * infloop. */

bool tables::is_infloop() {
	// The variables in which the fixpoint will be placed if it exists
	bdd_handles trues, falses, undefineds;
	if(compute_fixpoint(trues, falses, undefineds)) {
		for(ntable n = 0; n < (ntable)undefineds.size(); n++) {
			// If this relation is visible then existince of undefined parts in it
			// constitute an infloop
			if(!tbls[n].hidden && undefineds[n] != bdd_handle::F) {
				return true;
			}
		}
	}
	return false;
}

// adds __fp__ fact and returns true if __fp__ fact does not exist
bool tables::add_fixed_point_fact() {
	static ntable tab;
	static spbdd_handle h = 0;
	if (!h) {
		tab = fixed_point_term.tab;
		tbls[tab].hidden = true;
		h = from_fact(fixed_point_term);	
	}
	if (tbls[tab].t != htrue) return tbls[tab].t = tbls[tab].t || h, true;
	return false;
}

bool tables::pfp(size_t nsteps, size_t break_on_step, progress& ps) {
	error = false;
	bdd_handles l = get_front();
	fronts.push_back(l);
	if (opts.bproof != proof_mode::none) levels.emplace_back(l);
	for (;;) {
		if (print_steps) o::inf() << "# step: " << nstep << endl;
		++nstep;

		bool fwd_ret = fwd(ps);

		if (halt) return true;
		bdd_handles l = get_front();

		if (!fwd_ret && opts.fp_step && add_fixed_point_fact()) return pfp(0, 0, ps);

		fronts.push_back(l);
		if (halt) return true;
		if (unsat) return contradiction_detected();
		if ((break_on_step && nstep == break_on_step) ||
			(nsteps && nstep == nsteps)) return false; // no FP yet
		bool is_repeat = (!fwd_ret) ||
			(std::find(fronts.begin(), fronts.end() - 1, l) != fronts.end() - 1);
		if (opts.bproof != proof_mode::none) levels.push_back(move(l));
		if (is_repeat) return is_infloop() ? infloop_detected() : true;
	}
	DBGFAIL;
}

/* Run the given program on the given extensional database and yield
 * the derived facts. Returns true or false depending on whether the
 * given program reaches a fixed point. Useful for query containment
 * checks. */



tables::tables(rt_options opts_, builtins &bltins_) : opts(opts_), bltins(bltins_) {}

tables::~tables() {
	while (!bodies.empty()) {
		body *b = *bodies.begin();
		bodies.erase(bodies.begin());
		delete b;
	}
	while (!alts.empty()) {
		alt *a = *alts.begin();
		alts.erase(alts.begin());
		delete a;
	}
}

//-----------------------------------------------------------------------------
// decompress - out

#ifdef DEBUG
vbools tables::allsat(spbdd_handle x, size_t args) const {
	vbools v = ::allsat(x, bits * args), s;
	for (bools b : v) {
		s.emplace_back(bits * args);
		for (size_t n = 0; n != bits; ++n)
			for (size_t k = 0; k != args; ++k)
				s.back()[(k+1)*bits-n-1] = b[pos(n, k, args)];
	}
	return s;
}
#endif

/* If this sequence of databases has a generalized fixpoint, then compute it and
 * return true, otherwise return false. The true points in the generalized
 * fixpoint are those that remain true throughout a cycle, those that are false
 * never occur in the final cycle, and the undefined points comprise the
 * rest. */

bool tables::compute_fixpoint(bdd_handles &trues, bdd_handles &falses, bdd_handles &undefineds) {
	const int_t fronts_size = fronts.size(), tbls_size = tbls.size();
	if(fronts_size < 2 ||
			std::find(fronts.begin(), fronts.end()-1, fronts.back()) ==
			fronts.end()-1) {
		// There cannot be a fixpoint if there are less than two fronts or
		// if there do not exist two equal fronts
		return false;
	} else {
		// If FO(3-PFP) semantics are in effect
		// Determine which facts are true, false, and undefined
		trues.resize(tbls_size);
		falses.resize(tbls_size);
		undefineds.resize(tbls_size);
		// Loop back to the first repetition of the last front. It is clear
		// that the set of intervening fronts are periodic
		int_t cycle_start;
		for(cycle_start = fronts_size - 2;
			fronts[cycle_start] != fronts.back(); cycle_start--);
		// Make a buffer to hold the sequence of states a single table
		// eventually cycles through
		bdd_handles cycle(fronts_size - 1 - cycle_start);
		// For each table, compute which facts are true, false, and
		// undefined respectively
		for(ntable n = 0; n < (ntable)tbls_size; n++) {
			// Compute the eventual cycle of the current table
			for(int_t i = cycle_start + 1; i < fronts_size; i++) {
				cycle[i - cycle_start - 1] = fronts[i][n];
			}
			// True facts are those for which there exists an I such that
			// for all i>=I, the fact is a member of front i
			trues[n] = bdd_and_many(cycle);
			// False facts are those for which there exists an I such that
			// for all i>=I, the fact is not a member of front i
			falses[n] = htrue % bdd_or_many(cycle);
			// Undefined facts are those which are neither true nor false
			undefineds[n] = htrue % (trues[n] || falses[n]);
		}
		return true;
	}
}

void tables::decompress(spbdd_handle x, ntable tab, const cb_decompress& f,
	size_t len, bool allowbltins) const {
	table tbl = tbls.at(tab);
	if (!allowbltins && tbl.is_builtin()) return; //bltins no decompress
	if (!len) len = tbl.len;
	allsat_cb(x, len * bits,
		[tab, &f, &tbl, len, this](const bools& p, bdd_ref  DBG(y)) {
		DBG(assert(BDD_ABS(y) == T);)
		term r(false, term::REL, NOP, tab, ints(len, 0), 0);
		for (size_t n = 0; n != len; ++n)
			for (size_t k = 0; k != bits; ++k)
				if (p[pos(k, n, len)])
					r[n] |= 1 << k;

		#ifdef BIT_TRANSFORM
		// FIXME Move code to driver/progress monitor
		#endif

		f(r);
	})();
}

set<term> tables::decompress() {
	set<term> r;
	for (ntable tab = 0; (size_t)tab != tbls.size(); ++tab)
		decompress(tbls[tab].t, tab, [&r](const term& t) {r.insert(t);});
	return r;
}


#ifdef __EMSCRIPTEN__
// o is `tabular_collector` - JS object with methods:
// - length(relation_name) - returns number of rows (or index of next new row)
// - set(relation_name, row, col, value) - sets value of the cell of a table
void tables::out(emscripten::val o) const {
	out([&o](const raw_term& t) {
		string relation = to_string(lexeme2str(t.e[0].e));
		int row = o.call<int>("length", relation);
		int col = 0;
		for (size_t ar = 0, n = 1; ar != t.arity.size();) {
			ostringstream es;
			while (t.arity[ar] == -1) ++ar, es << '(';
			if (n >= t.e.size()) break;
			while (t.e[n].type == elem::OPENP) ++n;
			for (int_t k = 0; k != t.arity[ar];)
				if ((es<<t.e[n++]),++k!=t.arity[ar]) {
					o.call<void>("set", relation, row,col++,
						es.str());
					es.str("");
				}
			while (n<t.e.size() && t.e[n].type == elem::CLOSEP) ++n;
			++ar;
			while (ar < t.arity.size()
				&& t.arity[ar] == -2) ++ar, es<<')';
			if (es.str() != "")
				o.call<void>("set", relation, row, col++,
					es.str());
		}
	});
}
#endif
