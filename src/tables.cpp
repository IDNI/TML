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

#include "tables.h"
#include "dict.h"
#include "input.h"
#include "output.h"
using namespace std;

#define mkchr(x) (opts.bitunv? ((int_t)(x)):(((((int_t)(x))<<2)|1)))
#define mknum(x) (opts.bitunv? ((int_t)(x)):(((((int_t)(x))<<2)|2)))

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

map<size_t, int_t> varmap_inv(const varmap& vm) {
	map<size_t, int_t> inv;
	for (auto x : vm) {
		assert(!has(inv, x.second));
		inv.emplace(x.second, x.first);
	}
	return inv;
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

void tables::range(size_t arg, size_t args, bdd_handles& v) {
	spbdd_handle	ischar= ::from_bit(pos(0, arg, args), true) &&
			::from_bit(pos(1, arg, args), false);
	spbdd_handle	isnum = ::from_bit(pos(0, arg, args), false) &&
			::from_bit(pos(1, arg, args), true);
	spbdd_handle	issym = ::from_bit(pos(0, arg, args), false) &&
			::from_bit(pos(1, arg, args), false);
	// ir_handler->nums is set to max NUM, not universe size. While for ir_handler->syms it's the size.
	// It worked before because for arity==1 fact(ir_handler->nums) is always negated.
	bdd_handles r = {ischar || isnum || issym,
		(!ir_handler->chars	? htrue%ischar : bdd_impl(ischar,
			leq_const(mkchr(ir_handler->chars-1), arg, args, bits))),
		(!ir_handler->nums 	? htrue%isnum : bdd_impl(isnum,
			leq_const(mknum(ir_handler->nums), arg, args, bits))),
		(!ir_handler->syms 	? htrue%issym : bdd_impl(issym,
			leq_const(((ir_handler->syms-1)<<2), arg, args, bits)))};
	v.insert(v.end(), r.begin(), r.end());
}

spbdd_handle tables::range(size_t arg, ntable tab) {
	array<int_t, 6> k = { ir_handler->syms, ir_handler->nums, ir_handler->chars, (int_t)tbls[tab].len,
		(int_t)arg, (int_t)bits };
	auto it = range_memo.find(k);
	if (it != range_memo.end()) return it->second;
	bdd_handles v;
	return	range(arg, tbls[tab].len, v),
		range_memo[k] = bdd_and_many(move(v));
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
	range_clear_memo();
	spbdd_handle x = hfalse;
	bdd_handles v;
	for (auto& x : tbls)
//	for (size_t n = 0; n != ts.size(); ++n)
//		x.second.t = add_bit(x.second.t, x.second.len);
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
		else if (vs.emplace(t[n], n), !t.neg)
			r = r && range(n, t.tab);
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

spbdd_handle tables::get_alt_range(const term& h, const term_set& a,
	const varmap& vm, size_t len) {
	set<int_t> pvars, nvars, eqvars, leqvars, arithvars;
	vector<const term*> eqterms, leqterms, arithterms;
	// first pass, just enlist eq terms (that have at least one var)
	for (const term& t : a) {
		bool haseq = false, hasleq = false;
		for (size_t n = 0; n != t.size(); ++n)
			if (t[n] >= 0) continue;
			else if (t.extype == term::EQ) haseq = true; // .iseq
			else if (t.extype == term::LEQ) hasleq = true; // .isleq
			else (t.neg ? nvars : pvars).insert(t[n]);
		// TODO: BLTINS: add term::BLTIN handling
		// only if iseq and has at least one var
		if (haseq) eqterms.push_back(&t);
		else if (hasleq) leqterms.push_back(&t);
	}
	for (const term* pt : eqterms) {
		const term& t = *pt;
		bool noeqvars = true;
		vector<int_t> tvars;
		for (size_t n = 0; n != t.size(); ++n)
			if (t[n] >= 0) continue;
			// nvars add range already, so skip all in that case...
			// and per 1.3 - if any one is contrained (outside) bail
			// out
			else if (has(nvars, t[n])) { noeqvars = false; break; }
			// if neither pvars has this var it should be ranged
			else if (!has(pvars, t[n])) tvars.push_back(t[n]);
			else if (!t.neg) { noeqvars = false; break; }
			// if is in pvars and == then other var is covered too,
			// skip. this isn't covered by 1.1-3 (?) but further
			// optimization.
		if (noeqvars)
			for (const int_t tvar : tvars)
				eqvars.insert(tvar);
			// 1.3 one is enough (we have one constrained, no need
			// to do both). but this doesn't work well, we need to
			// range all that fit.
			//break;
	}
	for (const term* pt : leqterms) {
	// - for '>' (~(<=)) it's enough if 2nd var is in nvars/pvars.
		// - for '<=' it's enough if 2nd var is in nvars/pvars.
		// - if 1st/greater is const, still can't skip, needs to be
		// ranged.
		// - if neither var appears elsewhere (nvars nor pvars) => do
		// both.
		//   (that is a bit strange, i.e. if appears outside one is
		//   enough)
		// ?x > ?y => ~(?x <= ?y) => ?y - 2nd var is limit for both LEQ
		// and GT.
		const term& t = *pt;
		assert(t.size() == 2);
		const int_t v1 = t[0], v2 = t[1];
		if (v1 == v2) {
			if (!has(nvars, v2)) leqvars.insert(v2);
			continue;
		}
		if (v2 < 0) {
			if (has(nvars, v2) || has(pvars, v2))
				continue; // skip both
			leqvars.insert(v2); // add and continue to 1st
		}
		if (v1 < 0 && !has(nvars, v1) && !has(pvars, v1))
			leqvars.insert(v1);
	}

	for (int_t i : pvars) nvars.erase(i);
	if (h.neg) for (int_t i : h) if (i < 0)
		nvars.erase(i), eqvars.erase(i), leqvars.erase(i); // arithvars.erase(i);
	bdd_handles v;
	for (int_t i : nvars) range(vm.at(i), len, v);
	for (int_t i : eqvars) range(vm.at(i), len, v);
	for (int_t i : leqvars) range(vm.at(i), len, v);
	if (!h.neg) {
		set<int_t> hvars;
		for (int_t i : h) if (i < 0) hvars.insert(i);
		for (const term& t : a) for (int_t i : t) hvars.erase(i);
		for (int_t i : hvars) range(vm.at(i), len, v);
	}
	return bdd_and_many(v);
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
		else	b.q = b.q && from_sym_eq(n, it->second, t.size()),
			get_var_ex(n, t.size(), b.ex);
	return b;
}

bool tables::get_facts(const flat_prog& m) {
	map<ntable, set<spbdd_handle>> add, del;
	for (const auto& r : m)
		if (r.size() != 1) continue;
		else if (r[0].goal) goals.insert(r[0]);
		else if (r[0].is_builtin()) fact_builtin(r[0]);
		else (r[0].neg ? del : add)[r[0].tab].insert(from_fact(r[0]));
	if (unsat || halt) return false;
	clock_t start{}, end;
	if (opts.optimize) measure_time_start();
	bdd_handles v;
	for (auto x : add) for (auto y : x.second)
		tbls[x.first].t = tbls[x.first].t || y;
	for (auto x : del) {
		for (auto y : x.second) tbls[x.first].t = tbls[x.first].t % y;
	}
	if (opts.optimize)
		(o::ms() << "# get_facts: "),
		measure_time_end();
	return true;
}

int_t tables::freeze(vector<term>& v, int_t m = 0) {
	map<int_t, int_t> p;
	map<int_t, int_t>::const_iterator it;
	for (const term& t : v) for (int_t i : t)
		if (opts.bitunv && (i ==0 || i == 1 )) m = max(m, i);
		else if (i & 2) m = max(m, i >> 2);
	for (term& t : v)
		for (int_t& i : t)
			if (i >= 0) continue;
			else if ((it = p.find(i)) != p.end()) i = it->second;
			else p.emplace(i, mknum(m)), i = mknum(m++);
	return m;
}

flat_prog& tables::get_canonical_db(vector<term>& x, flat_prog& p) {
	freeze(x);
	for (size_t n = 1; n != x.size(); ++n) p.insert({x[n]});
	return p;
}

flat_prog& tables::get_canonical_db(vector<vector<term>>& x, flat_prog& p) {
	int_t m = 0;
	for (vector<term>& v : x)
		for (const term& t : v)
			for (int_t i : t)
				if (opts.bitunv && (i == 1 || i == 0) ) m = max(m, i);
				else if (i & 2) m = max(m, i >> 2);
	for (vector<term>& t : x) {
		freeze(t, m);
		for (size_t n = 1; n != t.size(); ++n) p.insert({t[n]});
	}
	return p;
}

void tables::run_internal_prog(flat_prog p, set<term>& r, size_t nsteps) {
	dict_t tmpdict(dict); // copy ctor, only here, if this's needed at all?
	rt_options tmpopts(opts);
	tables t(tmpdict, tmpopts, ir_handler);
	if (!t.run_nums(move(p), r, nsteps)) { DBGFAIL; }
}

void create_head(vector<term>&, ntable) {
/*	set<int_t> v;
	getvars(x, v);
	term h;
	h.tab = tab, h.insert(h.begin(), vx.begin(), vx.end());
	x.insert(x.begin(), move(h));*/
}

void replace_rel(const map<ntable, ntable>& m, vector<term>& x) {
	auto it = m.end();
	for (term& t : x) if (m.end() != (it = m.find(t[0]))) t[0] = it->second;
}

void replace_rel(const map<ntable, ntable>& m, flat_prog& p) {
	flat_prog q(move(p));
	for (vector<term> v : q) replace_rel(m, v), p.insert(v);
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

bool tables::handler_leq(const term& t, const varmap& vm, const size_t vl,
		spbdd_handle &c) const {
	DBG(assert(t.size() == 2););
	spbdd_handle q = bdd_handle::T;
	if (t[0] == t[1]) return !(t.neg);
	if (t[0] >= 0 && t[1] >= 0) return !(t.neg == (t[0] <= t[1]));
	if (t[0] < 0 && t[1] < 0)
		q = leq_var(vm.at(t[0]), vm.at(t[1]), vl, bits);
	else if (t[0] < 0)
		q = leq_const(t[1], vm.at(t[0]), vl, bits);
	else if (t[1] < 0)
		// 1 <= v1, v1 >= 1, ~(v1 <= 1) || v1==1.
		q = htrue % leq_const(t[0], vm.at(t[1]), vl, bits) ||
			from_sym(vm.at(t[1]), vl ,t[0]);
	c = t.neg ? c % q : (c && q);
	return true;
}

void tables::get_alt(const term_set& al, const term& h, set<alt>& as, bool blt){
	alt a;
	set<pair<body, term>> b;
	spbdd_handle leq = htrue, q;
	a.vm = get_varmap(h, al, a.varslen, blt), a.inv = varmap_inv(a.vm);

	for (const term& t : al) {
		if (t.extype == term::REL) {
			b.insert({ get_body(t, a.vm, a.varslen), t });
		} else if (t.extype == term::EQ) {
			if (!handler_eq(t, a.vm, a.varslen, a.eq)) {a.eq = hfalse; break;}
		} else if (t.extype == term::LEQ) {
			if (!handler_leq(t, a.vm, a.varslen, leq)) {leq = hfalse; break;}
		} else if (t.extype == term::ARITH) {
			//arith constraint on leq
			if (!handler_arith(t,a.vm, a.varslen, leq)) assert(false),leq=hfalse;
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
		// TODO grnd alt sharing?
		//set<alt*, ptrcmp<alt>>::const_iterator ait;
		//	if ((ait = grnds.find(&x)) != grnds.end())
		//		a.grnd = *ait;
		//	else	*(a.grnd = new alt) = x,
		//		grnds.insert(a.grnd);
	}
	if (opts.bitunv) a.rng = leq;
	else a.rng = bdd_and_many({ get_alt_range(h, al, a.vm, a.varslen), leq });
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

lexeme tables::get_new_rel() {
	static size_t last = 1;
	string s = "r";
	size_t sz;
	lexeme l;
retry:	sz = dict.nrels(), l = dict.get_lexeme(s + to_string_(last));
	dict.get_rel(l);
	if (dict.nrels() == sz) { ++last; goto retry; }
	return l;
}

void tables::get_form(const term_set& al, const term& h, set<alt>& as) {
	auto t0 = al.begin();
	DBG(assert(t0->extype == term::FORM1 || t0->extype == term::FORM2));
	alt a;
	a.f.reset(new(pnft));

	const term_set anull;
	size_t varsh;
	varmap vm = get_varmap(h, al, varsh), vmh;
	varmap tmpvm = vm;
	//assert(varsh != 0 && "VARMAP error");
	a.f->varslen_h = varsh; //h.size()
	a.f->varslen = vm.size();

	/*
	//todo: review since d is not what is always needed to decrease
	if (vm.size() != 0 && h.size() != vm.size()) {
		size_t d = h.size() - vm.size();
		for (auto &v : vm)
			v.second = v.second - d;
	}
	*/

	if (t0->extype == term::FORM1)
		handler_form1(a.f, t0->qbf.get(), vm, vmh, true);
	else
		handler_formh(a.f, t0->qbf.get(), vm, vmh);

	if (a.f->perm.size() == 0) {
		term t; t.resize(a.f->varslen);
		for (auto &v : vm) t[v.second] = v.first;
		a.f->perm = get_perm(t, tmpvm, a.f->varslen, bits-2);
	}

	//todo: review to reach an arity-increment permutation to handle head constants
	if (a.f->ex_h.size() == 0) {
		auto d = deltail(a.f->varslen, tmpvm.size(), bits-2);
		a.f->ex_h = d.first, a.f->perm_h = d.second;
	}
	a.f->varslen_h = varsh;
	as.insert(a);
	return;
}

ntable tables::prog_add_rule(flat_prog& p, map<ntable, ntable>&,// r,
	vector<term> x) {
	return p.emplace(x), x[0].tab;
}

bool tables::get_rules(flat_prog p) {
	if (!get_facts(p)) return false;
	flat_prog q(move(p));
	map<ntable, ntable> r;
	for (const auto& x : q) prog_add_rule(p, r, x);
	replace_rel(move(r), p);
	q = move(p);
	for (const auto& x : q) prog_add_rule(p, r, x);
	replace_rel(move(r), p);
	if (opts.optimize) bdd::gc();

	// BLTINS: set order is important (and wrong) for e.g. REL, BLTIN, EQ
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
		r.neg = t.neg, r.tab = t.tab, r.eq = htrue, r.t = t; //XXX: review why we replicate t variables in r
		for (size_t n = 0; n != t.size(); ++n)
			if (t[n] >= 0) get_sym(t[n], n, t.size(), r.eq);
			else if (v.end()==(it=v.find(t[n]))) v.emplace(t[n], n);
			else r.eq = r.eq&&from_sym_eq(n, it->second, t.size());
		set<alt> as;
		r.len = t.size();

		for (const term_set& al : x.second)
			if (al.begin()->extype == term::FORM1 ||
					al.begin()->extype == term::FORM2)
				get_form(al, t, as);
			else
				get_alt(al, t, as);
		//if (as.size() == 0) COUT << " with 0 size" << endl;
		for (alt x : as)
			if ((ait = alts.find(&x)) != alts.end())
				r.push_back(*ait);
			else	*(aa = new alt) = x,
				r.push_back(aa), alts.insert(aa);
		//DBG(o::dbg() << "rule size (n. of alts): " << r.size() << endl;)
		//if (r.size() == 0) print(COUT << "rule 0: ", r) << endl;
		rs.insert(r);
	}
	for (rule r : rs)
		tbls[r.t.tab].r.push_back(rules.size()), rules.push_back(r);
	sort(rules.begin(), rules.end(), [this](const rule& x, const rule& y) {
			return tbls[x.tab].priority > tbls[y.tab].priority; });
	return true;
}

#define rdict() ((dict_t&)dict)
void tables::load_string(lexeme r, const string_t& s) {

	unary_string us(sizeof(char32_t)*8);
	us.buildfrom(s);
	//DBG(us.toprint(o::dbg()));
	for( auto it: us.rel ){
		int_t r = dict.get_rel(rdict().get_lexeme(us.getrelin_str(it.first)));
		term t; t.resize(1);
		ntable tb = get_table({r, {1} });
		t.tab =tb;
		bdd_handles b;
		b.reserve(it.second.size());
		for( int_t i :it.second)
			t[0]= mknum(i), b.push_back(from_fact(t));
		tbls[tb].t = bdd_or_many(b);
	}

	int_t rel = dict.get_rel(r);
	str_rels.insert(rel);

//	const ints ar = {0,-1,-1,1,-2,-2,-1,1,-2,-1,-1,1,-2,-2};
	const int_t sspace = dict.get_sym(dict.get_lexeme("space")),
		salpha = dict.get_sym(dict.get_lexeme("alpha")),
		salnum = dict.get_sym(dict.get_lexeme("alnum")),
		sdigit = dict.get_sym(dict.get_lexeme("digit")),
		sprint = dict.get_sym(dict.get_lexeme("printable"));
	term t,tb;
	bdd_handles b1, b2;
	b1.reserve(s.size()), b2.reserve(s.size()), t.resize(2), tb.resize(3);
	for (int_t n = 0; n != (int_t)s.size(); ++n) {
		t[0] = mknum(n), t[1] = mkchr(s[n]), // t[2] = mknum(n + 1),
		ir_handler->chars = max(ir_handler->chars, t[1]),
		b1.push_back(from_fact(t));
		tb[1] = t[0], tb[2] = mknum(0);
		if (isspace(s[n])) tb[0] = sspace, b2.push_back(from_fact(tb));
		if (isdigit(s[n])) tb[0] = sdigit, b2.push_back(from_fact(tb));
		if (isalpha(s[n])) tb[0] = salpha, b2.push_back(from_fact(tb));
		if (isalnum(s[n])) tb[0] = salnum, b2.push_back(from_fact(tb));
		if (isprint(s[n])) tb[0] = sprint, b2.push_back(from_fact(tb));
	}
	clock_t start{}, end;
	if (opts.optimize)
		(o::ms()<<"# load_string or_many: "),
		measure_time_start();
	ntable st = get_table({rel, {2}}); // str(pos char)
	ntable stb = get_table({rel, {3}}); // str(printable pos 0)

	tbls[st].t = bdd_or_many(move(b1));
	tbls[stb].t = bdd_or_many(move(b2));
	if (opts.optimize) measure_time_end();
}

/*template<typename T> bool subset(const set<T>& small, const set<T>& big) {
	for (const T& t : small) if (!has(big, t)) return false;
	return true;
}*/

void tables::get_var_ex(size_t arg, size_t args, bools& b) const {
	for (size_t k = 0; k != bits; ++k) b[pos(k, arg, args)] = true;
}

void tables::get_sym(int_t sym, size_t arg, size_t args, spbdd_handle& r) const{
	for (size_t k = 0; k != bits; ++k) r = r && from_bit(k, arg, args, sym);
}

ntable tables::get_table(const sig& s) {
	auto it = smap.find(s);
	if (it != smap.end()) return it->second;
	ntable nt = tbls.size();
	size_t len = ir_handler->sig_len(s);
	max_args = max(max_args, len);
	table tb;
	return	tb.t = hfalse, tb.s = s, tb.len = len,
		tbls.push_back(tb), smap.emplace(s,nt), nt;
}

term tables::to_nums(term t) {
	for (int_t& i : t)  if (i > 0) i = mknum(i);
	return t;
}

//term from_nums(term t) {
//	for (int_t& i : t)  if (i > 0) i >>= 2;
//	return t;
//}

vector<term> tables::to_nums(const vector<term>& v) {
	vector<term> r;
	for (const term& t : v) r.push_back(to_nums(t));
	return r;
}

//set<term> from_nums(const set<term>& s) {
//	set<term> ss;
//	for (const term& t : s) ss.insert(from_nums(t));
//	return ss;
//}

void tables::to_nums(flat_prog& m) {
	flat_prog mm;
	for (auto x : m) mm.insert(to_nums(x));
	m = move(mm);
}

ntable tables::get_new_tab(int_t x, ints ar) { return get_table({ x, ar }); }

bool tables::add_prog(const raw_prog& p, const strs_t& strs_) {
	strs = strs_;
	if (!strs.empty()) {
		//ir_handler->chars = 255,
		dict.get_sym(dict.get_lexeme("space")),
		dict.get_sym(dict.get_lexeme("alpha")),
		dict.get_sym(dict.get_lexeme("alnum")),
		dict.get_sym(dict.get_lexeme("digit")),
		dict.get_sym(dict.get_lexeme("printable"));
		for (auto x : strs) {
			ir_handler->nums = max(ir_handler->nums, (int_t)x.second.size()+1);
			unary_string us(32);
			us.buildfrom(x.second);
			ir_handler->chars = max(ir_handler->chars, (int_t)us.rel.size());
		}
	}
	flat_prog fp = ir_handler->to_terms(p);
	return add_prog(fp, p.g);
}

bool tables::run_nums(flat_prog m, set<term>& r, size_t nsteps) {
	map<ntable, ntable> m1, m2;
	auto f = [&m1, &m2](ntable *x) {
		auto it = m1.find(*x);
		if (it != m1.end()) return *x = it->second;
		const int_t y = (int_t)m2.size();
		m1.emplace(*x, y), m2.emplace(y, *x);
		return *x = y;
	};
	auto g = [&m2](const set<term>& s) {
		set<term> r;
		for (term t : s) {
			auto it = m2.find(t.tab);
			if (it == m2.end()) r.insert(t);
			else t.tab = it->second, r.insert(t);
		}
		return r;
	};
	auto h = [this, f](const set<term>& s) {
		set<term> r;
		for (term t : s)
			get_table({ f(&t.tab), {(int_t)t.size()}}), r.insert(t);
		return r;
	};
	flat_prog p;
	for (vector<term> x : m) {
		get_table({ f(&x[0].tab), { (int_t)x[0].size() } });
		auto s = h(set<term>(x.begin() + 1, x.end()));
		x.erase(x.begin() + 1, x.end()),
		x.insert(x.begin() + 1, s.begin(), s.end()), p.insert(x);
	}
//	DBG(print(o::out()<<"run_nums for:"<<endl, p)<<endl<<"returned:"<<endl;)
	if (!add_prog(move(p), {})) return false;
	if (!pfp(nsteps)) return false;
	r = g(decompress());
	return true;
}

void tables::add_tml_update(const term& t, bool neg) {
	// TODO: decompose nstep if too big for the current universe
	ir_handler->nums = max(ir_handler->nums, (int_t)nstep);
	ints arity = tbls.at(t.tab).s.second;
	arity[0] += 3;
	ntable tab = get_table({ rel_tml_update, arity });
	ints args = { mknum(nstep), (neg ? sym_del : sym_add),
		dict.get_sym(dict.get_rel(tbls[t.tab].s.first)) };
	args.insert(args.end(), t.begin(), t.end());
	tbls[tab].add.push_back(from_fact(term(false, tab, args, 0, -1)));
}

template <typename T>
basic_ostream<T>& tables::decompress_update(basic_ostream<T>& os,
	spbdd_handle& x, const rule& r)
{
	if (print_updates) print(os << "#       ", r) << "\n#   ->  ";
	decompress(x, r.tab, [&os, &r, this](const term& x) {
		if (print_updates)
			os << (r.neg ? "~" : "") << ir_handler->to_raw_term(x) << ". ";
		if (populate_tml_update) add_tml_update(x, r.neg);
	});
	if (print_updates) os << endl;
	return os;
}

void tables::init_tml_update() {
	rel_tml_update = dict.get_rel(dict.get_lexeme("tml_update"));
	sym_add = dict.get_sym(dict.get_lexeme("add"));
	sym_del = dict.get_sym(dict.get_lexeme("delete"));
}

bool tables::add_prog(flat_prog m, const vector<production>& g, bool mknums) {
	error = false;
	smemo.clear(), ememo.clear(), leqmemo.clear();
	if (mknums) to_nums(m);
	if (populate_tml_update) init_tml_update();
	rules.clear(), datalog = true;
	ir_handler->syms = dict.nsyms();

	if (opts.bitunv) {
		bits = 1;
	} else {
		while (max(max(ir_handler->nums, ir_handler->chars), ir_handler->syms) >= (1 << (bits - 2)))
			add_bit();
	}

	for (auto x : strs) load_string(x.first, x.second);
	form *froot;
	if (!ir_handler->transform_grammar(g, m, froot)) return false;
	if (!get_rules(move(m))) return false;

	// filter for rels starting and ending with __
	auto filter_internal_tables = [] (const lexeme& l) {
		size_t len = l[1] - l[0];
		return len > 4 && '_' == l[0][0]     && '_' == l[0][1] &&
				  '_' == l[0][len-2] && '_' == l[0][len-1];
	};
	ints internal_rels = dict.get_rels(filter_internal_tables);
	for (auto& tbl : tbls)
		for (int_t rel : internal_rels)
			if (rel == tbl.s.first) { tbl.hidden = true; break; }

	if (opts.optimize) bdd::gc();
	return true;
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

spbdd_handle tables::body_query(body& b, size_t /*DBG(len)*/) {
//	DBG(assert(bdd_nvars(b.q) <= b.ex.size());)
//	DBG(assert(bdd_nvars(get_table(b.tab, db)) <= b.ex.size());)
	if (b.tlast && b.tlast->b == tbls[b.tab].t->b) return b.rlast;
	b.tlast = tbls[b.tab].t;
	return b.rlast = (b.neg ? bdd_and_not_ex_perm : bdd_and_ex_perm)
		(b.q, tbls[b.tab].t, b.ex, b.perm);
//	DBG(assert(bdd_nvars(b.rlast) < len*bits);)
//	if (b.neg) b.rlast = bdd_and_not_ex_perm(b.q, ts[b.tab].t, b.ex,b.perm);
//	else b.rlast = bdd_and_ex_perm(b.q, ts[b.tab].t, b.ex, b.perm);
//	return b.rlast;
//	return b.rlast = bdd_permute_ex(b.neg ? b.q % ts[b.tab].t :
//			(b.q && ts[b.tab].t), b.ex, b.perm);
}

auto handle_cmp = [](const spbdd_handle& x, const spbdd_handle& y) {
	return x->b < y->b;
};

spbdd_handle tables::alt_query(alt& a, size_t /*DBG(len)*/) {
	if (a.f) {
		bdd_handles f; //form
		formula_query(a.f, f);
		//TODO: complete for any type, only for ints by now
		if (a.f->ex_h.size() != 0 ) {
			append_num_typebits(f[0], a.f->varslen_h);
			a.rlast = f[0];
		}
		else a.rlast = f[0] == hfalse ? hfalse : htrue;
		return a.rlast;
	}

	bdd_handles v1 = { a.rng, a.eq };
	spbdd_handle x;
	//DBG(assert(!a.empty());)

	for (size_t n = 0; n != a.size(); ++n)
		if (hfalse == (x = body_query(*a[n], a.varslen))) {
			a.insert(a.begin(), a[n]), a.erase(a.begin() + n + 1);
			return hfalse;
		} else v1.push_back(x);

	//NOTE: for over bdd arithmetic (currently handled as a bltin, although may change)
	// In case arguments/ATOMS are the same than last iteration,
	// here is were it should be avoided to recompute.
	spbdd_handle xg = htrue;
	if (a.grnd) xg = alt_query(*(a.grnd), 0); // vars grounding query
	body_builtins(xg, &a, v1);

	sort(v1.begin(), v1.end(), handle_cmp);
	if (v1 == a.last) return a.rlast;// { v.push_back(a.rlast); return; }
	if (!opts.bproof) return a.rlast =
		bdd_and_many_ex_perm(a.last = move(v1), a.ex, a.perm);
	a.levels.emplace(nstep, x = bdd_and_many(v1));
//	if ((x = bdd_and_many_ex(a.last, a.ex)) != hfalse)
//		v.push_back(a.rlast = x ^ a.perm);
//	bdd_handles v;
	return a.rlast = bdd_permute_ex(x, a.ex, a.perm);
//	if ((x = bdd_and_many_ex_perm(a.last, a.ex, a.perm)) != hfalse)
//		v.push_back(a.rlast = x);
//	return x;
//	DBG(assert(bdd_nvars(a.rlast) < len*bits);)
}

bool table::commit(DBG(size_t /*bits*/)) {
	if (add.empty() && del.empty()) return false;
	spbdd_handle x;
	if (add.empty()) x = t % bdd_or_many(move(del));
	else if (del.empty()) add.push_back(t), x = bdd_or_many(move(add));
	else {
		spbdd_handle a = bdd_or_many(move(add)),
				 d = bdd_or_many(move(del)), s = a % d;
//		DBG(assert(bdd_nvars(a) < len*bits);)
//		DBG(assert(bdd_nvars(d) < len*bits);)
		if (s == hfalse) return unsat = true;
		x = (t || a) % d;
	}
//	DBG(assert(bdd_nvars(x) < len*bits);)
	return x != t && (t = x, true);
}

char tables::fwd() noexcept {
	for (rule& r : rules) {
		if (r.size() == 0) {
			COUT << "r.size() = 0" << endl;
			print(COUT, r) << endl;
		}
		bdd_handles v(r.size() == 0 ? 1 : r.size());
		spbdd_handle x;
		for (size_t n = 0; n != r.size(); ++n)
			//print(COUT << "rule: ", r) << endl,
			v[n] = alt_query(*r[n], r.len);
		if (v == r.last) { if (datalog) continue; x = r.rlast; }
		else r.last = v, x = r.rlast = bdd_or_many(move(v)) && r.eq;
		//DBG(assert(bdd_nvars(x) < r.len*bits);)
		if (x == hfalse) continue;
		(r.neg ? tbls[r.tab].del : tbls[r.tab].add).push_back(x);
		if (print_updates || populate_tml_update)
			decompress_update(o::inf(), x, r);
	}
	bool b = false;
	// D: just temp ugly static, move this out of fwd/pass in, or in tables.
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
/*	if (!b) return false;
	for (auto x : goals)
		for (auto y : x.second)
			b &= (y && ts[x.first].t) == y;
	if (b) return (o::out() <<"found"<<endl), false;
	return b;*/
}

level tables::get_front() const {
	level r(tbls.size());
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

// adds __fp__ fact and returns true if __fp__ fact does not exist
bool tables::add_fixed_point_fact() {
	raw_term rt;
	rt.arity = { 0 };
	rt.e.emplace_back(elem::SYM, dict.get_lexeme(string("__fp__")));
	term t = ir_handler->from_raw_term(rt);
	bool exists = false;
	decompress(tbls[t.tab].t && from_fact(t), t.tab,
		[&exists](const term& /*t*/) { exists = true; }, t.size());
	if (!exists) tbls[t.tab].t = tbls[t.tab].t || from_fact(t); // add if ne
	tbls[t.tab].hidden = true;
	return !exists;
}

bool tables::pfp(size_t nsteps, size_t break_on_step) {
	error = false;
	level l = get_front();
	fronts.push_back(l);
	if (opts.bproof) levels.emplace_back(l);
	for (;;) {
		if (print_steps || opts.optimize)
			o::inf() << "# step: " << nstep << endl;
		++nstep;
		bool fwd_ret = fwd();
		if (halt) return true;
		level l = get_front();
		if (!fwd_ret) {
			if(opts.fp_step && add_fixed_point_fact()) return pfp();
			else return fronts.push_back(l), true;
		} else  fronts.push_back(l);
		if (halt) return true;
		if (unsat) return contradiction_detected();
		if ((break_on_step && nstep == break_on_step) ||
			(nsteps && nstep == nsteps)) return false; // no FP yet
		bool is_repeat =
			std::find(fronts.begin(), fronts.end() - 1, l) != fronts.end() - 1;
		if (!datalog && is_repeat)
			return opts.semantics == semantics::pfp3 ? true : infloop_detected();
		if (opts.bproof) levels.push_back(move(l));
	}
	DBGFAIL;
}

/* Run the given program with the given settings, put the query
 * results into the given out-parameter, and return true in the case
 * that it reaches a fixed point. Otherwise just return false. */

bool tables::run_prog(const raw_prog &rp, dict_t &dict, const options &opts,
		ir_builder *ir_handler, std::set<raw_term> &results)
{
	rt_options to;
	to.bproof            = opts.enabled("proof");
	to.optimize          = opts.enabled("optimize");
	to.print_transformed = opts.enabled("t");
	to.apply_regexpmatch = opts.enabled("regex");
	tables tbl(dict, to, ir_handler);
	strs_t strs;
	if(tbl.run_prog(rp, strs)) {
		for(const term &result : tbl.decompress()) {
			results.insert(tbl.ir_handler->to_raw_term(result));
		}
		return true;
	} else {
		return false;
	}
}

/* Run the given program on the given extensional database and yield
 * the derived facts. Returns true or false depending on whether the
 * given program reaches a fixed point. Useful for query containment
 * checks. */

bool tables::run_prog(const std::set<raw_term> &edb, raw_prog rp,
	dict_t &dict, const ::options &opts, ir_builder *ir_handler,
	std::set<raw_term> &results)
{
	std::map<elem, elem> freeze_map, unfreeze_map;
	// Create a duplicate of each rule in the given program under a
	// generated alias.
	for(int_t i = rp.r.size() - 1; i >= 0; i--) {
		for(raw_term &rt : rp.r[i].h) {
			raw_term rt2 = rt;
			auto it = freeze_map.find(rt.e[0]);
			if(it != freeze_map.end()) {
				rt.e[0] = it->second;
			} else {
				elem frozen_elem = elem::fresh_temp_sym(dict);
				// Store the mapping so that the derived portion of each
				// relation is stored in exactly one place
				unfreeze_map[frozen_elem] = rt.e[0];
				rt.e[0] = freeze_map[rt.e[0]] = frozen_elem;
			}
			rp.r.push_back(raw_rule(rt2, rt));
		}
	}
	// Now add the extensional database to the given program.
	for(const raw_term &rt : edb) {
		rp.r.push_back(raw_rule(rt));
	}
	// Run the program to obtain the results which we will then filter
	std::set<raw_term> tmp_results;
	bool result = run_prog(rp, dict, opts, ir_handler, tmp_results);
	// Filter out the result terms that are not derived and rename those
	// that are derived back to their original names.
	for(raw_term res : tmp_results) {
		auto jt = unfreeze_map.find(res.e[0]);
		if(jt != unfreeze_map.end()) {
			res.e[0] = jt->second;
			results.insert(res);
		}
	}
	return result;
}

bool tables::run_prog(const raw_prog& p, const strs_t& strs, size_t steps,
	size_t break_on_step)
{
	clock_t start{}, end;
	double t;
	if (opts.optimize) measure_time_start();
	if (opts.bitunv) this->typenv = const_cast<raw_prog&>(p).get_typenv();
	if (!add_prog(p, strs)) return false;
	if (opts.optimize) {
		end = clock(), t = double(end - start) / CLOCKS_PER_SEC;
		o::ms() << "# pfp: ";
		measure_time_start();
	}
	DBG(o::dbg()<<endl<<p<<endl);

	nlevel begstep = nstep;
	bool r = true;
	// run program only if there are any rules
	if (rules.size()) {
		fronts.clear();
		r = pfp(steps ? nstep + steps : 0, break_on_step);
	} else {
		level l = get_front();
		fronts = {l, l};
	}
	size_t went = nstep - begstep;
	if (r && prog_after_fp.size()) {
		if (!add_prog(move(prog_after_fp), {}, false)) return false;
		r = pfp();
	}
	if (r && p.nps.size()) { // after a FP run the seq. of nested progs
		for (const raw_prog& np : p.nps) {
			steps -= went; begstep = nstep;
			r = run_prog(np, strs, steps, break_on_step);
			went = nstep - begstep;
			if (!r && went >= steps) break;
		}
	}
	if (opts.optimize)
		(o::ms() <<"add_prog: "<<t << " pfp: "),
		measure_time_end();
	return r;
}

tables::tables(dict_t& dict, rt_options opts, ir_builder* ir_handler_) :
	dict(dict), opts(opts), ir_handler(ir_handler_) {
	init_builtins();
}

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
//	const size_t args = siglens[tab];
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

template <typename T>
void tables::out(basic_ostream<T>& os) const {
	//strs_t::const_iterator it;
	for (ntable tab = 0; (size_t)tab != tbls.size(); ++tab) {
//		if ((it = strs.find(dict.get_rel(tab))) == strs.end())
		if (opts.show_hidden || !tbls[tab].hidden) out(os, tbls[tab].t, tab);
//		else os << it->first << " = \"" << it->second << '"' << endl;
	}
}

template void tables::out<char>(ostream& os) const;
template void tables::out<wchar_t>(wostream& os) const;

/* Print out the fixpoint associated with this sequence of databases and
 * return true. Return false if this sequence of databases contains no
 * repeats. */

template <typename T>
bool tables::out_fixpoint(basic_ostream<T>& os) {
	const int_t fronts_size = fronts.size(), tbls_size = tbls.size();
	if(fronts_size < 2 ||
			std::find(fronts.begin(), fronts.end()-1, fronts.back()) ==
			fronts.end()-1) {
		// There cannot be a fixpoint if there are less than two fronts or
		// if there do not exist two equal fronts
		return false;
	} else if (opts.semantics == semantics::pfp3) {
		// If FO(3-PFP) semantics are in effect
		// Determine which facts are true, false, and undefined
		level trues(tbls_size), falses(tbls_size), undefineds(tbls_size);
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
		// Print out the true points separately
		os << "true points:" << endl;
		bool exists_trues = false;
		for(ntable n = 0; n < (ntable)tbls_size; n++) {
			if(opts.show_hidden || !tbls[n].hidden) {
				decompress(trues[n], n, [&os, &exists_trues, this](const term& r) {
					os << ir_handler->to_raw_term(r) << '.' << endl;
					exists_trues = true; });
			}
		}
		if(!exists_trues) os << "(none)" << std::endl;

		// Finally print out the undefined points separately
		os << endl << "undefined points:" << endl;
		bool exists_undefineds = false;
		for(ntable n = 0; n < (ntable)tbls_size; n++) {
			if(opts.show_hidden || !tbls[n].hidden) {
				decompress(undefineds[n], n, [&os, &exists_undefineds, this](const term& r) {
					os << ir_handler->to_raw_term(r) << '.' << endl;
					exists_undefineds = true; });
			}
		}
		if(!exists_undefineds) os << "(none)" << std::endl;
		return true;
	} else if(opts.semantics == semantics::pfp) {
		if(fronts.back() == fronts[fronts_size - 2]) {
			// If FO(PFP) semantics are in effect and the last two fronts are
			// equal then print them; this is the fixpoint.
			level &l = fronts.back();
			for(ntable n = 0; n < (ntable)tbls_size; n++) {
				if (opts.show_hidden || !tbls[n].hidden)
					decompress(l[n], n, [&os, this](const term& r) {
						os << ir_handler->to_raw_term(r) << '.' << endl; });
			}
			return true;
		} else {
			// If FO(PFP) semantics are in effect and two equal fronts are
			// separated by an unequal front; then the fixpoint is empty.
			return true;
		}
	}
}

template bool tables::out_fixpoint<char>(ostream& os);
template bool tables::out_fixpoint<wchar_t>(wostream& os);

void tables::out(const rt_printer& f) const {
	for (ntable tab = 0; (size_t)tab != tbls.size(); ++tab)
		if (opts.show_hidden || !tbls[tab].hidden) out(tbls[tab].t, tab, f);
}

template <typename T>
void tables::out(basic_ostream<T>& os, spbdd_handle x, ntable tab) const {
	if (opts.show_hidden || !tbls[tab].hidden) // don't print internal tables.
		out(x, tab, [&os](const raw_term& rt) { os<<rt<<'.'<<endl; });
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

void tables::decompress(spbdd_handle x, ntable tab, const cb_decompress& f,
	size_t len, bool allowbltins) const {
	table tbl = tbls.at(tab);
	// D: bltins are special type of REL-s, mostly as any but no decompress.
	if (!allowbltins && tbl.is_builtin()) return;
	if (!len) len = tbl.len;
	allsat_cb(x/*&&ts[tab].t*/, len * bits,
		[tab, &f, len, this](const bools& p, int_t DBG(y)) {
		DBG(assert(abs(y) == 1);)
		term r(false, term::REL, NOP, tab, ints(len, 0), 0);
		for (size_t n = 0; n != len; ++n)
			for (size_t k = 0; k != bits; ++k)
				if (p[pos(k, n, len)])
					r[n] |= 1 << k;
		f(r);
	})();
}

set<term> tables::decompress() {
	set<term> r;
	for (ntable tab = 0; (size_t)tab != tbls.size(); ++tab)
		decompress(tbls[tab].t, tab, [&r](const term& t){r.insert(t);});
	return r;
}

void tables::out(spbdd_handle x, ntable tab, const rt_printer& f) const {
	decompress(x&&tbls.at(tab).t, tab, [f, this](const term& r) {
		f(ir_handler->to_raw_term(r)); });
}

// ----------------------------------------------------------------------------
// tramsform bin
set<int_t> intersect(const set<int_t>& x, const set<int_t>& y) {
	set<int_t> r;
	set_intersection(x.begin(), x.end(), y.begin(), y.end(),
		inserter(r, r.begin()));
	return r;
}

// ----------------------------------------------------------------------------

/*
// BACKUP CQC
set<term> tables::bodies_equiv(vector<term> x, vector<term> y) const {
//	if (x[0].size() != y[0].size()) return false;
	x[0].tab = y[0].tab;
	x.erase(x.begin()), y.erase(y.begin()),
	create_head(x, x[0].tab), create_head(y, y[0].tab);
	if (cqc(x, y)) {
		if (cqc(y, x)) return true;
	}
}

enum cqc_res { CONTAINED, CONTAINS, BOTH, NONE };

cqc_res maybe_contains(const vector<term>& x, const vector<term>& y) {
	if (x.size() == 1 || y.size() == 1) return NONE;
	set<ntable> tx, ty;
	for (size_t n = 1; n != x.size(); ++n)
		if (x[n].neg) return NONE; else tx.insert(x[n].tab);
	for (size_t n = 1; n != y.size(); ++n)
		if (y[n].neg) return NONE; else ty.insert(y[n].tab);
	bool maybe_contained, maybe_contains;
	if ((maybe_contained = tx.size() < ty.size()))
		for (ntable n : tx)
			if (!has(ty, n)) { maybe_contained = false; break; }
	if ((maybe_contains = tx.size() > ty.size()))
		for (ntable n : ty)
			if (!has(tx, n))
				return maybe_contained ? CONTAINED : NONE;
	return maybe_contained ? BOTH : CONTAINS;
}
*/
/*struct cqcdata {
	vector<term> r;
	size_t from;
	set<int_t> vars;
	set<ntable> tabs;
	cqcdata() {}
	cqcdata(const vector<term>& r) : r(r) {
		from = r.size();
		if (from == 1) return;
		sort(r.begin(), r.end());
		for (size_t n = 1; n < from;)
			if (tabs.insert(find(r[n].tab).second) ++n;
			else r.push_back(r[n]), r.erase(r.begin() + n), --from;
		for (size_t n = from; n != r.size(); ++n) getvars(r[n], vars);
		for (size_t n = 1, k; n != from; ++n)
			for (k = 0; k != r[n].size(); ++k)
				if (r[n][k] < 0) vars.erase(r[n][k]);
		align_vars(r);
	}
};
void tables::cqc_minimize(cqcdata& d) {
	if (d.from != d.r.size()) return;
}
void tables::cqc(flat_prog& p) {
	vector<cqcdata> v;
	for (const vector<term>& r : p)
		v.emplace_back(r), cqc_minimize(v.back());
}*/

/*
ntable tables::prog_add_rule(flat_prog& p, map<ntable, ntable>&,// r,
	vector<term> x) {
	return p.emplace(x), x[0].tab;

//	if (!bcqc || x.size() == 1) return p.emplace(x), x[0].tab;
//	for (const vector<term>& y : p)
//		if (x == y || y.size() == 1) continue;
//		else if (bodies_equiv(x, y)) {
//			if (has(tmprels, x[0].tab) && has(tmprels, y[0].tab)) {
//
//			}
//			return y[0].tab;
//		}
//	if (has(tmprels, x[0][0])) {
//		for (const vector<term>& y : p)
//			if (has(tmprels, y[0].tab) && cqc(x, y) && cqc(y, x))
//				return (tbls[x[0].tab].priority >
//					tbls[y[0].tab].priority ? x : y)[0].tab;
//		return x[0].tab;
//	}
//	if (x.size() > 3) cqc_minimize(x);
//	if (!cqc(x, p)) p.emplace(x);
//	return x[0].tab;
//
}
*/

//set<body*, ptrcmp<body>> body::s;
//set<alt*, ptrcmp<alt>> alt::s;

/*flat_prog tables::cqc(vector<term> x, vector<term> y) const {
	if (x == y) return {x};
	cqc_res r = maybe_contains(x, y), r1;
	if (r == NONE) return { x, y };
	const vector<term> xx = x, yy = y;
	flat_prog p;
	if (x[0].tab == y[0].tab) {
		if (r == BOTH) get_canonical_db({x, y}, p = { x, y });
		else if (r == CONTAINED) get_canonical_db({x}, p = { y });
		else get_canonical_db({y}, p = { x });
	}
	term f[2];
	f[0] = x[0], f[1] = y[0], x.erase(x.begin()), y.erase(y.begin());
	set<int_t> vx, vy;
	getvars(x, vx), getvars(y, vy);
	bool b;
	term hx, hy;
	if ((b = vx.size() == vy.size())) // TODO: support otherwise
		create_tmp_head(x), create_head(y, x[0].tab),
		hx = x[0], hy = y[0],
		get_canonical_db({ x, y }, p), p.insert(x), p.insert(y);
	run_internal_prog(p, r);
	if (has(r, f[0])) return has(r, f[1]) ? { x } : { y };
	if (has(r, f[1])) return { x };
	if (!b) return { x, y };
	if (has(r, x[0])) {
		if (has(r, y[0]))
			return	x[0] = hx, y[0] = hy,
				{ x, { xx[0], x[0] }, y, { yy[0], y[0] } };
		if (has(tmprels, x) && has(tmprels, y)) return { y };
	} else if (has(r, y[0]) && has(tmprels, x) && has(tmprels, y))
		return { x };
	return { x, y };
//	if (has(r, y[0]))
//		return print(print(o::out(),x)<<" is a generalization of ",yy),
//		       true;
//	return false;
}*/

/*bool tables::cqc(const vector<term>& v, const flat_prog& m) const {
	for (const vector<term>& x : m) if (cqc(x, v)) return true;
	return false;
}

void tables::cqc_minimize(vector<term>& v) const {
	if (v.size() < 2) return;
	const vector<term> v1 = v;
	term t;
	for (size_t n = 1; n != v.size(); ++n) {
		t = move(v[n]), v.erase(v.begin() + n);
		if (!cqc(v1, v)) v.insert(v.begin() + n, t);
	}
	DBG(if (v.size() != v1.size())
		print(print(o::err()<<"Rule\t\t", v)<<endl<<"minimized into\t"
		, v1)<<endl;)
}*/
