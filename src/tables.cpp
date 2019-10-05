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
#include "tables.h"
#include "dict.h"
#include "input.h"
#include "output.h"
#include "err.h"
using namespace std;

#define mkchr(x) ((((int_t)x)<<2)|1)
#define mknum(x) ((((int_t)x)<<2)|2)

size_t sig_len(const sig& s) {
	size_t r = 0;
	for (int_t x : get<ints>(s)) if (x > 0) r += x;
	return r;
}

void unquote(wstring& str) {
	for (size_t i = 0; i != str.size(); ++i)
		if (str[i] == L'\\') str.erase(str.begin() + i);
}

wstring _unquote(wstring str) { unquote(str); return str; }

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

spbdd_handle tables::leq_const(int_t c, size_t arg, size_t args, size_t bit)
	const {
	if (!--bit)
		return	(c & 1) ? bdd_handle::T :
			::from_bit(pos(0, arg, args), false);
	return (c & (1 << bit)) ?
		bdd_ite_var(pos(bit, arg, args), leq_const(c, arg, args, bit),
			bdd_handle::T) :
		bdd_ite_var(pos(bit, arg, args), bdd_handle::F,
			leq_const(c, arg, args, bit));
}

typedef tuple<size_t, size_t, size_t, int_t> skmemo;
typedef tuple<size_t, size_t, size_t, int_t> ekmemo;
map<skmemo, spbdd_handle> smemo;
map<ekmemo, spbdd_handle> ememo;
map<ekmemo, spbdd_handle> leqmemo;

spbdd_handle tables::leq_var(size_t arg1, size_t arg2, size_t args) const {
	static ekmemo x;
	static map<ekmemo, spbdd_handle>::const_iterator it;
	if ((it = leqmemo.find(x = { arg1, arg2, args, bits })) != leqmemo.end())
		return it->second;
	spbdd_handle r = leq_var(arg1, arg2, args, bits);
	return leqmemo.emplace(x, r), r;
}
spbdd_handle tables::leq_var(size_t arg1, size_t arg2, size_t args, size_t bit)
	const {
	if (!--bit)
		return	bdd_ite(::from_bit(pos(0, arg2, args), true),
				bdd_handle::T,
				::from_bit(pos(0, arg1, args), false));
	return	bdd_ite(::from_bit(pos(bit, arg2, args), true),
			bdd_ite_var(pos(bit, arg1, args),
				leq_var(arg1, arg2, args, bit), bdd_handle::T),
			bdd_ite_var(pos(bit, arg1, args), bdd_handle::F,
				leq_var(arg1, arg2, args, bit)));
}

void tables::range(size_t arg, size_t args, bdd_handles& v) {
	spbdd_handle	ischar= ::from_bit(pos(0, arg, args), true) &&
			::from_bit(pos(1, arg, args), false);
	spbdd_handle	isnum = ::from_bit(pos(0, arg, args), false) &&
			::from_bit(pos(1, arg, args), true);
	spbdd_handle	issym = ::from_bit(pos(0, arg, args), false) &&
			::from_bit(pos(1, arg, args), false);
	// nums is set to max NUM, not universe size. While for syms it's the size.
	// It worked before because for arity==1 fact(nums) is always negated.
	bdd_handles r = {ischar || isnum || issym,
		(!chars	? bdd_handle::T%ischar : bdd_impl(ischar,
			leq_const(mkchr(chars-1), arg, args, bits))),
		(!nums 	? bdd_handle::T%isnum : bdd_impl(isnum,
			leq_const(mknum(nums), arg, args, bits))),
		(!syms 	? bdd_handle::T%issym : bdd_impl(issym,
			leq_const(((syms-1)<<2), arg, args, bits)))};
	v.insert(v.end(), r.begin(), r.end());
}

spbdd_handle tables::range(size_t arg, ntable tab) {
	array<int_t, 6> k = { syms, nums, chars, (int_t)tbls[tab].len,
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
	spbdd_handle x = bdd_handle::F;
	bdd_handles v;
	for (auto& x : tbls)
//	for (size_t n = 0; n != ts.size(); ++n)
//		x.second.t = add_bit(x.second.t, x.second.len);
		x.t = add_bit(x.t, x.len);
	++bits;
}

//typedef tuple<size_t, size_t, size_t, int_t> skmemo;
//typedef tuple<size_t, size_t, size_t, int_t> ekmemo;
//map<skmemo, spbdd_handle> smemo;
//map<ekmemo, spbdd_handle> ememo;
//map<ekmemo, spbdd_handle> leqmemo;

spbdd_handle tables::from_sym(size_t pos, size_t args, int_t i) const {
	static skmemo x;
	static map<skmemo, spbdd_handle>::const_iterator it;
	if ((it = smemo.find(x = { i, pos, args, bits })) != smemo.end())
		return it->second;
	spbdd_handle r = bdd_handle::T;
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
	spbdd_handle r = bdd_handle::T;
	for (size_t b = 0; b != bits; ++b)
		r = r && ::from_eq(pos(b, p1, args), pos(b, p2, args));
	return ememo.emplace(x, r), r;
}

spbdd_handle tables::from_fact(const term& t) {
	// TODO: memoize
	spbdd_handle r = bdd_handle::T;
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

sig tables::get_sig(const raw_term&t) {return{dict.get_rel(t.e[0].e),t.arity};}
sig tables::get_sig(const lexeme& rel, const ints& arity) {
	return { dict.get_rel(rel), arity };
}

term tables::from_raw_term(const raw_term& r) {
	ints t;
	lexeme l;
	// skip the first symbol unless it's EQ/NEQ (which has VAR as it's first)
	for (size_t n = (r.iseq || r.isleq) ? 0 : 1; n < r.e.size(); ++n)
		switch (r.e[n].type) {
			case elem::NUM: t.push_back(mknum(r.e[n].num)); break;
			case elem::CHR: t.push_back(mkchr(r.e[n].ch)); break;
			case elem::VAR:
				t.push_back(dict.get_var(r.e[n].e)); break;
			case elem::STR:
				l = r.e[n].e;
				++l[0], --l[1];
				t.push_back(dict.get_sym(dict.get_lexeme(
					_unquote(lexeme2str(l)))));
				break;
			case elem::SYM: t.push_back(dict.get_sym(r.e[n].e));
			default: ;
		}
	// ints t is elems (VAR, consts) mapped to unique ints/ids for perms. 
	ntable tbl = (r.iseq || r.isleq) ? -1 : get_table(get_sig(r));
	return term(r.neg, r.iseq, r.isleq, tbl, t);
}

void tables::out(wostream& os) const {
	strs_t::const_iterator it;
	for (ntable tab = 0; (size_t)tab != tbls.size(); ++tab)
//		if ((it = strs.find(dict.get_rel(tab))) == strs.end())
			out(os, tbls[tab].t, tab);
//		else os << it->first << L" = \"" << it->second << L'"' << endl;
}

void tables::out(const rt_printer& f) const {
	for (ntable tab = 0; (size_t)tab != tbls.size(); ++tab)
		out(tbls[tab].t, tab, f);
}

void tables::out(wostream& os, spbdd_handle x, ntable tab) const {
	out(x, tab, [&os](const raw_term& rt) { os << rt << L'.' << endl; });
}

#ifdef __EMSCRIPTEN__
// o is `tabular_collector` - JS object with methods:
// - length(relation_name) - returns number of rows (or index of next new row)
// - set(relation_name, row, col, value) - sets value of the cell of a table
void tables::out(emscripten::val o) const {
	out([&o](const raw_term& t) {
		wstring relation = lexeme2str(t.e[0].e);
		int row = o.call<int>("length", ws2s(relation));
		int col = 0;
		for (size_t ar = 0, n = 1; ar != t.arity.size();) {
			wstringstream es;
			while (t.arity[ar] == -1) ++ar, es << L'(';
			if (n >= t.e.size()) break;
			while (t.e[n].type == elem::OPENP) ++n;
			for (int_t k = 0; k != t.arity[ar];)
				if ((es<<t.e[n++]),++k!=t.arity[ar]) {
					o.call<void>("set", relation, row,col++,
						ws2s(es.str()));
					es.str(L"");
				}
			while (n<t.e.size() && t.e[n].type == elem::CLOSEP) ++n;
			++ar;
			while (ar < t.arity.size()
				&& t.arity[ar] == -2) ++ar, es<<L')';
			if (es.str() != L"")
				o.call<void>("set", relation, row, col++,
					ws2s(es.str()));
		}
	});
}
#endif

void tables::decompress(spbdd_handle x, ntable tab, const cb_decompress& f,
	size_t len) const {
	if (!len) len = tbls.at(tab).len;
	allsat_cb(x/*&&ts[tab].t*/, len * bits,
		[tab, &f, len, this](const bools& p, int_t DBG(y)) {
		DBG(assert(abs(y) == 1);)
		term r(false, false, false, tab, ints(len, 0));
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

#define get_var_lexeme(v) dict.get_lexeme(wstring(L"?v") + to_wstring(-v))

elem tables::get_elem(int_t arg) const {
	if (arg < 0) return elem(elem::VAR, get_var_lexeme(arg));
	if (arg & 1) {
		const wchar_t ch = arg >> 2;
		if (iswprint(ch)) return elem(ch);
		return	elem(elem::SYM, dict.get_lexeme(wstring(L"\"#") +
			to_wstring((unsigned char)(ch)) + L"\""));
	}
	if (arg & 2) return elem((int_t)(arg>>2));
	return elem(elem::SYM, dict.get_sym(arg));
}

raw_term tables::to_raw_term(const term& r) const {
	raw_term rt;
	rt.neg = r.neg;
	size_t args;
	if (r.iseq)
		args = 2, rt.e.resize(args + 1), rt.e[0] = get_elem(r[0]),
		rt.e[1] = elem(elem::SYM,dict.get_lexeme(r.neg ? L"!=" : L"=")),
		rt.e[2] = get_elem(r[1]), rt.arity = {2};
	else if (r.isleq)
		args = 2, rt.e.resize(args + 1), rt.e[0] = get_elem(r[0]),
		rt.e[1] = elem(elem::SYM,dict.get_lexeme(r.neg ? L"<=" : L">")),
		rt.e[2] = get_elem(r[1]), rt.arity = {2};
	else {
		args = tbls.at(r.tab).len, rt.e.resize(args + 1);
		rt.e[0] = elem(elem::SYM,
			dict.get_rel(get<0>(tbls.at(r.tab).s)));
		rt.arity = get<ints>(tbls.at(r.tab).s);
		for (size_t n = 1; n != args + 1; ++n)
			rt.e[n] = get_elem(r[n - 1]);
		rt.insert_parens(dict.op, dict.cl);
	}
	DBG(assert(args == r.size());)
	return rt;
}

void tables::out(spbdd_handle x, ntable tab, const rt_printer& f) const {
	decompress(x&&tbls.at(tab).t, tab, [f, this](const term& r) {
		f(to_raw_term(r)); });
}

void term::replace(const map<int_t, int_t>& m) {
	auto it = m.end();
	for (int_t& i : *this) if (m.end() != (it = m.find(i))) i = it->second;
}

void tables::align_vars(vector<term>& v) const {
	set<int_t> vs;
	for (const term& t : v) for (int_t i : t) if (i < 0) vs.insert(i);
	if (vs.empty()) return;
	vs.clear();
	map<int_t, int_t> m;
	for (size_t k = 0; k != v.size(); ++k)
		for (size_t n = 0; n != v[k].size(); ++n)
			if (v[k][n] < 0 && !has(m, v[k][n]))
				m.emplace(v[k][n], -m.size() - 1);
	for (term& t : v) t.replace(m);
}

uints tables::get_perm(const term& t, const varmap& m, size_t len) const {
	uints perm = perm_init(t.size() * bits);
	for (size_t n = 0, b; n != t.size(); ++n)
		if (t[n] < 0)
			for (b = 0; b != bits; ++b)
				perm[pos(b,n,t.size())] = pos(b,m.at(t[n]),len);
	return perm;
}

template<typename T>
varmap tables::get_varmap(const term& h, const T& b, size_t &varslen) {
	varmap m;
	varslen = h.size();
	for (size_t n = 0; n != h.size(); ++n)
		if (h[n] < 0 && !has(m, h[n])) m.emplace(h[n], n);
	for (const term& t : b)
		for (size_t n = 0; n != t.size(); ++n)
			if (t[n] < 0 && !has(m, t[n]))
				m.emplace(t[n], varslen++);
	return m;
}

spbdd_handle tables::get_alt_range(const term& h, const set<term>& a,
	const varmap& vm, size_t len) {
	set<int_t> pvars, nvars, eqvars, leqvars;
	std::vector<const term*> eqterms, leqterms;
	// first pass, just enlist eq terms (that have at least one var)
	for (const term& t : a) {
		bool haseq = false, hasleq = false;
		for (size_t n = 0; n != t.size(); ++n)
			if (t[n] >= 0) continue;
			else if (t.iseq) haseq = true;
			else if (t.isleq) hasleq = true;
			else (t.neg ? nvars : pvars).insert(t[n]);
		// only if iseq and has at least one var
		if (haseq) eqterms.push_back(&t);
		else if (hasleq) leqterms.push_back(&t);
	}
	for (const term* pt : eqterms) {
		const term& t = *pt;
		bool noeqvars = true;
		std::vector<int_t> tvars;
		for (size_t n = 0; n != t.size(); ++n)
			if (t[n] >= 0) continue;
			// nvars add range already, so skip all in that case...
			// and per 1.3 - if any one is contrained (outside) bail out
			else if (has(nvars, t[n])) { noeqvars = false; break; }
			// if neither pvars has this var it should be ranged
			else if (!has(pvars, t[n])) tvars.push_back(t[n]);
			else if (!t.neg) { noeqvars = false; break; }
			// if is in pvars and == then other var is covered too, skip.
			// this isn't covered by 1.1-3 (?) but further optimization.
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
		// - if 1st/greater is const, still can't skip, needs to be ranged.
		// - if neither var appears elsewhere (nvars nor pvars) => do both.
		//   (that is a bit strange, i.e. if appears outside one is enough)
		// ?x > ?y => ~(?x <= ?y) => ?y - 2nd var is limit for both LEQ and GT.
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
		nvars.erase(i), eqvars.erase(i), leqvars.erase(i);
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

map<size_t, int_t> varmap_inv(const varmap& vm) {
	map<size_t, int_t> inv;
	for (auto x : vm) {
		assert(!has(inv, x.second));
		inv.emplace(x.second, x.first);
	}
	return inv;
}

body tables::get_body(const term& t, const varmap& vm, size_t len) const {
	body b;
	b.neg = t.neg, b.tab = t.tab, b.perm = get_perm(t, vm, len),
	b.q = bdd_handle::T, b.ex = bools(t.size() * bits, false);
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

void tables::get_facts(const flat_prog& m) {
	map<ntable, set<spbdd_handle>> f;
	for (const auto& r : m)
		if (r.size() != 1) continue;
		else if (r[0].goal) goals.insert(r[0]);
		else f[r[0].tab].insert(from_fact(r[0]));
	clock_t start, end;
	if (optimize) measure_time_start();
	bdd_handles v;
	for (auto x : f) {
		spbdd_handle r = bdd_handle::F;
		for (auto y : x.second) r = r || y;
		tbls[x.first].t = r;
	}
	if (optimize) measure_time_end();
}

void tables::get_nums(const raw_term& t) {
	for (const elem& e : t.e)
		if (e.type == elem::NUM) nums = max(nums, e.num);
		else if (e.type == elem::CHR) chars = 255;
}

flat_prog tables::to_terms(const raw_prog& p) {
	flat_prog m;
	vector<term> v;
	term t;
	for (const raw_rule& r : p.r)
		if (r.type == raw_rule::NONE && !r.b.empty())
			for (const raw_term& x : r.h) {
				get_nums(x), t = from_raw_term(x),
				v.push_back(t);
				for (const vector<raw_term>& y : r.b) {
					for (const raw_term& z : y)
						v.push_back(from_raw_term(z)),
						get_nums(z);
					align_vars(v), m.insert(move(v));
				}
			}
		else for (const raw_term& x : r.h)
			t = from_raw_term(x), t.goal = r.type == raw_rule::GOAL,
			m.insert({t}), get_nums(x);
	return m;
}

void freeze(vector<term>& v) {
	int_t m = 0;
	map<int_t, int_t> p;
	map<int_t, int_t>::const_iterator it;
	for (const term& t : v) for (int_t i : t) if (i & 2) m = max(m, i >> 2);
	for (term& t : v)
		for (int_t& i : t)
			if (i >= 0) continue;
			else if ((it = p.find(i)) != p.end()) i = it->second;
			else p.emplace(i, mknum(m)), i = mknum(m++);
}

bool tables::cqc(const vector<term>& x, vector<term> y) const {
	const vector<term> yy = y;
	set<ntable> tx, ty;
	for (const term& t : x)
		if(t.neg) return false;
		//throw "cqc not supported yet for terms with negation";
		else tx.insert(t.tab);
	for (const term& t : y)
		if(t.neg) return false;
		//throw "cqc not supported yet for terms with negation";
		else ty.insert(t.tab);
	if (tx.size() < ty.size()) return false;
	for (ntable n : tx) if (!has(ty, n)) return false;
	set<term> r;
	flat_prog m;
	m.insert(x), freeze(y);
	for (size_t n = 1; n != y.size(); ++n) m.insert({y[n]});
	tables t(false, false, true);
	t.dict = dict, t.bcqc = false, t.chars = chars, t.nums = nums,
	t.run_nums(move(m), r, 1);
	//DBG(print(wcout, r) << endl;)
	if (has(r, y[0]))
		return //print(print(wcout, x) << L" is a generalization of ",yy),
		       true;
	return false;
}

bool tables::cqc(const vector<term>& v, const flat_prog& m) const {
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
		print(print(wcerr<<L"Rule\t\t", v)<<endl<<L"minimized into\t"
		, v1)<<endl;)
}

ntable tables::prog_add_rule(flat_prog& p, vector<term> x) {
	if (!bcqc || x.size() == 1) return p.emplace(x), x[0].tab;
#define getbody(x) vector<term>((x).begin() + 1, (x).end())
	for (const vector<term>& y : p)
		if (y.size() > 1 && bodies_equiv(x, y))
//		if (y.size() > 1 && bodies_equiv(getbody(x), getbody(y)))
			if (x[0] == y[0]) return x[0].tab;
	if (bcqc && has(tmprels, x[0][0])) {
		for (const vector<term>& y : p)
			if (has(tmprels, y[0].tab) && cqc(x, y) && cqc(y, x))
				return (tbls[x[0].tab].priority >
					tbls[y[0].tab].priority ? x : y)[0].tab;
		return x[0].tab;
	}
	if (x.size() > 3) cqc_minimize(x);
	if (!cqc(x, p)) p.emplace(x);
	return x[0].tab;
}
#undef getbody

wostream& tables::print(wostream& os, const vector<term>& v) const {
	os << to_raw_term(v[0]);
	if (v.size() == 1) return os << L'.';
	os << L" :- ";
	for (size_t n = 1; n != v.size(); ++n) {
		if (v[n].goal) os << L'!';
		os << to_raw_term(v[n]) << (n == v.size() - 1 ? L"." : L", ");
	}
	return os;
}

wostream& tables::print(wostream& os, const flat_prog& p) const {
	for (const auto& x : p)
		print(os << (x[0].tab == -1 ? 0 : tbls[x[0].tab].priority) <<
			L'\t', x) << endl;
/*	map<size_t, flat_prog> m;
	for (const auto& x : p) m[tbls[x[0].tab].priority].insert(x);
	size_t n = m.rbegin()->first;
	vector<flat_prog> v(n);
	for (const auto& x : m) v[n--] = move(x.second);
	for (n = 0; n != v.size(); ++n)
		for (const vector<term>& y : v[n])
			print(os << n << L'\t', y) << endl;*/
	return os;
}

bool tables::get_alt(const set<term>& al, const term& h, alt& a) {
	set<int_t> vs;
	set<pair<body, term>> b;
	spbdd_handle leq = bdd_handle::T, q;
	a.vm = get_varmap(h, al, a.varslen),
	a.inv = varmap_inv(a.vm);
	for (const term& t : al) {
		if (t.size() != 2 || (!t.iseq && !t.isleq))
			b.insert({get_body(t, a.vm, a.varslen), t});
		else if (t.iseq) {
			if (t[0] == t[1]) {
				if (t.neg) return false;
				continue;
			}
			if (t[0] >= 0 && t[1] >= 0) {
				if (t.neg == (t[0] == t[1])) return false;
				continue;
			}
			if (t[0] < 0 && t[1] < 0)
				q = from_sym_eq(a.vm.at(t[0]), a.vm.at(t[1]),
					a.varslen);
			else if (t[0] < 0)
				q = from_sym(a.vm.at(t[0]), a.varslen, t[1]);
			else if (t[1] < 0)
				q = from_sym(a.vm.at(t[1]), a.varslen, t[0]);
			a.eq = t.neg ? a.eq % q : (a.eq && q);
		} else if (t.isleq) {
			if (t[0] == t[1]) {
				if (t.neg) return false;
				continue;
			}
			if (t[0] >= 0 && t[1] >= 0) {
				if (t.neg == (t[0] <= t[1])) return false;
				continue;
			}
			if (t[0] < 0 && t[1] < 0)
				q = leq_var(a.vm.at(t[0]), a.vm.at(t[1]),
					a.varslen, bits);
			else if (t[0] < 0)
				q = leq_const(t[1], a.vm.at(t[0]),
					a.varslen, bits);
			else if (t[1] < 0)
				// 1 <= v1, v1 >= 1, ~(v1 <= 1) || v1==1.
				q = bdd_handle::T % leq_const(t[0],
					a.vm.at(t[1]), a.varslen, bits) ||
					from_sym(a.vm.at(t[1]), a.varslen,t[0]);
			leq = t.neg ? leq % q : (leq && q);
		}
	}
	a.rng = get_alt_range(h, al, a.vm, a.varslen);
	a.rng = bdd_and_many({ a.rng, leq });
	static set<body*, ptrcmp<body>>::const_iterator bit;
	body* y;
	for (auto x : b) {
		a.t.push_back(x.second);
		if ((bit=bodies.find(&x.first)) != bodies.end())
			a.push_back(*bit);
		else *(y=new body) = x.first, a.push_back(y), bodies.insert(y);
	}
	auto d = deltail(a.varslen, h.size());
	a.ex = d.first, a.perm = d.second;
	return true;
}

lexeme tables::get_new_rel() {
	static size_t last = 1;
	wstring s = L"r";
	size_t sz;
	lexeme l;
retry:	sz = dict.nrels(), l = dict.get_lexeme(s + to_wstring(last));
	dict.get_rel(l);
	if (dict.nrels() == sz) { ++last; goto retry; }
	return l;
}

template<typename T>
void dag_get_reachable(const map<T, set<T>>& g, const T& t, set<T>& r) {
	if (has(r, t)) return;
	auto it = g.find(t);
	if (it != g.end())
		for (const T& x : it->second)
			dag_get_reachable(g, x, r);
	r.insert(t);
}

template<typename T>
set<T> dag_get_reachable(const map<T, set<T>>& g, const T& t) {
	set<T> r;
	return dag_get_reachable<T>(g, t, r), r;
}

void tables::table_increase_priority(ntable t, size_t inc) {
	for (ntable x : dag_get_reachable(deps, t)) tbls[x].priority += inc;
}

void tables::set_priorities(const flat_prog& p) {
	for (table& t : tbls) t.priority = 0;
	for (const vector<term>& x : p) {
		set<ntable>& s = deps[x[0].tab];
		for (size_t n = 1; n != x.size(); ++n)
			if (has(tmprels, x[n].tab))
				s.insert(x[n].tab);
	}
	for (const auto& x : deps)
		for (ntable y : x.second)
			if (has(tmprels, y))
				table_increase_priority(y);
}

void getvars(const term& t, set<int_t>& v) {
	for (int_t i : t) if (i < 0) v.insert(i);
}

void getvars(const vector<term>& t, set<int_t>& v) {
	for (const term& x : t) getvars(x, v);
}

bool tables::bodies_equiv(vector<term> x, vector<term> y) const {
	if (x[0].size() != y[0].size()) return false;
	x[0].tab = y[0].tab;
	set<int_t> vx, vy;
	getvars(x, vx), getvars(y, vy);
	term h;
//	int_t r = get_new_tab(dict.get_rel(get_new_rel()),{(int_t)v.size()}));
//	h.insert(h.begin(), vx.begin(), vx.end()), h.tab = x[0].tab,
//	x.insert(x.begin(), move(h)), h.insert(h.begin(),
//	vy.begin(), vy.end()), h.tab = x[0].tab, y.insert(y.begin(), move(h));
	return cqc(x, y) && cqc(y, x);
}

vector<term> tables::interpolate(vector<term> x, set<int_t> v) {
	term t;
	for (size_t k = 0; k != x.size(); ++k)
		for (size_t n = 0; n != x[k].size(); ++n)
			if (has(v, x[k][n]))
				t.push_back(x[k][n]), v.erase(x[k][n]);
	tmprels.insert(t.tab = get_new_tab(dict.get_rel(get_new_rel()),
		{(int_t)t.size()}));
	return x.insert(x.begin(), t), x;
}

set<int_t> intersect(const set<int_t>& x, const set<int_t>& y) {
	set<int_t> r;
	set_intersection(x.begin(), x.end(), y.begin(), y.end(),
		inserter(r, r.begin()));
	return r;
}

void tables::transform_bin(flat_prog& p) {
	const flat_prog q = move(p);
	vector<set<int_t>> vars;
	auto getterms = [this, &vars]
		(const vector<term>& x) -> vector<size_t> {
		if (x.size() <= 3) return {};
/*		vector<size_t> e;
		for (size_t n = 1; n != x.size(); ++n)
			if (has(exts, x[n].tab)) e.push_back(n);
		if (e.size() == x.size() - 1) return { 1, 2 };
		if (e.size() > 1) return { e[0], e[1] };*/
		size_t max = 0, b1 = 0, b2, n;
		for (size_t i = 2; i != x.size(); ++i)
			for (size_t j = 1; j != i; ++j)
				if (max < (n=intersect(vars[i],vars[j]).size()))
					max = n, b1 = j, b2 = i;
		if (!b1) b1 = 1, b2 = 2;
		return { b1, b2 };
	};
	vector<term> r;
	vector<size_t> m;
	set<int_t> v;
	for (vector<term> x : q) {
		if (x[0].goal) { goals.insert(x[0]); continue; }
			//prog_add_rule(p, x); continue; }
		for (const term& t : x) getvars(t, v), vars.push_back(move(v));
		while (!(m = getterms(x)).empty()) {
			for (size_t i : m) r.push_back(x[i]);
			for (size_t n = m.size(); n--;)
				x.erase(x.begin() + m[n]),
				vars.erase(vars.begin() + m[n]);
			for (const auto& s : vars) v.insert(s.begin(), s.end());
			r = interpolate(r, move(v)),
			x.push_back(r[0]), getvars(r[0], v),
			vars.push_back(move(v)), p.insert(move(r));
		}
		p.insert(move(x)), vars.clear();
	}
	if (print_transformed) print(wcout<<L"after transform_bin:"<<endl, p);
}

void tables::get_rules(flat_prog p) {
	bcqc = false;
	get_facts(p);
	for (const vector<term>& x : p)
		for (size_t n = 1; n != x.size(); ++n)
			exts.insert(x[n].tab);
	for (const vector<term>& x : p) if (x.size() > 1) exts.erase(x[0].tab);
	set<rule> rs;
	varmap::const_iterator it;
	set<alt*, ptrcmp<alt>>::const_iterator ait;
	alt* aa;
	if (bcqc) print(wcout<<L"before cqc, "<<p.size()<< L" rules:"<<endl, p);
	flat_prog q(move(p));
	for (const auto& x : q) prog_add_rule(p, x);
	if (bcqc) print(wcout<<L"after cqc before tbin, "<<p.size()<< L" rules."<<endl, p);
#ifndef TRANSFORM_BIN_DRIVER
	if (bin_transform) transform_bin(p);
#endif
	if (bcqc) print(wcout<<L"before cqc after tbin, "<<p.size()<< L" rules."<<endl, p);
	q = move(p);
	for (const auto& x : q) prog_add_rule(p, x);
	set_priorities(p);
	if (bcqc) print(wcout<<L"after cqc, "<<p.size()<< L" rules."<<endl, p);
	if (optimize) bdd::gc();
	map<term, set<set<term>>> m;
	for (const auto& x : p)
		if (x.size() == 1) m[x[0]] = {};
		else m[x[0]].insert(set<term>(x.begin() + 1, x.end()));
	for (pair<term, set<set<term>>> x : m) {
		if (x.second.empty()) continue;
		varmap v;
		set<int_t> hvars;
		const term &t = x.first;
		rule r;
		if (t.neg) datalog = false;
		tbls[t.tab].ext = false;
		r.neg = t.neg, r.tab = t.tab, r.eq = bdd_handle::T, r.t = t;
		for (size_t n = 0; n != t.size(); ++n)
			if (t[n] >= 0) get_sym(t[n], n, t.size(), r.eq);
			else if (v.end() == (it = v.find(t[n])))
				v.emplace(t[n], n);
			else r.eq = r.eq&&from_sym_eq(n, it->second, t.size());
		set<alt> as;
		r.len = t.size();
		for (const set<term>& al : x.second) {
			alt a;
			if (get_alt(al, t, a)) as.insert(move(a));
		}
		for (alt x : as)
			if ((ait = alts.find(&x)) != alts.end())
				r.push_back(*ait);
			else	*(aa = new alt) = x,
				r.push_back(aa), alts.insert(aa);
		rs.insert(r);
	}
	for (rule r : rs)
		tbls[r.t.tab].r.push_back(rules.size()), rules.push_back(r);
	sort(rules.begin(), rules.end(), [this](const rule& x, const rule& y) {
			return tbls[x.tab].priority > tbls[y.tab].priority; });
}

void tables::load_string(lexeme r, const wstring& s) {
	int_t rel = dict.get_rel(r);
	str_rels.insert(rel);
	const ints ar = {0,-1,-1,1,-2,-2,-1,1,-2,-1,-1,1,-2,-2};
	const int_t sspace = dict.get_sym(dict.get_lexeme(L"space")),
		salpha = dict.get_sym(dict.get_lexeme(L"alpha")),
		salnum = dict.get_sym(dict.get_lexeme(L"alnum")),
		sdigit = dict.get_sym(dict.get_lexeme(L"digit")),
		sprint = dict.get_sym(dict.get_lexeme(L"printable"));
	term t;
	bdd_handles b1, b2;
	b1.reserve(s.size()), b2.reserve(s.size()), t.resize(3);
	for (int_t n = 0; n != (int_t)s.size(); ++n) {
		t[0] = mknum(n), t[1] = mkchr(s[n]), t[2] = mknum(n + 1),
		b1.push_back(from_fact(t)), t[1] = t[0];
		if (iswspace(s[n])) t[0] = sspace, b2.push_back(from_fact(t));
		if (iswdigit(s[n])) t[0] = sdigit, b2.push_back(from_fact(t));
		if (iswalpha(s[n])) t[0] = salpha, b2.push_back(from_fact(t));
		if (iswalnum(s[n])) t[0] = salnum, b2.push_back(from_fact(t));
		if (iswprint(s[n])) t[0] = sprint, b2.push_back(from_fact(t));
	}
	clock_t start, end;
	if (optimize)
		(output::to(L"debug")<<"load_string or_many: "),
		measure_time_start();
	tbls[get_table({rel, ar})].t = bdd_or_many(move(b1)),
	tbls[get_table({rel, {3}})].t = bdd_or_many(move(b2));
	if (optimize) measure_time_end();
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
	size_t len = sig_len(s);
	max_args = max(max_args, len);
	table tb;
	return	tb.t = bdd_handle::F, tb.s = s, tb.len = len,
		tbls.push_back(tb), smap.emplace(s,nt), nt;
}

term to_nums(term t) {
	for (int_t& i : t)  if (i > 0) i = mknum(i);
	return t;
}

//term from_nums(term t) {
//	for (int_t& i : t)  if (i > 0) i >>= 2;
//	return t;
//}

vector<term> to_nums(const vector<term>& v) {
	vector<term> r;
	for (const term& t : v) r.push_back(to_nums(t));
	return r;
}

//set<term> from_nums(const set<term>& s) {
//	set<term> ss;
//	for (const term& t : s) ss.insert(from_nums(t));
//	return ss;
//}

void to_nums(flat_prog& m) {
	flat_prog mm;
	for (auto x : m) mm.insert(to_nums(x));
	m = move(mm);
}

ntable tables::get_new_tab(int_t x, ints ar) { return get_table({ x, ar }); }

void tables::transform_grammar(vector<production> g, flat_prog& p) {
	if (g.empty()) return;
//	wcout<<"grammar before:"<<endl;
//	for (production& p : g) wcout << p << endl;
	for (size_t k = 0; k != g.size();) {
		if (g[k].p.size() < 2) parse_error(err_empty_prod, g[k].p[0].e);
		size_t n = 0;
		while (n < g[k].p.size() && g[k].p[n].type != elem::ALT) ++n;
		if (n == g[k].p.size()) { ++k; continue; }
		g.push_back({vector<elem>(g[k].p.begin(), g[k].p.begin()+n)});
		g.push_back({vector<elem>(g[k].p.begin()+n+1, g[k].p.end())});
		g.back().p.insert(g.back().p.begin(), g[k].p[0]);
		g.erase(g.begin() + k);
	}
//	wcout<<"grammar after:"<<endl;
//	for (production& p : g) wcout << p << endl;
	for (production& p : g)
		for (size_t n = 0; n < p.p.size(); ++n)
			if (p.p[n].type == elem::STR) {
				lexeme l = p.p[n].e;
				p.p.erase(p.p.begin() + n);
				bool esc = false;
				for (cws s = l[0]+1; s != l[1]-1; ++s)
					if (*s == L'\\' && !esc) esc = true;
					else p.p.insert(p.p.begin() + n++,
						elem(*s)), esc = false;
			}
	vector<term> v;
	static const set<wstring> b =
		{ L"alpha", L"alnum", L"digit", L"space", L"printable" };
	set<lexeme, lexcmp> builtins;
	for (const wstring& s : b) builtins.insert(dict.get_lexeme(s));

	for (const production& x : g) {
		if (x.p.size() == 2 && x.p[1].e == L"null") {
			term t;
			t.resize(2), t[0] = t[1] = -1;
			t.tab = get_table({dict.get_rel(x.p[0].e),{2}}),
			p.insert({move(t)});
			continue;
		}
		for (int_t n = 0; n != (int_t)x.p.size(); ++n) {
			term t;
			if (builtins.find(x.p[n].e) != builtins.end()) {
				t.tab = get_table({*str_rels.begin(), {3}});
				t.resize(3), t[0] = dict.get_sym(x.p[n].e),
				t[1] = -n, t[2] = -n-1;
			} else if (x.p[n].type == elem::SYM) {
				t.resize(2);
				t.tab = get_table({dict.get_rel(x.p[n].e),{2}});
				if (n) t[0] = -n, t[1] = -n-1;
				else t[0] = -1, t[1] = -(int_t)(x.p.size());
			} else if (x.p[n].type == elem::CHR) {
				t.resize(3);
				if (str_rels.size() > 1) er(err_one_input);
				if (str_rels.empty()) continue;
				t.tab = *str_rels.begin();
				t[0] = -n, t[2] = -n-1,
				t[1] = mkchr((unsigned char)(x.p[n].ch));
			} else throw runtime_error(
				"Unexpected grammar element");
			v.push_back(move(t));
		}
		p.insert(move(v));
	}
	print(wcout << L"transformed grammar: " << endl, p);
}

void tables::add_prog(const raw_prog& p, const strs_t& strs_) {
	strs = strs_;
	if (!strs.empty())
		chars = 255,
		dict.get_sym(dict.get_lexeme(L"space")),
		dict.get_sym(dict.get_lexeme(L"alpha")),
		dict.get_sym(dict.get_lexeme(L"alnum")),
		dict.get_sym(dict.get_lexeme(L"digit")),
		dict.get_sym(dict.get_lexeme(L"printable"));
	for (auto x : strs) nums = max(nums, (int_t)x.second.size()+1);
	add_prog(move(to_terms(p)), p.g);
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
//	DBG(print(wcout<<L"run_nums for:"<<endl, p)<<endl<<L"returned:"<<endl;)
	add_prog(move(p), {});
	if (!pfp(nsteps)) return false;
	r = g(decompress());
	return true;
}

void tables::add_prog(flat_prog m, const vector<production>& g, bool mknums) {
	smemo.clear(), ememo.clear(), leqmemo.clear();
	if (mknums) to_nums(m);
	rules.clear(), datalog = true;
	syms = dict.nsyms();
	while (max(max(nums, chars), syms) >= (1 << (bits - 2))) add_bit();
	for (auto x : strs) load_string(x.first, x.second);
	transform_grammar(g, m);
	get_rules(move(m));
//	clock_t start, end;
//	output::to(L"debug")<<"load_string: ";
//	measure_time_start();
//	measure_time_end();
	if (optimize) bdd::gc();
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
//	if (b.a) return alt_query(*b.a, 0);
//	if (b.ext) return b.q;
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
/*	spbdd_handle t = bdd_handle::T;
	for (auto x : a.order) {
		bdd_handles v1;
		v1.push_back(t);
		for (auto y : x.first) v1.push_back(body_query(*a[y]));
		t = bdd_and_many(move(v1)) / x.second;
	}
	v.push_back(a.rlast = deltail(t && a.rng, a.varslen, len));*/
//	DBG(bdd::gc();)
	bdd_handles v1 = { a.rng, a.eq };
	spbdd_handle x;
	//DBG(assert(!a.empty());)
	for (size_t n = 0; n != a.size(); ++n)
		if (bdd_handle::F == (x = body_query(*a[n], a.varslen))) {
			a.insert(a.begin(), a[n]), a.erase(a.begin() + n + 1);
			return bdd_handle::F;
		} else v1.push_back(x);
	sort(v1.begin(), v1.end(), handle_cmp);
	if (v1 == a.last) return a.rlast;// { v.push_back(a.rlast); return; }
	if (!bproof)
		return	a.rlast =
			bdd_and_many_ex_perm(a.last = move(v1), a.ex, a.perm);
	a.levels.emplace(nstep, x = bdd_and_many(v1));
//	if ((x = bdd_and_many_ex(a.last, a.ex)) != bdd_handle::F)
//		v.push_back(a.rlast = x ^ a.perm);
//	bdd_handles v;
	return a.rlast = bdd_permute_ex(x, a.ex, a.perm);
//	if ((x = bdd_and_many_ex_perm(a.last, a.ex, a.perm)) != bdd_handle::F)
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
		if (s == bdd_handle::F) return unsat = true;
		x = (t || a) % d;
	}
//	DBG(assert(bdd_nvars(x) < len*bits);)
	return x != t && (t = x, true);
}

char tables::fwd() noexcept {
	bdd_handles add, del;
//	DBG(out(wcout<<"db before:"<<endl);)
	for (rule& r : rules) {
		bdd_handles v(r.size());
		for (size_t n = 0; n != r.size(); ++n)
			v[n] = alt_query(*r[n], r.len);
		spbdd_handle x;
		if (v == r.last) { if (datalog) continue; x = r.rlast; }
		// applying the r.eq and or-ing all alt-s
		else r.last = v, x = r.rlast = bdd_or_many(move(v)) && r.eq;
//		DBG(assert(bdd_nvars(x) < r.len*bits);)
		if (x == bdd_handle::F) continue;
		(r.neg ? tbls[r.tab].del : tbls[r.tab].add).push_back(x);
	}
	bool b = false;
	for (auto& t : tbls) {
		b |= t.commit(DBG(bits));
		if (t.unsat) return unsat = true;
		//b |= t.second.commit(DBG(bits));
		//if (t.second.unsat) return unsat = true;
	}
	return b;
/*	if (!b) return false;
	for (auto x : goals)
		for (auto y : x.second)
			b &= (y && ts[x.first].t) == y;
	if (b) return (wcout <<"found"<<endl), false;
	return b;*/
}

level tables::get_front() const {
	level r(tbls.size());
	for (ntable n = 0; n != (ntable)tbls.size(); ++n) r[n] = tbls.at(n).t;
	return r;
}

bool tables::pfp(size_t nsteps) {
	set<level> s;
	if (bproof) levels.emplace_back(get_front());
	level l;
	for (;;) {
		if (optimize) output::to(L"info") << "step: " << nstep << endl;
		++nstep;
		if (!fwd()) return bproof ? get_goals(), true : true;
		if (unsat) throw unsat_exception();
		if (nsteps && nstep == nsteps) return true;
		l = get_front();
		if (!datalog && !s.emplace(l).second) return false;
		if (bproof) levels.push_back(move(l));
	}
	throw 0;
}

bool tables::run_prog(const raw_prog& p, const strs_t& strs) {
	clock_t start, end;
	double t;
//	output::to(L"@stderr") << L"add_prog: ";
	if (optimize) measure_time_start();
	add_prog(p, strs);
	if (optimize) {
		end = clock(), t = double(end - start) / CLOCKS_PER_SEC;
		wcerr << L"pfp: ";
		measure_time_start();
	}
//	output::to(L"@stderr")
	bool r = pfp();
	if (optimize)
		(wcerr << L"add_prog: " << t << L" pfp: "),measure_time_end();
	return r;
}

tables::tables(bool bproof, bool optimize, bool bin_transform,
	bool print_transformed) : dict(*new dict_t), bproof(bproof),
	optimize(optimize), bin_transform(bin_transform),
	print_transformed(print_transformed) {}

tables::~tables() {
	if (optimize) delete &dict;
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

//set<body*, ptrcmp<body>> body::s;
//set<alt*, ptrcmp<alt>> alt::s;
