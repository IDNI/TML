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
		bdd_ite_var(pos(bit,arg,args), leq_const(c, arg, args, bit),
			bdd_handle::T) :
		bdd_ite_var(pos(bit,arg,args), bdd_handle::F,
			leq_const(c, arg, args, bit));
}

void tables::range(size_t arg, size_t args, bdd_handles& v) {
	spbdd_handle	ischar= ::from_bit(pos(0, arg, args), true) &&
			::from_bit(pos(1, arg, args), false);
	spbdd_handle	isnum = ::from_bit(pos(0, arg, args), false) &&
			::from_bit(pos(1, arg, args), true);
	spbdd_handle	issym = ::from_bit(pos(0, arg, args), false) &&
			::from_bit(pos(1, arg, args), false);
	bdd_handles r = {ischar || isnum || issym,
		(!chars	? bdd_handle::T%ischar : bdd_impl(ischar,
			leq_const(mkchr(chars-1), arg, args, bits))),
		(!nums 	? bdd_handle::T%isnum : bdd_impl(isnum,
			leq_const(mknum(nums-1), arg, args, bits))),
		(!syms 	? bdd_handle::T%issym : bdd_impl(issym,
			leq_const(((syms-1)<<2), arg, args, bits)))};
	v.insert(v.end(), r.begin(), r.end());
}

spbdd_handle tables::range(size_t arg, ntable tab) {
	array<int_t, 6> k = { syms, nums, chars, (int_t)tab, (int_t)arg,
		(int_t)bits };
	auto it = range_memo.find(k);
	if (it != range_memo.end()) return it->second;
	bdd_handles v;
	return	range(arg, ts[tab].len, v),
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
	for (size_t n = 0; n != ts.size(); ++n)
		ts[n].t = add_bit(ts[n].t, ts[n].len);
	++bits;
}

typedef tuple<size_t, size_t, size_t, int_t> skmemo;
static map<skmemo, spbdd_handle> smemo;
typedef tuple<size_t, size_t, size_t, int_t> ekmemo;
static map<ekmemo, spbdd_handle> ememo;

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
	static map<skmemo, spbdd_handle>::const_iterator it;
	if ((it = ememo.find(x = { p1, p2, args, bits })) != ememo.end())
		return it->second;
	spbdd_handle r = bdd_handle::T;
	for (size_t b = 0; b != bits; ++b)
		r = r && ::from_eq(pos(b, p1, args), pos(b, p2, args));
	return ememo.emplace(x, r), r;
}

spbdd_handle tables::from_fact(const term& t) {
	spbdd_handle r = bdd_handle::T;
	static varmap vs;
	vs.clear();
	auto it = vs.end();
	for (size_t n = 0, args = t.size(); n != args; ++n)
		if (t[n] >= 0)
			r = r && from_sym(n, args, t[n]);
		else if (vs.end() == (it = vs.find(t[n]))) {
			vs.emplace(t[n], n);
			if (!t.neg) r = r && range(n, t.tab);
		} else r = r && from_sym_eq(n, it->second, args);
	return r;
}

sig tables::get_sig(const raw_term&t) {return{dict.get_rel(t.e[0].e),t.arity};}

term tables::from_raw_term(const raw_term& r) {
	ints t;
	lexeme l;
	for (size_t n = 1; n < r.e.size(); ++n)
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
	return term(r.neg, smap.at(get_sig(r)), t);
}

void tables::out(wostream& os) const {
	for (ntable tab = 0; (size_t)tab != ts.size(); ++tab)
		out(os, ts[tab].t, tab);
}

void tables::out(const rt_printer& f) const {
	for (ntable tab = 0; (size_t)tab != ts.size(); ++tab)
		out(ts[tab].t, tab, f);
}

void tables::out(wostream& os, spbdd_handle x, ntable tab) const {
	out(x, tab, [&os](const raw_term& rt) {
		os << rt << L'.' << endl;
	});
}

void tables::decompress(spbdd_handle x, ntable tab, const cb_decompress& f)
	const {
	allsat_cb(x&&ts[tab].t, ts[tab].len * bits,
		[tab, &f, this](const bools& p, int_t DBG(y)) {
		DBG(assert(abs(y) == 1);)
		const size_t args = ts[tab].len;
		term r(false, tab, ints(args, 0));
		for (size_t n = 0; n != args; ++n)
			for (size_t k = 0; k != bits; ++k)
				if (p[pos(k, n, args)])
					r[n] |= 1 << k;
		f(r);
	})();
}

void tables::out(spbdd_handle x, ntable tab, const rt_printer& f) const {
	lexeme op(dict.get_lexeme(L"(")), cl(dict.get_lexeme(L")"));
	decompress(x, tab, [op, cl, tab, f, this](const term& r) {
		raw_term rt;
		const size_t args = ts[tab].len;
		rt.e.resize(args+1),
		rt.e[0]=elem(elem::SYM,dict.get_rel(get<0>(ts[tab].s)));
		for (size_t n = 1; n != args + 1; ++n) {
			int_t arg = r[n - 1];
			if (arg & 1) rt.e[n]=elem((wchar_t)(arg>>2));
			else if (arg & 2) rt.e[n]=elem((int_t)(arg>>2));
			else rt.e[n]=elem(elem::SYM, dict.get_sym(arg));
		}
		rt.arity = get<ints>(ts[tab].s), rt.insert_parens(op, cl),
		f(rt);
	});
}

template<typename T, typename F>
void for_each1(T& x, F f) { for (auto y : x) f(y); }

template<typename T, typename F>
void for_each2(T& x, F f) { for (auto y : x) for (auto z : y) f(z); }

template<typename T1, typename T2, typename F>
void for_each12(T1& x, T2& y, F f) { for_each1(x, f), for_each2(y, f); }

void term::replace(const map<int_t, int_t>& m) {
	auto it = m.end();
	for (int_t& i : *this) if (m.end() != (it = m.find(i))) i = it->second;
}

void tables::align_vars(term& h, set<term>& b) const {
	set<int_t> vs;
	for_each12(h, b, [&vs](int_t i) { if (i < 0) vs.emplace(i); });
	if (vs.empty()) return;
	vs.clear();
	map<int_t, int_t> m;
	for (size_t n = 0; n != h.size(); ++n)
		if (h[n] < 0 && !has(m, h[n])) m.emplace(h[n], -m.size()-1);
	for (const term& t : b)
		for (int_t i : t)
			if (i < 0 && !has(m, i)) m.emplace(i, -m.size()-1);
	set<term> sb;
	for (term t : b) t.replace(m), sb.insert(t);
	h.replace(m), b = sb;
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
tables::varmap tables::get_varmap(const term& h, const T& b, size_t &varslen) {
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
	set<int_t> pvars, nvars;
	for (const term& t : a)
		for (size_t n = 0; n != t.size(); ++n)
			if (t[n] < 0) (t.neg ? nvars : pvars).insert(t[n]);
	for (int_t i : pvars) nvars.erase(i);
	if (h.neg) for (int_t i : h) if (i < 0) nvars.erase(i);
	bdd_handles v;
	for (int_t i : nvars) range(vm.at(i), len, v);
	if (!h.neg) {
		set<int_t> hvars;
		for (int_t i : h) if (i < 0) hvars.insert(i);
		for (const term& t : a) for (int_t i : t) hvars.erase(i);
		for (int_t i : hvars) range(vm.at(i), len, v);
	}
	return bdd_and_many(v);
}

body tables::get_body(const term& t,const varmap& vm,size_t len) const {
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

void tables::get_facts(const raw_prog& p) {
	map<ntable, set<spbdd_handle>> f;
	for (const raw_rule& r : p.r)
		if (r.type == raw_rule::GOAL) {
			assert(r.h.size() == 1 && r.b.empty());
			term x = from_raw_term(r.h[0]);
			goals[x.tab].insert(from_fact(x));
		} else if (r.type == raw_rule::NONE)
			for (const raw_term& x : r.h)
				if (r.b.empty()) {
					term h = from_raw_term(x);
					f[h.tab].insert(from_fact(h));
				}
	clock_t start, end;
	measure_time_start();
	bdd_handles v;
	for (auto x : f) {
		spbdd_handle r = bdd_handle::F;
		for (auto y : x.second) r = r || y;
		ts[x.first].t = r;
	}
	measure_time_end();
}

/*bool tables::cqc(const set<rule>& rs, const rule& r, size_t a, tables& tb)const{
	int_t m = 0;
	for (int_t i : r.t) m = max(m, i);
	for (int_t i : r.r[a]) m = max(m, i);
	bool bsym = false, bnum = false, bchr = false;

}

bool tables::cqc(const set<rule>& rs, rule& r) {
	tables tb(false);
	tb.bits = bits, tb.ts = ts, tb.smap = smap;
	for (const rule& x : rs)
		if (!x.equals_termwise(r))
			tb.rules.push_back(x);
	for (size_t n = 0; n < r.size();)
		if (cqc(rs, r, n, tb)) r.erase(n);
		else ++n;
}*/

void tables::get_rules(const raw_prog& p) {
	get_facts(p);
	map<term, set<set<term>>> m;
	set<term> s;
	for (const raw_rule& r : p.r)
		if (r.type == raw_rule::NONE && !r.b.empty())
			for (const raw_term& x : r.h) {
				term h = from_raw_term(x);
				for (const vector<raw_term>& y : r.b) {
					for (const raw_term& z : y)
						s.emplace(from_raw_term(z));
					align_vars(h, s), m[h].emplace(move(s));
				}
			}
	set<rule> rs;
	varmap::const_iterator it;
	set<body*, ptrcmp<body>>::const_iterator bit;
	set<alt*, ptrcmp<alt>>::const_iterator ait;
	body* y;
	alt* aa;
	for (auto x : m) {
		varmap v;
		set<int_t> hvars;
		const term &t = x.first;
		rule r;
		if (t.neg) datalog = false;
		ts[t.tab].ext = false;
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
			set<int_t> vs;
			set<pair<body, term>> b;
			varmap vm = get_varmap(t, al, a.varslen);
			for (const term& t : al)
				b.insert({get_body(t, vm, a.varslen), t});
			a.rng = get_alt_range(t, al, vm, a.varslen);
			for (auto x : b) {
				a.t.push_back(x.second);
				if ((bit=body::s.find(&x.first))!=body::s.end())
					a.push_back(*bit);
				else	*(y = new body) = x.first,
					a.push_back(y), body::s.insert(y);
			}
			auto d = deltail(a.varslen, r.len);
			a.ex = d.first, a.perm = d.second;
			as.insert(a);
		}
		for (alt x : as)
			if ((ait = alt::s.find(&x)) != alt::s.end())
				r.push_back(*ait);
			else	*(aa = new alt) = x,
				r.push_back(aa), alt::s.insert(aa);
		rs.insert(r);
	}
	m.clear();
	for (rule r : rs) rules.push_back(r);
/*	if (!optimize) for (rule r : rs) rules.push_back(r);
	else {
		for (rule r : rs)
			if (!cqc(rs, r))
				rules.push_back(r);
		break_shared();
		cqc_minimize();
	}*/
}

void tables::load_string(lexeme r, const wstring& s) {
	int_t rel = dict.get_rel(r);
	const ints ar = {0,-1,-1,1,-2,-2,-1,1,-2,-1,-1,1,-2,-2};
	const ntable t1 = get_table({rel, ar}), t2 = get_table({rel, {3}});
	const int_t sspace = dict.get_sym(dict.get_lexeme(L"space")),
		salpha = dict.get_sym(dict.get_lexeme(L"alpha")),
		salnum = dict.get_sym(dict.get_lexeme(L"alnum")),
		sdigit = dict.get_sym(dict.get_lexeme(L"digit")),
		sprint = dict.get_sym(dict.get_lexeme(L"printable"));
	term t;
	bdd_handles b1, b2;
	b1.reserve(s.size()), b2.reserve(s.size());
	t.resize(3), t.neg = false;
	for (int_t n = 0; n != (int_t)s.size(); ++n) {
		t[0] = mknum(n), t[1] = mkchr(s[n]), t[2] = mknum(n+1),
		b1.push_back(from_fact(t)), t[1] = t[0];
		if (iswspace(s[n])) t[0] = sspace, b2.push_back(from_fact(t));
		if (iswdigit(s[n])) t[0] = sdigit, b2.push_back(from_fact(t));
		if (iswalpha(s[n])) t[0] = salpha, b2.push_back(from_fact(t));
		if (iswalnum(s[n])) t[0] = salnum, b2.push_back(from_fact(t));
		if (iswprint(s[n])) t[0] = sprint, b2.push_back(from_fact(t));
	}
	clock_t start, end;
	output::to(L"debug")<<"load_string or_many: ";
	measure_time_start();
	ts[t1].t = bdd_or_many(move(b1)), ts[t2].t = bdd_or_many(move(b2));
	measure_time_end();
}

template<typename T> bool subset(const set<T>& small, const set<T>& big) {
	for (const T& t : small) if (!has(big, t)) return false;
	return true;
}

void tables::get_var_ex(size_t arg, size_t args, bools& b) const {
	for (size_t k = 0; k != bits; ++k) b[pos(k, arg, args)] = true;
}

void tables::get_sym(int_t sym, size_t arg, size_t args, spbdd_handle& r) const{
	for (size_t k = 0; k != bits; ++k) r = r && from_bit(k, arg, args, sym);
}

void tables::get_alt_ex(alt& a, const term& h) const {
	varmap vm = get_varmap(h, a.t, a.varslen);
	set<int_t> hvars;
	set<size_t> bodies;
	map<int_t, set<size_t>> m;
	for (int_t i : h) if (i < 0) hvars.insert(i);
	DBG(assert(a.size() == a.t.size());)
	for (size_t n = 0; n != a.size(); ++n) {
		for (int_t i : a.t[n])
			if (i < 0 && !has(hvars, i))
				m[i].emplace(n);
		bodies.insert(n);
	}
/*	size_t sz = (size_t)-1, v = 0;
	for (auto x : m)
		if (x.second.size() < sz)
			sz = x.second.size(), v = x.first;*/
	while (!m.empty()) {
		auto it = m.begin();
		bools ex = bools(a.varslen * bits, false);
		get_var_ex(vm.at(it->first), a.varslen, ex);
		uints s;
		for (auto x : it->second)
			if (has(bodies, x)) s.push_back(x), bodies.erase(x);
//		a.order.push_back({s, ex});
		for (auto x : m)
			if (x.first!=it->first&&subset(x.second, it->second))
				m.erase(x.first);
		m.erase(it);
	}
}

ntable tables::get_table(const sig& s) {
	auto it = smap.find(s);
	if (it != smap.end()) return it->second;
	ntable nt = ts.size();
	size_t len = sig_len(s);
	max_args = max(max_args, len);
	table tb;
	tb.t = bdd_handle::F;
	return tb.s = s, tb.len = len, ts.push_back(tb), smap.emplace(s,nt), nt;
}

void tables::add_prog(const raw_prog& p, const strs_t& strs) {
	rules.clear(), datalog = true;
	auto f = [this](const raw_term& t) {
		for (size_t n = 1; n < t.e.size(); ++n)
			switch (t.e[n].type) {
				case elem::NUM: nums = max(nums, t.e[n].num+1);
						break;
				case elem::CHR: chars = 256; break;
				case elem::SYM: dict.get_sym(t.e[n].e),
						syms = max(syms,
							(int_t)dict.nsyms());
				default: ;
			}
		get_table(get_sig(t));
	};
	for (const raw_rule& r : p.r) {
		for (const raw_term& t : r.h) f(t);
		for (const auto& a : r.b) for (const raw_term& t : a) f(t);
	}
	for (auto x : strs) nums = max(nums, (int_t)x.second.size()+1);
	int_t u = max((int_t)1, max(nums, max(chars, syms))-1);
	while (u >= (1 << (bits - 2))) add_bit();
	get_rules(p);
	clock_t start, end;
	output::to(L"debug")<<"load_string: ";
	measure_time_start();
	for (auto x : strs) load_string(x.first, x.second);
	measure_time_end();
	smemo.clear(), ememo.clear();
	bdd::gc();
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

spbdd_handle tables::body_query(body& b, size_t /*DBG(len)*/) {
	if (b.a) return alt_query(*b.a, 0);
//	if (b.ext) return b.q;
//	DBG(assert(bdd_nvars(b.q) <= b.ex.size());)
//	DBG(assert(bdd_nvars(get_table(b.tab, db)) <= b.ex.size());)
	if (b.tlast && b.tlast->b == ts[b.tab].t->b) return b.rlast;
	b.tlast = ts[b.tab].t;
	b.rlast=(b.neg ? bdd_and_not_ex_perm : bdd_and_ex_perm)
		(b.q, ts[b.tab].t, b.ex, b.perm);
//	DBG(assert(bdd_nvars(b.rlast) < len*bits);)
	return b.rlast;
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
	bdd_handles v1 = { a.rng };
	spbdd_handle x;
	DBG(assert(!a.empty());)
	for (size_t n = 0; n != a.size(); ++n)
		if (bdd_handle::F == (x = body_query(*a[n], a.varslen))) {
			a.insert(a.begin(), a[n]), a.erase(a.begin() + n + 1);
			return bdd_handle::F;
		} else v1.push_back(x);
	sort(v1.begin(), v1.end(), handle_cmp);
	if (v1 == a.last) return a.rlast;// { v.push_back(a.rlast); return; }
	a.last = move(v1);
//	if ((x = bdd_and_many_ex(a.last, a.ex)) != bdd_handle::F)
//		v.push_back(a.rlast = x ^ a.perm);
//	bdd_handles v;
	return a.rlast = bdd_and_many_ex_perm(a.last, a.ex, a.perm);
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
		if (s == bdd_handle::F) {
			output::to(L"output") << "unsat." << endl;
			exit(0); //FIXME
		}
		x = (t || a) % d;
	}
//	DBG(assert(bdd_nvars(x) < len*bits);)
	return x != t && (t = x, true);
}

char tables::fwd() {
	bdd_handles add, del;
//	DBG(out(wcout<<"db before:"<<endl);)
	for (rule& r : rules) {
		bdd_handles v(r.size());
		for (size_t n = 0; n != r.size(); ++n)
			v[n] = alt_query(*r[n], r.len);
		spbdd_handle x;
		if (v == r.last) { if (datalog) continue; x = r.rlast; }
		else r.last = v, x = r.rlast = bdd_or_many(move(v)) && r.eq;
//		DBG(assert(bdd_nvars(x) < r.len*bits);)
		if (x == bdd_handle::F) continue;
		(r.neg ? ts[r.tab].del : ts[r.tab].add).push_back(x);
	}
	bool b = false;
	for (table& t : ts) b |= t.commit(DBG(bits));
	return b;
/*	if (!b) return false;
	for (auto x : goals)
		for (auto y : x.second)
			b &= (y && ts[x.first].t) == y;
	if (b) return (wcout <<"found"<<endl), false;
	return b;*/
}

set<pair<ntable, spbdd_handle>> tables::get_front() const {
	set<pair<ntable, spbdd_handle>> r;
	for (ntable tab = 0; tab != (ntable)ts.size(); ++tab)
		r.insert({tab, ts[tab].t});
	return r;
}

bool tables::pfp() {
	size_t step = 0;
	char b;
	for (set<set<pair<ntable, spbdd_handle>>> s; (b = fwd()), true;) {
		output::to(L"info") << "step: " << step++ << endl;
		if (!b/* == 1 || b == 2*/) return true;
		if (!datalog && !s.emplace(get_front()).second) return false;
	}
	throw 0;
}

bool tables::run_prog(const raw_prog& p, const strs_t& strs) {
	clock_t start, end;
	measure_time_start();
	add_prog(p, strs);
	measure_time_end();
	measure_time_start();
	bool r = pfp();
	measure_time_end();
	return r;
}

tables::tables(bool optimize) : dict(*new dict_t), optimize(optimize) {}

tables::~tables() {
	delete &dict;
	while (!body::s.empty()) {
		body *b = *body::s.begin();
		body::s.erase(body::s.begin());
		delete b;
	}
}

set<body*, ptrcmp<body>> body::s;
set<alt*, ptrcmp<alt>> alt::s;
