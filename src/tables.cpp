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
#include "dict.h"
#include "input.h"
using namespace std;
using namespace std::placeholders;

#define mkchr(x) ((((int_t)x)<<2)|1)
#define mknum(x) ((((int_t)x)<<2)|2)

size_t sig_len(const sig_t& s) {
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
vbools tables::allsat(spbdd x, size_t args) const {
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

spbdd tables::leq_const(int_t c, size_t arg, size_t args, size_t bit) const {
	if (!--bit) return (c & 1) ? T : bdd::add(pos(0, arg, args)+1, F, T);
	return (c & (1 << bit)) ?
		bdd::add(pos(bit,arg,args)+1, leq_const(c, arg, args, bit), T) :
		bdd::add(pos(bit,arg,args)+1, F, leq_const(c, arg, args, bit));
}

void tables::range(size_t arg, size_t args, bdds& v) {
	spbdd	ischar= bdd::from_bit(pos(0, arg, args), true) &&
			bdd::from_bit(pos(1, arg, args), false);
	spbdd	isnum = bdd::from_bit(pos(0, arg, args), false) &&
			bdd::from_bit(pos(1, arg, args), true);
	spbdd	issym = bdd::from_bit(pos(0, arg, args), false) &&
			bdd::from_bit(pos(1, arg, args), false);
	bdds r={ischar || isnum || issym,
		(!chars	? T%ischar : bdd_impl(ischar,
			leq_const(mkchr(chars-1), arg, args, bits))),
		(!nums 	? T%isnum : bdd_impl(isnum, 
			leq_const(mknum(nums-1), arg, args, bits))),
		(!syms 	? T%issym : bdd_impl(issym, 
			leq_const(((syms-1)<<2), arg, args, bits)))};
	v.insert(v.end(), r.begin(), r.end());
}

spbdd tables::range(size_t arg, ntable tab) {
	array<int_t, 6> k = { syms, nums, chars, (int_t)tab, (int_t)arg,
		(int_t)bits };
	auto it = range_memo.find(k);
	if (it != range_memo.end()) return it->second;
	bdds v;
	return	range(arg, ts[tab].len, v), onmemo(),
		range_memo[k] = bdd_and_many(move(v));
}

sizes perm_init(size_t n) {
	sizes p(n);
	while (n--) p[n] = n;
	return p;
}

spbdd tables::add_bit(spbdd x, size_t args) {
	sizes perm = perm_init(args * bits);
	for (size_t n = 0; n != args; ++n)
		for (size_t k = 0; k != bits; ++k)
			perm[pos(k, n, args)] = pos(k+1, bits+1, n, args);
	bdds v = { x ^ perm };
	for (size_t n = 0; n != args; ++n)
		v.push_back(bdd::from_bit(pos(0, bits + 1, n, args), false));
	return bdd_and_many(move(v));
}

void tables::add_bit() {
	range_clear_memo();
	spbdd x = F;
	bdds v;
	for (size_t n = 0; n != ts.size(); ++n)
		ts[n].t = add_bit(ts[n].t, ts[n].len);
	++bits;
}

spbdd tables::from_fact(const term& t) {
//	bdds v;
	spbdd r = T;
	varmap vs;
	auto it = vs.end();
	for (size_t n = 0, args = t.size(), b; n != args; ++n)
		if (t[n] >= 0)
			for (b = 0; b != bits; ++b)
				r = r && from_bit(b, n, args, t[n]);
//				v.push_back(from_bit(b, n, args, t[n]));
		else if (vs.end() == (it = vs.find(t[n]))) {
			vs.emplace(t[n], n);
			if (!t.neg) r = r && range(n, t.tab);
//				v.push_back(range(n, t.tab));
		} else for (b = 0; b != bits; ++b)
//			v.push_back(
			r = r && bdd::from_eq(
				pos(b, n, args), pos(b, it->second, args));
	return r;
//	return bdd_and_many(move(v));
}

void tables::add_term(const term& t, set<spbdd>& s) {
	s.insert(from_fact(t));
//	ts[t.tab].t = from_fact(t) || ts[t.tab].t;
}

sig_t tables::get_sig(const raw_term&t){return{dict.get_rel(t.e[0].e),t.arity};}

tables::term tables::from_raw_term(const raw_term& r) {
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
	for (ntable tab=0; (size_t)tab != ts.size(); ++tab)
		out(os, ts[tab].t, tab);
}

void tables::out(wostream& os, spbdd x, ntable tab) const {
	lexeme op(dict.get_lexeme(L"(")), cl(dict.get_lexeme(L")"));
	allsat_cb(x&&ts[tab].t, ts[tab].len * bits,
		[&os, tab, op, cl, this](const bools& p, spbdd DBG(y)) {
		DBG(assert(y->leaf());)
		const size_t args = ts[tab].len;
		term r(false, tab, ints(args, 0));
		for (size_t n = 0; n != args; ++n)
			for (size_t k = 0; k != bits; ++k)
				if (p[pos(k, n, args)])
					r[n] |= 1 << k;
		raw_term rt;
		rt.e.resize(args+1),
		rt.e[0]=elem(elem::SYM,dict.get_rel(get<0>(ts[tab].s)));
		for (size_t n = 1; n != args + 1; ++n) {
			int_t arg = r[n - 1];
			if (arg & 1) rt.e[n]=elem((wchar_t)(arg>>2));
			else if (arg & 2) rt.e[n]=elem((int_t)(arg>>2));
			else rt.e[n]=elem(elem::SYM, dict.get_sym(arg));
		}
		rt.arity = get<ints>(ts[tab].s), rt.insert_parens(op, cl),
		os<<rt<<L'.'<<endl;
	})();
}

template<typename T, typename F>
void for_each1(T& x, F f) { for (auto y : x) f(y); }

template<typename T, typename F>
void for_each2(T& x, F f) { for (auto y : x) for (auto z : y) f(z); }

template<typename T1, typename T2, typename F>
void for_each12(T1& x, T2& y, F f) { for_each1(x, f), for_each2(y, f); }

void tables::term::replace(const map<int_t, int_t>& m) {
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

sizes tables::get_perm(const term& t, const varmap& m, size_t len) const {
	sizes perm = perm_init(t.size() * bits);
	for (size_t n = 0, b; n != t.size(); ++n)
		if (t[n] < 0)
			for (b = 0; b != bits; ++b)
				perm[pos(b,n,t.size())] = pos(b,m.at(t[n]),len);
	return perm;
}

tables::varmap tables::get_varmap(const term& h, const set<term>& b,
	size_t &varslen) {
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

spbdd tables::get_alt_range(const term& h, const set<term>& a,
	const varmap& vm, size_t len) {
	set<int_t> pvars, nvars;
	for (const term& t : a)
		for (size_t n = 0; n != t.size(); ++n)
			if (t[n] < 0) (t.neg ? nvars : pvars).insert(t[n]);
	for (int_t i : pvars) nvars.erase(i);
	if (h.neg) for (int_t i : h) if (i < 0) nvars.erase(i);
	bdds v;
	for (int_t i : nvars) range(vm.at(i), len, v);
	if (!h.neg) {
		set<int_t> hvars;
		for (int_t i : h) if (i < 0) hvars.insert(i);
		for (const term& t : a) for (int_t i : t) hvars.erase(i);
		for (int_t i : hvars) range(vm.at(i), len, v);
	}
	return bdd_and_many(v);
}

#define and_bit(b, arg, args, n, t) ((t) = (t) && from_bit(b, arg, args, n))
#define and_eq_(b, arg1, arg2, args, t) \
	((t) = (t) && bdd::from_eq(pos(b, arg1, args), pos(b, arg2, args)))

tables::body tables::get_body(const term& t,const varmap& vm,size_t len) const {
	body b;
	b.neg = t.neg, b.tab = t.tab, b.perm = get_perm(t, vm, len),
	b.q = T, b.ex = bools(t.size() * bits, false);
	varmap m;
	auto it = m.end();
	for (size_t n = 0; n != t.size(); ++n)
		if (t[n] >= 0)
			for (size_t k = 0; k != bits; ++k)
				and_bit(k, n, t.size(), t[n], b.q),
				b.ex[pos(k, n, t.size())] = true;
		else if (m.end() == (it = m.find(t[n]))) m.emplace(t[n], n);
		else for (size_t k = 0; k != bits; ++k)
			and_eq_(k, n, it->second, t.size(), b.q),
			b.ex[pos(k, n, t.size())] = true;
//	DBG(assert(bdd_nvars(b.q) <= b.ex.size());)
//	DBG(assert(t.size() == siglens[t.tab]);)
	return b;
}

void tables::get_rules(const raw_prog& p) {
	map<term, set<set<term>>> m;
	set<term> s;
	map<ntable, set<spbdd>> f;
	for (const raw_rule& r : p.r)
		for (const raw_term& x : r.h) {
			term h = from_raw_term(x);
			if (r.b.empty()) add_term(h, f[h.tab]);
			else for (const vector<raw_term>& y : r.b) {
				for (const raw_term& z : y)
					s.emplace(from_raw_term(z));
				align_vars(h, s), m[h].emplace(move(s));
			}
		}
	for (auto x : f) {
		bdds v;
		for (auto y : x.second) v.push_back(y);
		ts[x.first].t = bdd_or_many(v);
	}
	f.clear();
	set<rule> rs;
	for (auto x : m) {
		varmap v;
		set<int_t> hvars;
		auto it = v.end();
		const term &t = x.first;
		rule r;
		if (t.neg) datalog = false;
		r.neg = t.neg, r.tab = t.tab, r.eq = T;
		for (size_t n = 0; n != t.size(); ++n)
			if (t[n] >= 0)
				for (size_t b = 0; b != bits; ++b)
					and_bit(b, n, t.size(), t[n], r.eq);
			else if (v.end() == (it = v.find(t[n])))
				v.emplace(t[n], n);
			else for (size_t b = 0; b != bits; ++b)
				and_eq_(b, n, it->second, t.size(), r.eq);
		set<alt> as;
		for (const set<term>& al : x.second) {
			alt a;
			set<int_t> vs;
			set<body> b;
			varmap vm = get_varmap(t, al, a.varslen);
			for (const term& t : al)
				b.insert(get_body(t, vm, a.varslen));
			a.rng = get_alt_range(t, al, vm, a.varslen);
			for (body x : b) {
				auto it = body::s.find(&x);
				if (it != body::s.end()) a.push_back(*it);
				body* y = new body;
				*y = x, a.push_back(y), body::s.insert(y);
			}
			as.insert(a);
		}
		for (const alt& x : as) r.push_back(x);
		r.len = t.size(), rs.insert(r);
	}
	for (const rule& r : rs) rules.push_back(r);
}

void tables::add_prog(const raw_prog& p) {
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
		sig_t s = get_sig(t);
		if (has(smap, s)) return;
		ntable nt = ts.size();
		size_t len = sig_len(s);
		max_args = max(max_args, len);
		table t;
		t.s = s, t.len = len, ts.push_back(t), smap.emplace(s, nt);
	};
	for (const raw_rule& r : p.r) {
		for (const raw_term& t : r.h) f(t);
		for (const auto& a : r.b) for (const raw_term& t : a) f(t);
	}
	int_t u = max((int_t)1, max(nums, max(chars, syms))-1);
	while (u >= (1 << (bits - 2))) add_bit();
	get_rules(p);
}

spbdd tables::deltail(spbdd x, size_t len1, size_t len2) const {
	if (len1 == len2) return x;
	bools ex(len1 * bits, false);
	sizes perm = perm_init(len1 * bits);
	for (size_t n = 0; n != len1; ++n)
		for (size_t k = 0; k != bits; ++k)
			if (n >= len2) ex[pos(k, n, len1)] = true;
			else perm[pos(k, n, len1)] = pos(k, n, len2);
	return bdd_permute_ex(x, ex, perm);
}

spbdd tables::body_query(body& b) {
//	DBG(assert(bdd_nvars(b.q) <= b.ex.size());)
//	DBG(assert(bdd_nvars(get_table(b.tab, db)) <= b.ex.size());)
	if (b.tlast == ts[b.tab].t) return b.rlast;
	b.tlast = ts[b.tab].t;
	return b.rlast = bdd_permute_ex(b.neg ? b.q % ts[b.tab].t :
			(b.q && ts[b.tab].t), b.ex, b.perm);
}

void tables::alt_query(alt& a, size_t len, bdds& v) {
	bdds v1 = { a.rng };
	spbdd x;
	assert(!a.empty());
	for (body* b : a)
		if (F == (x = body_query(*b))) return;
		else v1.push_back(x);
	if (v1 == a.last) { v.push_back(a.rlast); return; }
	a.last = v1;
	if ((x = bdd_and_many(move(v1))) != F)
		v.push_back(a.rlast = deltail(x, a.varslen, len));
}

bool tables::table::commit() {
	if (add.empty() && del.empty()) return false;
	spbdd x;
	if (add.empty()) x = t % bdd_or_many(move(del));
	else if (del.empty()) add.push_back(t), x = bdd_or_many(move(add));
	else {
		spbdd a = bdd_or_many(move(add)), d = bdd_or_many(move(del)),
		      s = a % d;
		if (s == F) { wcout << "unsat" << endl; exit(0); }
		x = (t || a) % d;
	}
	if (x == t) return false;
	return t = x, true;
}

bool tables::fwd() {
	bdds add, del;
	DBG(out(wcout<<"db before:"<<endl);)
	for (rule& r : rules) {
		bdds v;
		for (alt& a : r) alt_query(a, r.len, v);
		spbdd x;
		if (v == r.last) { if (datalog) continue; x = r.rlast; }
		else r.last = v, x = r.rlast = bdd_or_many(move(v)) && r.eq;
		if (x == F) continue;
		(r.neg ? ts[r.tab].del : ts[r.tab].add).push_back(x);
	}
	bool b = false;
	for (table& t : ts) b |= t.commit();
	if (onmemo(0) > 1e+7) memos_clear();//, wcerr<<onmemo(0)<<endl;
	return b;
}

set<pair<ntable, spbdd>> tables::get_front() const {
	set<pair<ntable, spbdd>> r;
	for (ntable tab = 0; tab != (ntable)ts.size(); ++tab)
		r.insert({tab, ts[tab].t});
	return r;
}

bool tables::pfp() {
	size_t step = 0;
	bool b;
	for (set<set<pair<ntable, spbdd>>> s; (b = fwd()), true;) {
		wcerr << "step: " << step++ << endl;
		if (!b) return true;
		if (!datalog && !s.emplace(get_front()).second) return false;
//		if (step % 2) memos_clear();
	}
	throw 0;
}

tables::tables() : dict(*new dict_t) {}
tables::~tables() {
	delete &dict;
	for (body* b : body::s) delete b;
}

set<tables::body*, tables::body::pbodycmp> tables::body::s;
