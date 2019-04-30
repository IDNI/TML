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
	for (auto x : get<1>(s)) if (x > 0) r += x;
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
	vbools v = ::allsat(x, tbits + bits * args), s;
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
	array<int_t, 7> k = { syms, nums, chars, (int_t)tab, (int_t)arg,
		(int_t)bits, (int_t)tbits };
	auto it = range_memo.find(k);
	if (it != range_memo.end()) return it->second;
	bdds v;
	return	range(arg, siglens[tab], v), onmemo(),
		range_memo[k] = bdd_and_many(move(v));
}

sizes perm_init(size_t n) {
	sizes p(n);
	while (n--) p[n] = n;
	return p;
}

spbdd tables::add_bit(spbdd x, ntable tab) {
	const size_t args = siglens[tab];
	sizes perm = perm_init(args * bits + tbits);
	for (size_t n = 0; n != args; ++n)
		for (size_t k = 0; k != bits; ++k)
			perm[pos(k, n, args)] = pos(k+1, bits+1, n, args);
	bdds v = { x ^ perm };
	for (size_t n = 0; n != args; ++n)
		v.push_back(bdd::from_bit(pos(0, bits + 1, n, args), false));
	x = bdd_and_many(move(v));
	return x;
}

void tables::add_bit() {
	range_clear_memo();
	spbdd x = F;
	for (size_t n=0; n!=tbdds.size(); ++n) x = x || add_bit(db&&tbdds[n],n);
	db = x, ++bits;
	validate();
}

void tables::add_tbit() {
	range_clear_memo();
	sizes perm(max_args * bits + tbits);
	for (size_t n = 0; n != perm.size(); ++n) perm[n] = n + 1;
	db = (db ^ perm) && bdd::from_bit(0, false), ++tbits;
	for (size_t k = 0; k != tbdds.size(); ++k) {
		perm.resize(siglens[k]);
		for (size_t n = 0; n != perm.size(); ++n) perm[n] = n + 1;
		tbdds[k] = (tbdds[k] ^ perm) && bdd::from_bit(0, false);
	}
	validate();
}

spbdd tables::from_fact(const term& t) {
	bdds v;
	varmap vs;
	auto it = vs.end();
	for (size_t n = 0, args = t.size(), b; n != args; ++n)
		if (t[n] >= 0)
			for (b = 0; b != bits; ++b)
				v.push_back(from_bit(b, n, args, t[n]));
		else if (vs.end() == (it = vs.find(t[n]))) {
			vs.emplace(t[n], n);
			if (!t.neg) v.push_back(range(n, t.tab));
		} else for (b = 0; b != bits; ++b)
			v.push_back(bdd::from_eq(
				pos(b, n, args), pos(b, it->second, args)));
	return bdd_and_many(move(v));
}

ntable tables::add_table(sig_t s) {
	auto it = smap.find(s);
	if (it != smap.end()) return it->second;
	ntable nt = sigs.size();
	size_t len = sig_len(s);
	max_args = max(max_args, len);
	if (!sigs.size() || sigs.size() > (size_t)(1 << (tbits-1))) add_tbit();
	spbdd t = T;
	for (size_t b = 0; b != tbits; ++b)
		t = t && bdd::from_bit(b, nt & (1 << (tbits - b - 1)));
	smap.emplace(s, nt), sigs.push_back(s), tbdds.push_back(t),
	siglens.push_back(len);
	return nt;
}

void tables::add_term(const term& t) {
	DBG(assert(t.tab < (1 << tbits));)
//	if (t.tab >= (1 << tbits)) add_tbit();
	db = (from_fact(t) && tbdds[t.tab]) || db;
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
	return term(r.neg, add_table(get_sig(r)), t);
}

//ntable tables::get_table(const raw_term& t) { return add_table(get_sig(t)); }

void tables::out(wostream& os) const { out(os, db); }

void tables::out(wostream& os, spbdd x) const {
	for (ntable tab=0; (size_t)tab != tbdds.size(); ++tab) out(os, x, tab);
}

void tables::out(wostream& os, spbdd x, ntable tab) const {
	lexeme op(dict.get_lexeme(L"(")), cl(dict.get_lexeme(L")"));
	allsat_cb(x&&tbdds[tab], siglens[tab] * bits + tbits,
		[&os, tab, op, cl, this](const bools& p, spbdd DBG(y)) {
		DBG(assert(y->leaf());)
		const size_t args = siglens[tab];
		term r(false, tab, ints(args, 0));
		for (size_t n = 0; n != args; ++n)
			for (size_t k = 0; k != bits; ++k)
				if (p[pos(k, n, args)])
					r[n] |= 1 << k;
		raw_term rt;
		rt.e.resize(args+1),
		rt.e[0]=elem(elem::SYM,dict.get_rel(get<0>(sigs[tab])));
		for (size_t n = 1; n != args + 1; ++n) {
			int_t arg = r[n - 1];
			if (arg & 1) rt.e[n]=elem((wchar_t)(arg>>2));
			else if (arg & 3) rt.e[n]=elem((int_t)(arg>>2));
			else rt.e[n]=elem(elem::SYM, dict.get_sym(arg));
		}
		rt.arity = get<1>(sigs[tab]), rt.insert_parens(op, cl),
		os<<rt<<endl;
	})();
}

void tables::validate() {
#ifdef DEEPDEBUG
	bdd::validate();
	if (db == F) return;
	auto bddcmp = [](spbdd x, spbdd y) {
		bdd::validate();
		bool b = x == y;
		bool c = bdd::_bddcmp(x, y);
		if (b != c) bdd::validate(x, y);
		assert((x == y) == (bdd::_bddcmp(x, y)));
		return x == y;
	};
	spbdd t = F;
	for (size_t n = 0; n != tbdds.size(); ++n) t = t || tbdds[n];
	if (!bddcmp(F, db%t) || !bddcmp(db, db&&t)) {
		for (size_t n = 0; n != tbdds.size(); ++n) {
			wcout<<"tbdd["<<n<<"]:"<<endl<<::allsat(tbdds[n], tbits)
			<<endl<<"db:"<<endl<<
			::allsat(db, tbits + bits*max_args+1)<<endl
			<<"sig: " << dict.get_rel(get<0>(sigs[n])) << L' ';
			for (int_t i : get<1>(sigs[n])) wcout << i << ' ';
			wcout << endl;
		}
		wcout<<"db&&t:"<<endl<<::allsat(db&&t, tbits+max_args*bits);
		spbdd y = db && t;
		assert((db % t) == F);
		assert((db && t) == db);
	}
	assert(tbdds.size() == sigs.size());
	for (size_t n = 0; n != sigs.size(); ++n) {
		t = db && tbdds[n];
		assert(siglens[n] == sig_len(sigs[n]));
		spbdd x;
		for (size_t k = 0; k != siglens[n]; ++k) {
			x = range(k, n);
			if ((x && t) != t) {
				wcout<<"bits: "<<bits<<" tbits: "<<tbits<<endl
				<<"nums: "<<nums<<" syms: "<<syms<<" chars: "
				<<chars<<endl<<"db:"<<endl<<
				::allsat(db,tbits+max_args*bits)<<endl
				<<"t(=db && tbdds["<<n<<"]):"<<endl
				<<::allsat(t, tbits+max_args*bits)<<endl<<
				"x(=range("<<k<<','<<n<<"))&&t:"<<endl
				<<::allsat(x&&t,tbits+max_args*bits)<<endl<<"x:"
				<<endl<<::allsat(x,tbits+max_args*bits)<<endl;
				assert(bddcmp(x && t, t));
			}
		}
	}
#endif
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
	int_t mv = *vs.begin();
	for_each12(h, b, [mv](int_t i) { if (i < 0) i += mv; });
	vs.clear();
	map<int_t, int_t> m;
	for (size_t n = 0; n != h.size(); ++n)
		if (!has(m, h[n])) m.emplace(h[n], -m.size()-1);
	set<term> sb;
	for (term t : b) t.replace(m), sb.insert(t);
	h.replace(m), b = sb;
}

sizes tables::get_perm(const term& t, const varmap& m, size_t len) const {
	sizes perm = perm_init(t.size() * bits + tbits);
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
		for (int_t i : h) hvars.insert(i);
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
	b.q = tbdds[t.tab];
	b.ex = bools(t.size() * bits + tbits, false);
	for (size_t n = 0; n != tbits; ++n) b.ex[n] = true;
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
	return b;
}

void tables::get_rules(const raw_prog& p) {
	map<term, set<set<term>>> m;
	set<term> s;
	for (const raw_rule& r : p.r)
		for (const raw_term& x : r.h) {
			term h = from_raw_term(x);
			if (r.b.empty()) add_term(h);
			else for (const vector<raw_term>& y : r.b) {
				for (const raw_term& z : y)
					s.emplace(from_raw_term(z));
				align_vars(h, s), m[h].emplace(move(s));
			}
		}
	set<rule> rs;
	for (auto x : m) {
		varmap v;
		set<int_t> hvars;
		auto it = v.end();
		const term &t = x.first;
		rule r;
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
			for (const body& x : b) a.push_back(x);
			as.insert(a);
		}
		for (const alt& x : as) r.push_back(x);
		r.len = t.size(), rs.insert(r);
	}
	for (const rule& r : rs) rules.push_back(r);
}

void tables::count_term(const raw_term& r) {
	for (size_t n = 1; n < r.e.size(); ++n)
		switch (r.e[n].type) {
			case elem::NUM: nums = max(nums, r.e[n].num+1); break;
			case elem::CHR: chars = 256; break;
			case elem::SYM: dict.get_sym(r.e[n].e),
					syms = max(syms, (int_t)dict.nsyms());
			default: ;
		}
}

void tables::add_prog(const raw_prog& p) {
	auto f = [this](const raw_term& t) {
		count_term(t);
		sig_t s = get_sig(t);
		if (has(smap, s)) return;
		ntable nt = sigs.size();
		size_t len = sig_len(s);
		max_args = max(max_args, len);
		smap.emplace(s, nt), sigs.push_back(s), siglens.push_back(len);
	};
	for (const raw_rule& r : p.r) {
		for (const raw_term& t : r.h) f(t);
		for (const auto& a : r.b) for (const raw_term& t : a) f(t);
	}
	do { ++tbits; } while (sigs.size() > (size_t)(1<<(tbits-1)));
	while (nums + chars + syms >= (1 << (bits - 2))) ++bits;
	for (ntable tab = 0; tab != (ntable)sigs.size(); ++tab) {
		spbdd t = T;
		for (size_t b = 0; b != tbits; ++b)
			t = t && bdd::from_bit(b, tab & (1 << (tbits - b - 1)));
		tbdds.push_back(t);
	}
	get_rules(p);
}

spbdd tables::get_table(ntable tab, spbdd x) const {
	return x && tbdds[tab];
	return	x->leaf() || x->v() > tbits ? x :
		get_table(tab, tab & (1 << (x->v() - 1)) ? x->h() : x->l());
}

spbdd tables::deltail(spbdd x, size_t len1, size_t len2) const {
	if (len1 == len2) return x;
	bools ex(tbits + len1 * bits, false);
	sizes perm = perm_init(tbits + len1 * bits);
	for (size_t n = 0; n != len1; ++n)
		for (size_t k = 0; k != bits; ++k)
			if (n >= len2) ex[pos(k, n, len1)] = true;
			else perm[pos(k, n, len1)] = pos(k, n, len2);
	return bdd_permute_ex(x, ex, perm);
}

spbdd tables::body_query(const body& b) const {
	return bdd_permute_ex(b.neg ? b.q % get_table(b.tab, db) :
			(b.q && get_table(b.tab, db)), b.ex, b.perm);
}

void tables::alt_query(const alt& a, size_t len, bdds& v) const {
	bdds v1;
	for (const body& b : a) {
		spbdd x = body_query(b) && a.rng;
//		DBG(out(wcout<<"body:"<<endl, x, a.varslen);)
		if (x == F) return;
		v1.push_back(x);
	}
	v.push_back(deltail(bdd_and_many(v1), a.varslen, len));
}

void tables::fwd() {
	bdds add, del;
//	DBG(out(wcout<<"db before:"<<endl);)
	for (const rule& r : rules) {
		bdds v;
		for (const alt& a : r) alt_query(a, r.len, v);
		(r.neg ? del : add).push_back(bdd_or_many(v) && tbdds[r.tab]);
	}
	if (add.empty()) db = db % bdd_or_many(del);
	else if (del.empty()) add.push_back(db), db = bdd_or_many(add);
	else {
		spbdd a = bdd_or_many(add), d = bdd_or_many(del), s = a % d;
		if (s == F) { wcout << "unsat" << endl; exit(0); }
		db = (db || a) % d;
	}
//	DBG(out(wcout<<"add:"<<endl, bdd_or_many(add));)
//	DBG(out(wcout<<"del:"<<endl, bdd_or_many(del));)
//	DBG(out(wcout<<"db after:"<<endl);)
}

bool tables::pfp() {
	spbdd l = db;
	size_t step = 0;
	for (set<spbdd> s; fwd(), true; l = db) {
		wcout << "step: " << step++ << endl;
		if (l == db) return true;
		else if (has(s, l)) return false;
		else s.insert(l);
	}
	throw 0;
}

tables::tables() : dict(*new dict_t) {}
tables::~tables() { delete &dict; }
