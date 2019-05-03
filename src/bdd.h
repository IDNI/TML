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
#ifndef __BDD_H__
#define __BDD_H__
#include <vector>
#include <unordered_map>
#include <array>
#include <functional>
#include <numeric>
#include <memory>
#include "defs.h"

#define leafvar(x) (!(x) || ((x) == (size_t)-1))
class bdd;
struct key;
typedef std::shared_ptr<bdd> spbdd;
typedef std::weak_ptr<bdd> wpbdd;
extern spbdd T, F;

class bdd {
	struct key {
		const size_t v;
		const bdd *h, *l;
		const size_t hash;
		key(size_t v, const bdd *h, const bdd *l) :v(v), h(h), l(l),
			hash(v+(((size_t)h)<<BDD_HASH_H_SHIFT)+
				(((size_t)l)<<BDD_HASH_L_SHIFT)) {}
		bool operator==(const key& n) const {
			return v == n.v && h == n.h && l == n.l;
		}
	};
	struct keyhash { size_t operator()(const key&k) const {return k.hash;}};
	static std::unordered_map<key, std::weak_ptr<bdd>, keyhash> M;
	const size_t var;
	spbdd hi, lo;
	bdd(size_t var, spbdd hi, spbdd lo) : var(var), hi(hi), lo(lo) {
		DBG(if (var && var != (size_t)-1) assert(hi&&lo);)
	}
	friend spbdd;
public:
	inline const size_t& v() const { return var; }
	inline const spbdd& h() const { return hi; }
	inline const spbdd& l() const { return lo; }
	inline bool leaf() const { return leafvar(var); }
	inline bool trueleaf() const { return var; }
	inline bool operator==(const bdd& n) const {
		return var == n.var && hi == n.hi && lo == n.lo;
	}
	static void init() {
		T = spbdd(new bdd((size_t)-1, nullptr, nullptr)),
		F = spbdd(new bdd(0, nullptr, nullptr)),
		T->hi = T->lo = T, F->hi = F->lo = F,
		M.emplace(key(T->var, T->hi.get(), T->lo.get()), T),
		M.emplace(key(F->var, F->hi.get(), F->lo.get()), F);
	}
	static spbdd from_bit(size_t x, bool v) {
		return v ? add(x + 1, T, F) : add(x + 1, F, T);
	}
	static spbdd from_eq(size_t x, size_t y) {
		return x < y ? add(x + 1, from_bit(y, true), from_bit(y, false))
			: add(y + 1, from_bit(x, true), from_bit(x, false));
	}
	static spbdd add(size_t v, spbdd h, spbdd l) {
		if (h == l) return l;
		DBG(assert(h&&l);)
		DBG(if (!h->leaf()) assert(v < h->v());)
		DBG(if (!l->leaf()) assert(v < l->v());)
		auto it = M.find(key(v, h.get(), l.get()));
		if (it != M.end()) return it->second.lock();
		spbdd r = spbdd(new bdd(v, h, l));
		return M.emplace(key(v, h.get(), l.get()), wpbdd(r)), r;
	}
	static spbdd get(const bdd* b) {
		return M[key(b->var, b->hi.get(), b->lo.get())].lock();
	}
#ifdef DEEPDEBUG
	static void validate(spbdd x, spbdd y) {
		key k1(x->v(), x->h().get(), x->l().get());
		key k2(y->v(), y->h().get(), y->l().get());
		auto it = M.find(k1);
		auto jt = M.find(k2);
		assert(it->second.lock() == jt->second.lock());
		assert(it == jt);
	}
	static bool _bddcmp(spbdd x, spbdd y) {
		if (x == y) return true;
		if (x->leaf() != y->leaf()) return false;
		if (x->leaf()) return x->trueleaf() == y->trueleaf();
		if (x->v() != y->v()) return false;
		return _bddcmp(x->l(), y->l()) && _bddcmp(x->h(), y->h());
	}
	static void validate() {
		auto bddcmp = [](spbdd x, spbdd y) {
			assert((x == y) == (_bddcmp(x, y)));
			return x == y;
		};
		for (auto x : M)
			for (auto y : M)
				if (!(x.first == y.first))
					assert(!bddcmp(
					x.second.lock(), y.second.lock()));
		for (auto x : M)
			assert(x.first.v == x.second.lock()->var),
			assert(x.first.h == x.second.lock()->h().get()),
			assert(x.first.l == x.second.lock()->l().get());
	}
#else
	static void validate() {}
	static bool _bddcmp(spbdd x, spbdd y) { return x == y; }
#endif
	static size_t size() { return M.size(); }
	static bool onexit;
	static size_t gc;
	~bdd() { if (onexit) return; M.erase(key(var, hi.get(), lo.get())); ++gc; }
	static void clear();
};
typedef std::vector<spbdd> bdds;

struct onexit {
	~onexit();
};
extern onexit _onexit;

void bdd_init();
vbools allsat(spbdd x, size_t nvars);
vbools allsat(spbdd x, size_t bits, size_t args);
spbdd operator||(const spbdd& x, const spbdd& y);
spbdd operator/(const spbdd& x, const bools&); // existential quantification
spbdd operator&&(const spbdd& x, const spbdd& y);
spbdd operator%(const spbdd& x, const spbdd& y); // and not
spbdd operator^(const spbdd& x, const sizes&); // overlapping rename (permute)
spbdd bdd_permute_ex(const spbdd& x, const bools& b, const sizes& m);
#define bdd_impl(x, y) ((y) || (T%x))
spbdd bdd_and_many(bdds v);
spbdd bdd_or_many(bdds v);
spbdd bdd_expand(spbdd x, size_t args1, size_t args2, size_t bits);
std::pair<bools, sizes> bdd_subterm(size_t from, size_t to,
	size_t args1, size_t args2, size_t bits);
spbdd bdd_subterm(spbdd x, const bools& b, const sizes& perm, size_t from,
	size_t to, size_t args1);
spbdd bdd_subterm(spbdd x, size_t from, size_t to, size_t args1, size_t args2,
	size_t bits);
//spbdd bdd_deltail(spbdd x, size_t args1, size_t args2, size_t bits);
spbdd bdd_ite(size_t v, spbdd t, spbdd e);
size_t bdd_count(size_t x, size_t nvars);
bool bdd_onesat(spbdd x, size_t nvars, bools& r);
spbdd from_int(size_t x, size_t bits, size_t arg, size_t args);
size_t bdd_nvars(spbdd x);
std::wostream& operator<<(std::wostream& os, const bools& x);
std::wostream& operator<<(std::wostream& os, const vbools& x);
std::wostream& operator<<(std::wostream& os, spbdd x);
std::wostream& bdd_out_ite(std::wostream& os, spbdd x, size_t dep = 0);
void memos_clear();
DBG(void assert_nvars(spbdd x, size_t vars);)

#define from_int_and(x, y, arg, args, r) (r = (r) && from_int(x,y,arg,args))

class allsat_cb {
public:
	typedef std::function<void(const bools&, spbdd)> callback;
	allsat_cb(spbdd r, size_t nvars, callback f) :
		r(r), nvars(nvars), f(f), p(nvars) {}
	void operator()() { sat(r); }
private:
	spbdd r;
	const size_t nvars;
	size_t v = 1;
	callback f;
	bools p;
	void sat(spbdd x);
};

template<typename X, size_t Y> struct array_hash {
	size_t operator()(const std::array<X, Y>& m) const {
		return std::accumulate(m.begin(), m.end(), 0);
	}
};

int_t onmemo(int_t n = 1);
#endif
