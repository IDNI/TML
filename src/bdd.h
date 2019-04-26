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

//bdd bdd is a triple: varid,1-bdd-id,0-bdd-id
//typedef std::array<size_t, 3> bdd;
#define leafvar(x) (!(x) || ((x) == (size_t)-1))
#define from_bit(x, v) ((v)?bdd::add((x)+1,T,F):bdd::add((x)+1,F,T))
#define from_eq(x, y) ((x)<(y) ? bdd::add(x+1,from_bit(y,1),from_bit(y,0))\
			: bdd::add(y+1, from_bit(x,1), from_bit(x,0)))
class bdd;
struct key;
typedef std::shared_ptr<bdd> spbdd;
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
public:
	bdd(size_t var, spbdd hi, spbdd lo) : var(var), hi(hi), lo(lo) {
		DBG(if (var && var != (size_t)-1) assert(hi&&lo);)
	}
	const size_t& v() const { return var; }
	const spbdd& h() const { return hi; }
	const spbdd& l() const { return lo; }
	bool leaf() const { return leafvar(var); }
	bool trueleaf() const { return var; }
	bool operator==(const bdd& n) const {
		return var == n.var && hi == n.hi && lo == n.lo;
	}
	static void init() {
		T = std::make_shared<bdd>((size_t)-1, nullptr, nullptr),
		F = std::make_shared<bdd>(0, nullptr, nullptr),
		T->hi = T->lo = T, F->hi = F->lo = F,
		M.emplace(key(T->var, T->hi.get(), T->lo.get()), T),
		M.emplace(key(F->var, F->hi.get(), F->lo.get()), F);
	}
	static spbdd add(size_t _v, spbdd _h, spbdd _l) {
		if (_h == _l) return _l;
		DBG(assert(_h&&_l);)
		DBG(if (!_h->leaf()) assert(_v < _h->v());)
		DBG(if (!_l->leaf()) assert(_v < _l->v());)
		auto it = M.find(key(_v, _h.get(), _l.get()));
		if (it != M.end()) return it->second.lock();
		spbdd r = std::make_shared<bdd>(_v, _h, _l);
		return 	M.emplace(key(_v, _h.get(), _l.get()),
			std::weak_ptr<bdd>(r)), r;
	}
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
spbdd operator/(spbdd x, const bools&); // existential quantification
spbdd operator&&(spbdd x, spbdd y);
spbdd operator%(spbdd x, spbdd y); // and not
spbdd operator^(spbdd x, const sizes&); // overlapping rename (permute)
spbdd bdd_permute_ex(spbdd x, const bools& b, const sizes& m);
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
std::wostream& bdd_out(std::wostream& os, bdd);// print bdd in ?: syntax
std::wostream& bdd_out(std::wostream& os, spbdd n);
void memos_clear();
DBG(void assert_nvars(spbdd x, size_t vars);)

#define from_int_and(x, y, arg, args, r) (r = (r) && from_int(x,y,arg,args))

class allsat_cb {
public:
	typedef std::function<void(const bools&)> callback;
	allsat_cb(spbdd r, size_t nvars, callback f)
		: r(r), nvars(nvars), f(f), p(nvars) {}
	void operator()() { sat(r); }
private:
	spbdd r;
	size_t nvars, v = 1;
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
