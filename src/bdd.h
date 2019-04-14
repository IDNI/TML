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
#define from_bit(x, v) ((v)?bdd::add((x)+1,T,F):bdd::add((x)+1,F,T))
#define from_eq(x, y) ((x)<(y) ? bdd::add(x+1,from_bit(y,1),from_bit(y,0))\
			: bdd::add(y+1, from_bit(x,1), from_bit(x,0)))
class bdd;
struct _bdd;
typedef std::shared_ptr<bdd> spbdd;
template<> struct std::hash<_bdd> { size_t operator()(const _bdd& n) const; };
extern spbdd T, F;
struct _bdd {
	size_t v;
	bdd *h, *l;
	_bdd(const bdd& n);
	_bdd(size_t v, bdd *h, bdd *l) : v(v), h(h), l(l) {}
	bool operator==(const _bdd& n) const;
};

class bdd {
	friend struct _bdd;
	static std::unordered_map<_bdd, std::weak_ptr<bdd>> M; //bdd to its index
	size_t var;
	spbdd hi, lo;
public:
	bdd(size_t var, spbdd hi, spbdd lo) : var(var), hi(hi), lo(lo) {}
	size_t v() const { return var; }
	const spbdd h() const { return hi; }
	const spbdd l() const { return lo; }
	bool leaf() const { return var == 0 || var == (size_t)-1; }
	bool trueleaf() const { return var; }
	bool operator==(const bdd& n) const {
		return var == n.var && hi == n.hi && lo == n.lo;
	}
	static void bdd_init() {
		T = bdd::ntrue(), F = bdd::nfalse();
		bdd::M.emplace(*T, T), bdd::M.emplace(*F, F);
	}
	static spbdd ntrue() {
		return std::make_shared<bdd>((size_t)-1, nullptr, nullptr);
	}
	static spbdd nfalse() {
		return std::make_shared<bdd>(0, nullptr, nullptr);
	}
	static spbdd add(size_t _v, spbdd _h, spbdd _l) {
		bddl = true;
		if (_h == _l) return _l;
		DBG(assert(_h&&_l);)
		DBG(if (!_h->leaf()) assert(_v < _h->v());)
		DBG(if (!_l->leaf()) assert(_v < _l->v());)
		auto it = M.find(_bdd(_v,_h.get(),_l.get()));
		if (it == M.end()) {
			auto r = std::make_shared<bdd>(_v,_h,_l);
			return M.emplace(_bdd(_v,_h.get(),_l.get()), std::weak_ptr<bdd>(r)), r;
		}
		return it->second.lock();
	}
	static size_t size() { return M.size(); }
	static bool bddl;
	~bdd() { M.erase(*this); }
};
typedef std::vector<spbdd> bdds;
//extern unordered_map<bdd, shared_ptr<bdd>> M; // bdd to its index
//const size_t F = 0, T = 1;
//extern std::vector<bdd> V;

void bdd_init();
//spbdd bdd_add(const bdd& n); //create new bdd bdd,standard implementation
vbools allsat(spbdd x, size_t nv);
vbools allsat(spbdd x, size_t bits, size_t args);
//spbdd from_bit(size_t x ,bool v);
spbdd operator||(spbdd x, spbdd y);
spbdd operator/(spbdd x, const bools&); // existential quantificatoin
spbdd operator&&(spbdd x, spbdd y);
#define bdd_impl(x, y) ((y) || (T%x))
spbdd bdd_and_many(bdds v);
spbdd bdd_or_many(bdds v);
spbdd bdd_expand(spbdd x, size_t args1, size_t args2, size_t bits);
spbdd bdd_subterm(spbdd x, size_t from, size_t to, size_t args1, size_t args2,
	size_t bits);
spbdd bdd_deltail(spbdd x, size_t h);
spbdd bdd_deltail(spbdd x, size_t args1, size_t args2, size_t bits);
spbdd bdd_and_deltail(spbdd x, size_t y, size_t h);
spbdd operator%(spbdd x, spbdd y); // and not
spbdd bdd_ite(size_t v, spbdd t, spbdd e);
spbdd operator^(spbdd x, const sizes&); // overlapping rename (permute)
size_t bdd_count(size_t x, size_t nvars);
bool bdd_onesat(spbdd x, size_t nvars, bools& r);
//size_t from_eq(size_t x, size_t y);
spbdd from_int(size_t x, size_t bits, size_t arg, size_t args);
//matrix from_bits(size_t x, size_t bits, size_t ar);
//struct term one_from_bits(size_t x, size_t bits, size_t ar);
std::wostream& operator<<(std::wostream& os, const bools& x);
std::wostream& operator<<(std::wostream& os, const vbools& x);
std::wostream& bdd_out(std::wostream& os, const bdd& n);// print bdd in ?: syntax
std::wostream& bdd_out(std::wostream& os, spbdd n);
void memos_clear();

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
#endif
