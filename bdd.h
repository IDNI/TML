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
#include "defs.h"
#include "term.h"

//bdd node is a triple: varid,1-node-id,0-node-id
typedef std::array<size_t, 3> node;
const size_t F = 0, T = 1;
extern std::vector<node> V;

void bdd_init();
size_t bdd_add(const node& n); //create new bdd node,standard implementation
std::vector<std::vector<bool>> allsat(size_t x, size_t nv);
void allsat(size_t x, size_t nvars, std::function<void(const bools&)> f);
size_t from_bit(size_t x ,bool v);
size_t bdd_or(size_t x, size_t y);
size_t bdd_ex(size_t x, const bools&);
size_t bdd_and(size_t x, size_t y);
size_t bdd_and_many(sizes v);
size_t bdd_expand(size_t x, size_t args1, size_t args2, size_t bits);
size_t bdd_subterm(size_t x, size_t from, size_t to, size_t args1, size_t args2,
	size_t bits);
size_t bdd_deltail(size_t x, size_t h);
size_t bdd_deltail(size_t x, size_t args1, size_t args2, size_t bits);
size_t bdd_and_deltail(size_t x, size_t y, size_t h);
//size_t bdd_and_ex(size_t x, size_t y, const bools&);
size_t bdd_and_not(size_t x, size_t y);
//size_t bdd_and_not_ex(size_t x, size_t y, const bools&);
size_t bdd_ite(size_t v, size_t t, size_t e);
size_t bdd_permute(size_t x, const sizes&); //overlapping rename
size_t bdd_count(size_t x, size_t nvars);
bool bdd_onesat(size_t x, size_t nvars, bools& r);
size_t from_eq(size_t x, size_t y);
size_t from_int(size_t x, size_t bits, size_t arg, size_t args);
//size_t bdd_pad(size_t x, size_t ar1, size_t ar2, size_t pad, size_t bits);
//size_t bdd_rebit(size_t x, size_t prev, size_t curr, size_t pnvars);
//void from_range(size_t max, size_t bits, size_t offset, size_t &r);
//void from_range(size_t max, size_t bits, size_t offset, std::set<int_t> ex,
//	size_t &r);
matrix from_bits(size_t x, size_t bits, size_t ar);
term one_from_bits(size_t x, size_t bits, size_t ar);
std::wostream& operator<<(std::wostream& os, const bools& x);
std::wostream& operator<<(std::wostream& os, const vbools& x);

#define from_int_and(x, y, arg, args, r) r = bdd_and(r, from_int(x,y,arg,args))
#define getnode(x) V[x]
#define leaf(x) (((x) == T) || ((x) == F))
#define nleaf(x) (!((x)[0]))
#define trueleaf(x) ((x) == T)
#define ntrueleaf(x) (nleaf(x) && (x)[1])
#define from_bit(x, v) (bdd_add((v) ? node{{(x)+1,T,F}} : node{{(x)+1,F,T}}))
#define from_eq(x, y) ((x) < (y) ? bdd_add({{x+1,from_bit(y,1),from_bit(y,0)}})\
			: bdd_add({{y+1, from_bit(x,1), from_bit(x,0)}}))
#endif
