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
#include <vector>
#include <unordered_map>
#include <array>
#include "defs.h"

//bdd node is a triple: varid,1-node-id,0-node-id
typedef std::array<size_t, 3> node;
const size_t F = 0, T = 1;
extern std::vector<node> V;

void bdd_init();
size_t bdd_add(const node& n); //create new bdd node,standard implementation
std::vector<std::vector<bool>> allsat(size_t x, size_t nvars);
size_t from_bit(size_t x ,bool v);
size_t bdd_or(size_t x, size_t y);
size_t bdd_ex(size_t x, const bools&);
size_t bdd_and(size_t x, size_t y);
size_t bdd_deltail(size_t x, size_t h);
size_t bdd_and_deltail(size_t x, size_t y, size_t h);
size_t bdd_and_ex(size_t x, size_t y, const bools&);
size_t bdd_and_not(size_t x, size_t y);
size_t bdd_and_not_ex(size_t x, size_t y, const bools&);
size_t bdd_ite(size_t v, size_t t, size_t e);
size_t bdd_permute(size_t x, const std::vector<size_t>&); //overlapping rename
size_t from_eq(size_t x, size_t y);

#define getnode(x) V[x]
#define leaf(x) (((x) == T) || ((x) == F))
#define nleaf(x) (!(x)[0])
#define trueleaf(x) ((x) == T)
#define ntrueleaf(x) (nleaf(x) && (x)[1])
#define from_bit(x, v) bdd_add((v) ? node{{(x)+1,T,F}} : node{{(x)+1,F,T}})
