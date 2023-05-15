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
#include <set>

#include "ir_builder.h"
#include "term.h"

namespace idni {

typedef int int_t;
typedef int_t rel;

typedef std::set<term> clause;
typedef std::set<clause> dnf;
typedef std::vector<std::pair<term, dnf>> prog;
typedef std::set<std::pair<clause, dnf>> f_prog;

prog from_term(const term&);
prog operator&&(const prog&, const prog&);
prog operator||(const prog&, const prog&);
prog operator~(const prog&);
prog ex(const prog&, int_t v, int_t t);
prog all(const prog&, int_t v, int_t t);

f_prog unseq(const prog&);

void print_fof(prog& p, ir_builder *irb);
void to_flat_prog(term &h, ir_builder *irb, const prog& p, flat_prog &m);
void fof_init_tables(std::vector<term> &v);

} // namespace idni
