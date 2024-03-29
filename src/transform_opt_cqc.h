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

#ifndef __TRANSFORM_OPT_Z3_H__
#define __TRANSFORM_OPT_Z3_H__

#include "transform_opt_common.h"

flat_prog minimize_rules(flat_prog const &p);
flat_rule minimize_rule(flat_rule const &r, flat_prog const &p);
bool rule_contains(flat_rule const &r1, flat_rule const &r2, flat_prog const &p);

#endif // __TRANSFORM_OPT_Z3_H__