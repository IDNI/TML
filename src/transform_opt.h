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

#ifndef __TRANSFORM_OPT_H__
#define __TRANSFORM_OPT_H__

#include <vector>
#include <map>
#include <cmath>
#include <functional>
#include <limits>

#include "ir_builder.h"

/* Optimization methods. */

flat_prog optimize_o1(const flat_prog &fp);
flat_prog optimize_o2(const flat_prog &fp);
flat_prog optimize_o3(const flat_prog &fp);

/* Optimization plus squaring methods. */

flat_prog squaring_o1(const flat_prog &fp);
flat_prog squaring_o2(const flat_prog &fp);
flat_prog squaring_o3(const flat_prog &fp);


/*! Produces a program where executing a single step is equivalent to
 * executing two steps of the original program. This is achieved through
 * inlining where each body term is replaced by the disjunction of the
 * bodies of the relation that it refers to. For those facts not
 * computed in the previous step, it is enough to check that they were
 * derived to steps ago and were not deleted in the previous step. */

flat_prog square_program(const flat_prog &fp);

#endif // __TRANSFORM_OPT_H__