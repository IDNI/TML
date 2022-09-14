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
#include "transform_opt_squaring.h"
#include "transform_opt_cqc.h"


/* Optimization methods polynomial in the input. */

flat_prog optimize_o1(const flat_prog &fp);
flat_prog squaring_o1(const flat_prog &fp);

/* Optimization methods polynomial in the length of the program but exponential 
 * in the size of the bodies. */

flat_prog optimize_o2(const flat_prog &fp);
flat_prog squaring_o2(const flat_prog &fp);

/* Optimization methods exponential in the length of the program and the 
 * size of the bodies. */

flat_prog squaring_o3(const flat_prog &fp);
flat_prog optimize_o3(const flat_prog &fp);

#endif // __TRANSFORM_OPT_H__