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
#ifndef __UPDATES_FACTTORY_H__
#define __UPDATES_FACTORY_H__

#include "builtins.h"
#include "dict.h"
#include "tables.h"

namespace idni { 
struct updates_factory {

	updates updts;
	dict_t& dict;

	bool add_updates() { /* add symbols */ }
	updates get();
};
} // namespace idni
#endif __UPDATES_FACTORY_H__