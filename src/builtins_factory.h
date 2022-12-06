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
#ifndef __BUILTINS_FACTTORY_H__
#define __BUILTINS_FACTORY_H__

#include "builtins.h"
#include "dict.h"
#include "tables.h"

struct builtins_factory {

	builtins bltins;
	dict_t& dict;

	builtins_factory(dict_t& dict_) : dict(dict_) {};

	builtins_factory& add_basic_builtins();
	builtins_factory& add_bdd_builtins();
	builtins_factory& add_print_builtins();
	builtins_factory& add_js_builtins();
	// TODO remove, it is an struct an the field is public
	builtins get();
};

#endif // __BUILTINS_FACTORY_H__