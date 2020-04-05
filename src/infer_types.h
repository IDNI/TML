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
#ifndef __INFER_TYPES_H__
#define __INFER_TYPES_H__
#include <cassert>
#include <vector>
#include <set>
#include <unordered_map>
#include <array>
#include <iostream>
#include <iomanip>
#include <cstdio>
#include <map>

#include "defs.h"
#include "types.h"
#include "term.h"

class tables;
struct alt;

struct infer_types {
	// TODO: rework this, fwd refs just a temp solution to separate things a bit
	tables& rtables;
	std::map<tbl_arg, std::set<alt_arg>> minvtyps;
	std::map<alt_arg, tbl_arg> mtyps;
	// enumerates alts as they come, initially local, it needs to be here
	// we need to support multiple progs and transform/after
	std::map<ntable, size_t> altids4types;

	// this is is auto typed info for pre-processing 
	std::map<tbl_alt, alt> altstyped;

	infer_types(tables& tables_) :rtables(tables_) {}

	// type inference related
	bool get_root_type(const alt_arg& type, tbl_arg& root) const;
	tbl_arg get_root_type(const tbl_arg& type) const;
	tbl_arg get_fix_root_type(const tbl_arg& type);
	bool map_type(tbl_arg from, tbl_arg to);
	void map_type(alt_arg from, tbl_arg to);
	//void map_type(tbl_arg to);
	void propagate_types();
	void propagate_types(const tbl_arg& intype);
	void get_alt_types(const term& h, size_t altid);
	void get_alt_types(const term& h, const term_set& al, size_t altid);
	//void get_types(const std::map<term, std::set<term_set>>& m);
	void get_prog_types(const flat_prog& p);
	void get_types(const flat_prog& p);
	//void get_types(flat_prog& p);
};

#endif // __INFER_TYPES_H__