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
struct table;
struct rule;

class infer_types {
public:
	// TODO: rework this, fwd refs just a temp solution to separate things a bit
	tables& rtables;
	std::map<multi_arg, std::set<alt_arg>> minvtyps;
	std::map<alt_arg, multi_arg> mtyps;
	// enumerates alts as they come, initially local, it needs to be here
	// we need to support multiple progs and transform/after
	std::map<ntable, size_t> altids4types;
	// this is is auto typed info for pre-processing 
	std::map<tbl_alt, alt> altstyped;
	// all bodies related to a table or rule (across alt-s)
	std::map<ntable, std::set<tbl_alt>> tblbodies;
	// maps tbl to rules
	std::map<ntable, std::set<size_t>> tblrules;
	// this is the real alts type info, used for post-processing e.g. addbit
	std::map<tbl_alt, alt*> altsmap;
	// maps types (pre) ordering to (post) rules ordering (sorting is different)
	std::map<tbl_alt, tbl_alt> altordermap;

	infer_types(tables& tables_);

	// type inference related
	bool get_root_type(const alt_arg& type, multi_arg& root) const;
	multi_arg get_root_type(const multi_arg& type) const;
	multi_arg get_fix_root_type(const multi_arg& type);
	bool map_type(multi_arg from, multi_arg to);
	void map_type(alt_arg from, multi_arg to);
	//void map_type(multi_arg to);
	void propagate_types();
	void get_types(const flat_prog& p);

private:
	struct alt_info {
		ntable tab = -1;
		std::map<int_t, vm_arg> m, mh;
		argtypes types;
		size_t varslen;
		int_t altid;
		bool headerOnly;
		alt_info(
			ntable tab, const argtypes& types, int_t altid, bool headerOnly) :
			tab(tab), types(types), varslen(0), altid(altid), 
			headerOnly(headerOnly) {}
	};

	void propagate_types(const multi_arg& intype);
	void get_alt_types(const term& h, size_t altid);
	void get_alt_types(const term& h, const term_set& al, size_t altid);
	void get_prog_types(const flat_prog& p);
	void get_header_types(
		multi_arg targ, int_t val, const arg_type& type, alt_info& info);
	void get_term_types(
		const term& t, multi_arg targ, int_t val, const arg_type& type,
		bitsmeta& bm, size_t tnums, alt_info& info);
};

#endif // __INFER_TYPES_H__