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
#ifndef __ITERBDDS_H__
#define __ITERBDDS_H__
#include <map>
#include <vector>
#include "bdd.h"
#include "term.h"
#include "bitsmeta.h"
#include "dict.h"
#include "defs.h"
#include "types.h"
class tables;
struct alt;

struct tblperminfo {
	ntable tab;
	std::set<size_t> args;
	bitsmeta oldbm;
	perminfo info;
};

struct iterbdds {
	tables& rtbls;
	std::set<tbl_arg> tdone;
	std::set<tbl_arg> rdone;
	//std::set<alt_arg> altdone;
	std::map<tbl_arg, perminfo> tblargperms;
	std::map<ntable, tblperminfo> tblperms;
	std::map<alt_arg, perminfo> altperms;
	std::map<std::pair<alt*, size_t>, alt_arg> altdone;
	std::set<std::pair<tbl_arg, alt*>> bodydone;
	//std::vector<bits_perm> vperms;

	iterbdds(tables& tbls) :rtbls(tbls) {}

	void clear() {
		//vperms.clear(); // clear any previous that are applied
		altperms.clear();
		tblargperms.clear();
		tblperms.clear();
		altdone.clear();
		rdone.clear();
		tdone.clear();
		bodydone.clear();
	}

	alt* get_alt(const tbl_alt& talt) const;
	void permute_type(const tbl_arg& intype, size_t addbits = 1);
	bool permute_table(ntable tab, size_t arg);
	bool permute_table(const tbl_arg& targ, size_t bits, base_type type);
	bool permute_table(ntable tab, size_t arg, size_t bits, base_type type) {
		return permute_table({ tab, arg }, bits, type);
	}
	// const bits_perm& altperm
	bool permute_bodies(const tbl_arg& targ, const bits_perm& p, alt& a, 
		size_t bits, base_type type);
	//bool permute_alt(ntable tab, size_t arg, size_t n, alt& a, 
	//	size_t bits, base_type type);
	//bool permute_all();
};

#endif // __ITERBDDS_H__