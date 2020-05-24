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
#ifndef __ADDBITS_H__
#define __ADDBITS_H__
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

class AddBits {
public:
	AddBits(tables& tbls) : rtables(tbls) {}

	void clear();
	void permute_type(
		const multi_arg& intype, size_t nbits = 1, bool bitsready = false);

private:
	inline void init_target(const arg_type& type, bool bitsready, size_t nbits){
		target = calc_target(type, bitsready, nbits);
	}
	inline static primitive_type calc_target(
		const arg_type& type, bool bitsready, size_t nbits)
	{
		if (!type.isPrimitive()) throw 0;
		// for Compound-s we need one more param (subarg), and to rework addbits
		size_t oldbits = type.primitive.bitness;
		return { type.primitive.type, bitsready ? oldbits : oldbits + nbits };
	}

	#ifdef DEBUG
	inline void check_bits(
		const arg_type& type, bool bitsready = true, size_t nbits = 0) {
		check_bits(type, target, bitsready, nbits);
	}
	inline static void check_bits(
		const arg_type& type, primitive_type target, 
		bool bitsready = true, size_t nbits = 0)
	{
		if (!type.isPrimitive()) throw 0;
		if (bitsready)
			assert(type.primitive.bitness == target.bitness);
		else
			assert(type.primitive.bitness + nbits == target.bitness);
		assert(type.primitive.type == target.type);
	}
	#endif

	alt* get_alt(const tbl_alt& talt) const;
	bits_perm permute_table(const multi_arg& targ, size_t nbits, bool bitsready);
	bool permute_bodies(const bits_perm& p, alt& a);

	static xperm permex_add_bit(const std::map<multi_arg, int_t>& poss,
								const bitsmeta& bm, const bitsmeta& abm);
	
	static perminfo add_bit_perm(const bitsmeta& bm, 
		multi_arg arg, size_t args, size_t nbits, bool bitsready = false);
	static perminfo add_bit_perm(const bitsmeta& oldbm, const bitsmeta& newbm,
		multi_arg arg, size_t args, size_t nbits);
	static spbdd_handle add_bit(spbdd_handle h,
		const perminfo& perm, multi_arg arg, size_t args, size_t nbits);
	static spbdd_handle add_bit(spbdd_handle h, const bits_perm& p) {
		return add_bit(h, p.perm, p.arg, p.args, p.nbits);
	}

	tables& rtables;

	std::set<multi_arg> rdone;
	std::map<multi_arg, perminfo> tblargperms;
	std::map<alt_arg, perminfo> altperms;
	std::map<std::pair<alt*, size_t>, alt_arg> altdone;
	std::set<std::pair<multi_arg, alt*>> bodydone;

	primitive_type target;
};

#endif // __ADDBITS_H__