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
#ifndef __BITSMETA_H__
#define __BITSMETA_H__
#include <map>
#include <vector>
#include "defs.h"
#include "types.h"
#include "bdd.h"

class dict_t;

// D: TODO: a struct that enables table/alt to share data around.
// maybe do this by making pos and methods be part of alt/table, or similar
struct bitsmeta {
	// types.size() is always set at args (or table.len) in or right after .ctor
	argtypes types;
	uints vargs, vbits;
	size_t nterms = 0; // D: # of terms/types processed so far.
	size_t args_bits = 0; // like args * bits (just now variable sum)

	// cache
	std::map<size_t, size_t> mleftbits;
	size_t maxbits;
	std::map<size_t, std::map<size_t, size_t>> mleftargs;
	// this is reset on any bits / type change, will trigger tbl init_bits/reset
	bool bitsfixed = false;
	bool hasmultivals = false;
	static bool BITS_FROM_LEFT;

	bitsmeta() {}
	bitsmeta(size_t len) 
		: types(len), vargs(len), nterms{0}, args_bits{0} {
		for (size_t i = 0; i != len; ++i) vargs[i] = i; // native ordering
	}
	/* 
	sort of a copy .ctor w/ bits changed (for one arg) - supports add_bit 
	note: we shouldn't throw in ctor, just temporary while dev
	*/
	bitsmeta(const bitsmeta& src, multi_arg arg, size_t nbits = 1)
		: bitsmeta(src.types.size()) {
		DBG(assert(src.types.size() > 0);); // don't call this if empty
		if (src.types.empty()) throw 0;
		//DBG(assert(nbits == 1););
		//if (nbits != 1) throw 0;
		types = src.types;
		vargs = src.vargs;
		++nterms; // set init 'flag'
		// TODO: check if this makes sense (e.g. if it's CHR it has to be 8)
		// for the moment we can only addbits to primitives (maybe more later)
		arg_type& type = types[arg.arg][arg];
		if (!type.isPrimitive()) throw 0;
		// TODO: set_bitness
		type.primitive.bitness += nbits; // add bits... //++
		init_cache();
		// Only this (add_bit_perm/add_bit) & tables::init_bits will reset vbits
		init_bits();
	}

	int_t get_chars(size_t arg) const {
		return types[arg].get_chars();
	}
	int_t get_syms(size_t arg, size_t nsyms = 0) const {
		return types[arg].get_syms(nsyms);
	}
	size_t get_args() const { return types.size(); }
	
	size_t get_bits(size_t arg) const {
		return types[arg].get_bits();
	}
	//base_type get_type(size_t arg) const {
	//	return types[arg].get_type();
	//}
	//size_t get_bits(size_t arg, size_t subarg) const {
	//	return types[arg].get_bits(subarg);
	//}
	//base_type get_type(size_t arg, size_t subarg) const {
	//	return types[arg].get_type(subarg);
	//}
	/*
	 check if bits changed, any propagate_type on new prog may do this (etc.)
	 - once fixed, any added bits (or args??) have to be permuted (add_bit)
	 - we don't care during propagate_types (map/sync), check at this end (this)
	*/
	bool bits_changed() const {
		if (!bitsfixed) return false; // only fixed bits of interest
		if (vbits.empty()) return false;
		if (vbits.size() != types.size()) return true; // is this possible?
		for (size_t i = 0; i != types.size(); ++i)
			if (vbits[vargs[i]] != types[vargs[i]].get_bits()) {
				// only increase in bits is allowed (and enforced, just recheck)
				DBG(assert(vbits[vargs[i]] < types[vargs[i]].get_bits()););
				return true;
			}
		return false;
	}

	void init_bits();
	void init_cache();
	void init(const dict_t& dict);
	static void init_type(primitive_type& type, const dict_t& dict);

	static bool sync_types(
		argtypes& ltypes, const argtypes& rtypes, size_t larg, size_t rarg);
	static bool sync_types(
		argtypes& ltypes, multi_arg l, const argtypes& rtypes, multi_arg r);
	static bool sync_types(argtypes& ltypes, multi_arg l, const arg_type& r);
	static bool sync_types(arg_type& l, const arg_type& r);
	static bool sync_types(primitive_type& l, const primitive_type& r);

	static bool sync_types(
		argtypes& ltypes, multi_arg l, argtypes& rtypes, multi_arg r);
	static bool sync_types(
		argtypes& ltypes, multi_arg l, argtypes& rtypes, multi_arg r,
		bool& lchng, bool& rchng);
	static bool sync_types(argtypes& ltypes, multi_arg l, arg_type& r);
	static bool sync_types(
		argtypes& ltypes, multi_arg l, arg_type& r, bool& lchng, bool& rchng);
	static bool sync_types(arg_type& l, arg_type& r);
	static bool sync_types(arg_type& l, arg_type& r, bool& lchng, bool& rchng);
	static bool sync_types(
		primitive_type& l, primitive_type& r, bool& lchanged, bool& rchanged);

	static bool sync_types(argtypes& ltypes, argtypes& rtypes);
	static bool sync_types(
		argtypes& ltypes, argtypes& rtypes, bool& lchng, bool& rchng);
	bool sync_types(argtypes& rtypes);
	static bool sync_types(bitsmeta& lbits, argtypes& rtypes);
	//static bool sync_types(bitsmeta& l, term& t);
	static bool sync_types(bitsmeta& lbits, bitsmeta& rbits);
	static bool update_type(arg_type& type, const arg_type& other);
	static bool update_type(primitive_type& type, const primitive_type& other);
	void update_types(const argtypes& vtypes);
	bool set_args(const argtypes& vtypes, bool hasmultivals_ = false);
	// BSR op equivalent
	inline static size_t BitScanR(int_t num, size_t min_bits = 0) {
		// D: could num be < 0 (in the future?)
		DBG(assert(num >= 0););
		// D: what about just '0'? bits is 0 too? also 0 vs 'null'?
		if (num == 0) num = 1; // just to force one bit at least. // n=!n?1:n;
		if (num < 1 << min_bits) return min_bits;
		size_t bits;
		for (bits = 0; num > 0; num >>= 1) ++bits;
		return bits;
	}

	/*
	This is the ordered variable-bits pos
	- mleftargs - a map/cache of positions
	- vargs - vector of arg-s ordered (has to contain all args, no duplicates)
	*/
	size_t pos(size_t bit, size_t arg, size_t) const { // size_t args
		const std::map<size_t, size_t>& mpos = mleftargs.at(bit);
		return mpos.at(arg); // vargs[arg]

		// D: alternative, keep it for now.
		//DBG(assert(args == types.size()););
		//DBG(assert(bit < types[arg].bitness && arg < args););
		//size_t bits = types[arg].bitness;
		//DBG(assert(bit < bits && arg < args););
		//// lsum - sum of all the bits 'on the left' (same for all bit-s)
		//size_t lsum = mleftbits.at(arg);
		//// doubled consts fix: reverse bits, ie make it from-left (as consts)
		//return lsum + bit;
		////return lsum + (bits - bit - 1); // bit; // 
	}

	//DBG(assert(b < bits););
	// doubled consts fix: make it again from-left (consts the same as pos)
	/* this is bit mapping for consts basically */
	static inline size_t bit(size_t b, size_t bits) { 
		return BITS_FROM_LEFT ? b : (bits - b - 1);
	}

	/*
	- bit - bit from the right
	- arg - argument order #
	- args - # of arguments
	- val - const value to bit compare
	*/
	inline spbdd_handle from_bit(size_t bit, size_t arg, size_t args,
		int_t val) const {
		return ::from_bit(pos(bit, arg, args), val & (1 << bit));
	}

	inline spbdd_handle from_bit_re(size_t b, size_t bits, size_t arg, 
		size_t args, int_t val) const {
		//size_t b = bits - b - 1;
		return ::from_bit(pos(b, arg, args), val & (1 << bit(b,bits)));
		//return ::from_bit(pos(bit, arg, args), val & (1 << b));
	}

	/*
	This is the ordered variable-bits pos
	(it's static atm but we should make this part of alt or table)
	*/
	static size_t pos(size_t bit, size_t arg, size_t args, const bitsmeta& bm) {
		return bm.pos(bit, arg, args);
	}

	// inline not worth much anyways
	inline static spbdd_handle from_bit(size_t bit, size_t arg, size_t args,
		int_t val, const bitsmeta& bm) {
		return ::from_bit(bm.pos(bit, arg, args), val & (1 << bit));
	}
};

typedef const bitsmeta& cr_bitsmeta;
typedef const bitsmeta c_bitsmeta;

struct perminfo {
	bitsmeta bm;
	uints perm;
};

struct bits_perm {
	//bitsmeta bm;
	ntable tab;
	multi_arg arg; // size_t arg;
	size_t args;
	perminfo perm;
	size_t nbits;
};

#endif // __BITSMETA_H__