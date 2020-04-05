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
#include <algorithm>
#include <list>
#include "bitsmeta.h"
#include "dict.h"
#include "input.h"
//#include "term.h"
//#include "output.h"
#include "err.h"
using namespace std;

// this is going away anyways, copy it for now, who cares
//#define mkchr(x) ((((int_t)x)<<2)|1)
//#define mknum(x) ((((int_t)x)<<2)|2)
//#define mksym(x) (int_t(x)<<2)
//#define un_mknum(x) (int_t(x)>>2)
#define mkchr(x) (int_t(x))
#define mknum(x) (int_t(x))
#define mksym(x) (int_t(x))
#define un_mknum(x) (int_t(x))

bool bitsmeta::BITS_FROM_LEFT = false;

/* prepare bits, bitness, caches if any */
void bitsmeta::init(const dict_t& dict) {
	// vargs should be set before entering, or rerun this on ordering change.
	if (types.empty()) return;
	mleftbits.clear();
	size_t lsum = 0, args = types.size(), maxb = 0;
	mleftbits[vargs[0]] = lsum;
	for (size_t i = 0; i != types.size(); ++i) {
		//arg_type& type = types[i]; // this is a bug
		arg_type& type = types[vargs[i]];
		// just temp, update all int, chr, str bits w/ 2 extra bits (as before).
		switch (type.type) {
			case base_type::STR:
				// D: Q: TODO: how to set up individual arg's sym universe?
				// always init for STR/CHR or not? may alt universe size differ?
				if (type.bitness == 0) {
					type.bitness = BitScanR(dict.nsyms()); // nsyms-1? I guess
					// add extra because we haven't handled syms properly yet
					// i.e. we have 'shared dict universe' for all sym/str args
					//type.bitness += 2; // ...will be removed
				}
				break;
			case base_type::CHR:
				// it's always 8, always init (or if correct it's 0)
				if (type.bitness == 0) {
					type.bitness = 8;
					// there's a bug with tight bits (dycks example), safe bits
					//type.bitness += 2; // ...will be removed
				}
				break;
			case base_type::INT: 
				if (type.bitness == 0) {
					// calc bitness for ints (we just have nums at this point).
					type.bitness = BitScanR(nums[i]); // un_mknum(args[i])
					// there's a bug with tight bits (dycks example), safe bits
					//type.bitness += 2; // ...will be removed
				}
				break;
			case base_type::NONE:
				type.bitness = 1; // 8;
				type.bitness += 2; // ...will be removed
			default: ;
		}
		//DBG(assert(type.bitness < 100););

		//if (vargs[i] == arg) break;
		if (i != args-1) {
			lsum += types[vargs[i]].bitness;
			mleftbits[vargs[i+1]] = lsum;
		}
		// vargs is redundant here as it's an aggregate, maxb/vbits will be same
		maxb = max(maxb, types[vargs[i]].bitness);
		//vbits[vargs[i]] = types[vargs[i]].bitness;
	}
	args_bits = mleftbits.at(vargs[args-1]) + types[vargs[args-1]].bitness;
	maxbits = maxb;

	size_t argsum = 0;
	if (maxbits == 0)
		return;
	mleftargs.clear();
	for (int_t bit = maxbits-1; bit >= 0; --bit) {
		map<size_t, size_t>& mpos = mleftargs[bit];
		for (size_t arg = 0; arg != types.size(); ++arg)
			if (types[vargs[arg]].bitness > size_t(bit))
				mpos[vargs[arg]] = argsum++;
	}
	DBG(assert(argsum == args_bits););
}

/* this's probably not necessary, just do init() when done w/ changes */
void bitsmeta::init_cache() {
	DBG(assert(!types.empty()););
	size_t args = types.size(), lsum = 0, maxb = 0, argsum = 0;
	mleftargs.clear();
	mleftbits.clear();
	mleftbits[vargs[0]] = lsum;
	// recalculate everything...
	for (size_t i = 0; i < args-1; ++i) { // process [0..args-2] (skip last)
		lsum += types[vargs[i]].bitness;
		mleftbits[vargs[i+1]] = lsum;
		maxb = std::max(maxb, types[vargs[i]].bitness);
		//vbits[vargs[i]] = types[vargs[i]].bitness; // wrong, missing args-1
	}
	args_bits = mleftbits.at(vargs[args-1]) + types[vargs[args-1]].bitness;
	maxbits = std::max(maxb, types[vargs[args-1]].bitness);
	DBG(assert(maxbits != 0);); // if (maxbits == 0) return;
	for (int_t bit = maxbits - 1; bit >= 0; --bit) {
		map<size_t, size_t>& mpos = mleftargs[bit];
		for (size_t arg = 0; arg != types.size(); ++arg)
			if (types[vargs[arg]].bitness > size_t(bit))
				mpos[vargs[arg]] = argsum++;
	}
	DBG(assert(argsum == args_bits););
}

/* 
 this effectively 'cements' the bits, any later on changes result in add_bits
 (it's done on tbl init/init_bits or later on permute_type/add_bit/add_bit_perm)
*/
void bitsmeta::init_bits() {
	vbits = uints(types.size());
	// TODO: easier is just vbits.push_back(types[i].bitness);
	for (size_t i = 0; i != types.size(); ++i)
		// vargs is redundant here as it's an aggregate, maxb/vbits will be same
		vbits[vargs[i]] = types[vargs[i]].bitness;
	bitsfixed = true;
}

bool bitsmeta::set_args(
	const ints& args, const argtypes& vtypes, const ints& vnums) {
	if (vtypes.empty()) return false;
	DBG(assert(vtypes.size() > 0);); // don't call this if nothing to do
	DBG(assert(args.size() == vtypes.size()););
	DBG(assert(args.size() == vnums.size()););
	// we're empty initialized already (to table len), so sizes need to match
	DBG(assert(types.size() == vtypes.size()););
	// !nterms meaning we have no previous types / bits data (size's always >0)
	if (!nterms) { // types.size() == 0)
		types = vtypes;
		nums = vnums;
	} else {
		for (size_t i = 0; i != types.size(); ++i) {
			// D: TODO: use update_types instead but we need some testing
			//update_types(vtypes, vnums);
			arg_type& type = types[i];
			const arg_type& newtype = vtypes[i];
			if (newtype.type == base_type::NONE) continue; // not set, skip
			if (type.type == base_type::NONE) 
				type = newtype; // first init...
			if (type.type != newtype.type) 
				parse_error(err_type, L""); //lexeme?
			if (type.type == base_type::INT) 
				nums[i] = max(nums[i], vnums[i]); // no need if NONE but cheap
			// we may not need this, it's 0 except for alt's (inheriting, once)
			if (newtype.bitness > type.bitness) 
				type.bitness = newtype.bitness; 
			//if (type.type == base_type::INT) nums[i] = vnums[i];
			//if (isset && type.type == base_type::INT) // calc bitness for ints
			//	type.bitness = BitScanR(un_mknum(args[i]), type.bitness);
			//DBG(assert(type.bitness < 100););
		}
	}
	++nterms;
	return true;
}

/* 
we're init already, this is just to update table back from alt/rules 
not entirely nice but handy to sync types in between tbls, rules, alts, for now
(this is to be deprecated, not much use, just use init() on any change)
*/
void bitsmeta::update_types(const argtypes& vtypes, const ints& vnums) {
	DBG(assert(types.size() <= vtypes.size()););
	bool changed = false;
	for (size_t i = 0; i != types.size(); ++i) {
		arg_type& type = types[i];
		const arg_type& newtype = vtypes[i];
		if (newtype.type == base_type::NONE) continue; // not set, skip
		if (type.type == base_type::NONE)
			type = newtype, changed = true; // first init...
		if (type.type != newtype.type)
			parse_error(err_type, L""); //lexeme?
		if (type.type == base_type::INT && vnums[i] > nums[i])
			nums[i] = vnums[i], changed = true; //nums[i] = max(...);
		if (newtype.bitness > type.bitness)
			type.bitness = newtype.bitness, changed = true;
		//if (isset && type.type == base_type::INT) // calc bitness for ints
		//	type.bitness = BitScanR(un_mknum(args[i]), type.bitness);
		//DBG(assert(type.bitness < 100););
	}
	// this updates 'live', caches may change
	if (changed) init_cache();
}

bool bitsmeta::sync_types(argtypes& ltypes, const argtypes& rtypes, 
	ints& lnums, const ints& rnums, size_t larg, size_t rarg) {
	return sync_types(ltypes[larg], rtypes[rarg], lnums[larg], rnums[rarg]);
}

bool bitsmeta::sync_types(
	arg_type& l, const arg_type& r, int_t& lnum, const int_t& rnum) {
	bool changed = false;
	bool lnone = l.type == base_type::NONE, rnone = r.type == base_type::NONE;
	if (rnone) return false;
	else if (lnone) return l = r, true;
	if (l.type != r.type) parse_error(err_type, L"");
	if (l.type == base_type::INT && rnum > lnum)
		lnum = rnum, changed = true;
	if (r.bitness > l.bitness)
		l.bitness = r.bitness, changed = true;
	//DBG(assert(l.bitness < 100););
	//DBG(assert(r.bitness < 100););
	return changed;
}

bool bitsmeta::sync_types(arg_type& l, arg_type& r, int_t& lnum, int_t& rnum) {
	bool lchng, rchng;
	return sync_types(l, r, lnum, rnum, lchng, rchng);
}
bool bitsmeta::sync_types(arg_type& l, arg_type& r, int_t& lnum, int_t& rnum,
	bool& lchng, bool& rchng) {
	//bool changed = false;
	bool lnone = l.type == base_type::NONE, rnone = r.type == base_type::NONE;
	if (lnone && rnone) return false;
	else if (rnone) return r = l, rchng = true;
	else if (lnone) return l = r, lchng = true;
	if (l.type != r.type) parse_error(err_type, L"");
	if (l.type == base_type::INT) {
		if (rnum > lnum) 
			lnum = rnum, lchng = true;
		else if (lnum > rnum) 
			rnum = lnum, rchng = true;
	}
	if (r.bitness > l.bitness)
		l.bitness = r.bitness, lchng = true;
	else if (l.bitness > r.bitness)
		r.bitness = l.bitness, rchng = true;
	//DBG(assert(l.bitness < 100););
	//DBG(assert(r.bitness < 100););
	return lchng || rchng;
}

bool bitsmeta::sync_types(
	argtypes& ltypes, argtypes& rtypes, ints& lnums, ints& rnums) {
	bool lchng, rchng;
	return sync_types(ltypes, rtypes, lnums, rnums, lchng, rchng);
}
bool bitsmeta::sync_types(
	argtypes& ltypes, argtypes& rtypes, ints& lnums, ints& rnums,
	bool& lchng, bool& rchng) {
	DBG(assert(ltypes.size() == rtypes.size()););
	//bool lchng = false, rchng = false;
	for (size_t i = 0; i != ltypes.size(); ++i)
		sync_types(ltypes[i], rtypes[i], lnums[i], rnums[i], lchng, rchng);
	// this updates 'live', caches may change
	//if (lchng) l.init_cache();
	//if (rchng) r.init_cache();
	return lchng || rchng;
}

bool bitsmeta::sync_types(argtypes& rtypes, ints& rnums) {
	return sync_types(*this, rtypes, rnums);
}
bool bitsmeta::sync_types(bitsmeta& l, argtypes& rtypes, ints& rnums) {
	bool lchng = false, rchng = false, changed;
	changed =
		sync_types(l.types, rtypes, l.nums, rnums, lchng, rchng);
	if (lchng) l.init_cache();
	//if (rchng) r.init_cache();
	return changed; // lchng || rchng;
}

//bool bitsmeta::sync_types(bitsmeta& l, term& t) {
//	return sync_types(l, t.types, t.nums);
//}

bool bitsmeta::sync_types(bitsmeta& l, bitsmeta& r) {
	bool lchng = false, rchng = false, changed;
	changed = 
		sync_types(l.types, r.types, l.nums, r.nums, lchng, rchng);
	if (lchng) l.init_cache();
	if (rchng) r.init_cache();
	return changed; // lchng || rchng;
	//DBG(assert(l.types.size() == r.types.size()););
	//bool lchng = false, rchng = false;
	//for (size_t i = 0; i != l.types.size(); ++i)
	//	sync_types(l.types[i], r.types[i], l.nums[i], r.nums[i], lchng, rchng);
	//// this updates 'live', caches may change
	//if (lchng) l.init_cache();
	//if (rchng) r.init_cache();
	//return lchng || rchng;
}


