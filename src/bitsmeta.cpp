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
#include "term.h"
//#include "output.h"
#include "err.h"
using namespace std;

// this is going away anyways, copy it for now, who cares
#define mkchr(x) (int_t(x))
#define mknum(x) (int_t(x))
#define mksym(x) (int_t(x))
#define un_mknum(x) (int_t(x))

bool bitsmeta::BITS_FROM_LEFT = false;

void bitsmeta::init_type(primitive_type& type, const dict_t& dict) {
	switch (type.type) {
		case base_type::STR:
			// D: Q: TODO: how to set up individual arg's sym universe?
			// always init for STR/CHR or not? may alt universe size differ?
			if (type.bitness == 0) {
				type.set_bitness(BitScanR(dict.nsyms()));
				//type.bitness = BitScanR(dict.nsyms()); // nsyms-1? I guess
				// we have 'shared dict universe' for all sym/str args
			}
			break;
		case base_type::CHR:
			// it's always 8, always init (or if correct it's 0)
			if (type.bitness == 0) {
				type.set_bitness(8);
				//type.bitness = 8;
			}
			break;
		case base_type::INT: 
			// calc bitness for ints (we just have num at this point).
			if (type.bitness == 0) {
				type.set_bitness(BitScanR(type.num));
				//type.bitness = BitScanR(type.num);
			}
			else if (type.num >= 1 << type.bitness) {
				o::dump() << L"bitsmeta: num > max(bits)..." << endl;
				type.set_bitness(BitScanR(type.num));
				//type.bitness = BitScanR(type.num);
			}
			break;
		case base_type::NONE:
			type.set_bitness(1);
		default: ;
	}
}

/* prepare bits, bitness, caches if any */
void bitsmeta::init(const dict_t& dict) {
	// vargs should be set before entering, or rerun this on ordering change.
	if (types.empty()) return;
	mleftbits.clear();
	size_t lsum = 0, args = types.size(), maxb = 0;
	mleftbits[vargs[0]] = lsum;
	for (size_t i = 0; i != types.size(); ++i) {
		arg_type& type = types[vargs[i]];
		// either branch or use an iterator similar to get_types()
		type.r_iterate([&](primitive_type& subtype, size_t, sizes, size_t) {
			// we don't care about start, path for this
			init_type(subtype, dict);
		});
		type.init();
		if (i != args-1) {
			// we calc cache/maps regardless of the type, just need total bits
			// micro management is at the level of compound calls, eg leq_const
			lsum += types[vargs[i]].get_bits();
			mleftbits[vargs[i+1]] = lsum;
		}
		// vargs is redundant here as it's an aggregate, maxb/vbits will be same
		maxb = max(maxb, type.get_bits());
		//vbits[vargs[i]] = types[vargs[i]].get_bits();
	}
	args_bits = mleftbits.at(vargs[args-1]) + types[vargs[args-1]].get_bits();
	maxbits = maxb;

	size_t argsum = 0;
	if (maxbits == 0)
		return;
	mleftargs.clear();
	for (int_t bit = maxbits-1; bit >= 0; --bit) {
		map<size_t, size_t>& mpos = mleftargs[bit];
		for (size_t arg = 0; arg != types.size(); ++arg)
			if (types[vargs[arg]].get_bits() > size_t(bit))
				mpos[vargs[arg]] = argsum++;
	}
	DBG(assert(argsum == args_bits););
	hasmultivals = term::calc_hasmultivals(types);
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
		lsum += types[vargs[i]].get_bits();
		mleftbits[vargs[i+1]] = lsum;
		maxb = std::max(maxb, types[vargs[i]].get_bits());
		//vbits[vargs[i]] = types[vargs[i]].get_bits(); // wrong, missing args-1
	}
	args_bits = mleftbits.at(vargs[args-1]) + types[vargs[args-1]].get_bits();
	maxbits = std::max(maxb, types[vargs[args-1]].get_bits());
	DBG(assert(maxbits != 0);); // if (maxbits == 0) return;
	for (int_t bit = maxbits - 1; bit >= 0; --bit) {
		map<size_t, size_t>& mpos = mleftargs[bit];
		for (size_t arg = 0; arg != types.size(); ++arg)
			if (types[vargs[arg]].get_bits() > size_t(bit))
				mpos[vargs[arg]] = argsum++;
	}
	DBG(assert(argsum == args_bits););
	hasmultivals = term::calc_hasmultivals(types);
}

/* 
 this effectively 'cements' the bits, any later on changes result in add_bits
 (it's done on tbl init/init_bits or later on permute_type/add_bit/add_bit_perm)
*/
void bitsmeta::init_bits() {
	vbits = uints(types.size());
	// TODO: easier is just vbits.push_back(types[i].get_bits());
	for (size_t i = 0; i != types.size(); ++i)
		// vargs is redundant here as it's an aggregate, maxb/vbits will be same
		vbits[vargs[i]] = types[vargs[i]].get_bits();
	bitsfixed = true;
}

bool bitsmeta::set_args(const argtypes& vtypes, bool hasmultivals_) {
	if (vtypes.empty()) return false;
	DBG(assert(vtypes.size() > 0);); // don't call this if nothing to do
	// we're empty initialized already (to table len), so sizes need to match
	DBG(assert(types.size() == vtypes.size()););
	// !nterms meaning we have no previous types / bits data (size's always >0)
	if (!nterms)
		types = vtypes;
	else
		for (size_t i = 0; i != types.size(); ++i)
			update_type(types[i], vtypes[i]);
	++nterms;
	// TODO: a bug probably, once hasmultivals is set it can't be reset?
	if (hasmultivals && !hasmultivals_) {
		//o::dump() << endl;//L"set_args: hasmultivals && !hasmultivals_" << 
	}
	hasmultivals = hasmultivals || hasmultivals_;
	return true;
}

bool bitsmeta::update_type(arg_type& type, const arg_type& newtype) {
	if (!type.isCompatible(newtype)) return false;
	if (newtype.isNone()) return false; // non-deterministic, can't help us
	if (type.isNone()) return type = newtype, true;
	// either branch or use an iterator similar to get_types()
	// newtype is a 'concrete' type (non-NONE), so test it instead of the type
	if (newtype.isPrimitive()) // either both are primitive or NONE + prim.
		return update_type(type.primitive, newtype.primitive);
	else if (newtype.isCompound()) {
		//primtypes& types = type.compound.types;
		//const primtypes& newtypes = newtype.compound.types;
		const primtypes& types = type.get_primitives();
		const primtypes& newtypes = newtype.get_primitives();
		if (types.size() != newtypes.size()) {
			o::dump() << L"update_type: types.size() != newtypes.size()?"<<endl;
			return false;
		}
		bool changed = false;
		if (type.sig != newtype.sig) {
			if (newtype.sig.empty()) {} // newtype.sig = type.sig;
			else if (type.sig.empty()) type.sig = newtype.sig, changed = true;
			else {
				if (!type.isCompatible(newtype))
					throw runtime_error("update_type: different signatures?");
				// sigs are fine, just one needs to be updated, which one?
			}
			//changed = true;
		}

		type.r_iterate([&](primitive_type& subtype, size_t, sizes, size_t i) {
			changed |= update_type(subtype, newtypes[i]);
		});
		//for (size_t i=0; i != types.size(); ++i)
		//	changed |= 
		//		update_type(types[i], newtypes[i]);

		// now see if 'left' has changed, if so and only then update its sig
		// (or make some calc_sig() here just from types, if possible?)
		if (changed && type.sig != newtype.sig)
			type.sig = newtype.sig;
		return changed;
	} else throw 0;
}

bool bitsmeta::update_type(primitive_type& type, const primitive_type& newtype){
	bool changed = false;
	// if not set, skip
	if (newtype.isNone()) return false;
	if (type.isNone()) {
		type = newtype;
		changed = true; // first init...
	}
	if (type.type != newtype.type) 
		throw runtime_error("update_type: type mismatch?");
	//if (type.type == base_type::INT) 
	//	type.num = max(type.num, newtype.num); // no need if NONE but cheap
	if (type.type == base_type::INT && newtype.num > type.num) {
		//type.num = newtype.num;
		type.set_num(newtype.num);
		changed = true;
	}
	// we may not need this, it's 0 except for alt's (inheriting, once)
	if (newtype.bitness > type.bitness) {
		//type.bitness = newtype.bitness;
		type.set_bitness(newtype.bitness);
		changed = true;
	}
	return changed;
}

/* 
we're init already, this is just to update table back from alt/rules 
not entirely nice but handy to sync types in between tbls, rules, alts, for now
(this is to be deprecated, not much use, just use init() on any change)
*/
void bitsmeta::update_types(const argtypes& vtypes) {
	DBG(assert(types.size() <= vtypes.size()););
	bool changed = false;
	for (size_t i = 0; i != types.size(); ++i)
		changed |= 
			update_type(types[i], vtypes[i]);
	// this updates 'live', caches may change
	if (changed) init_cache();
}

bool bitsmeta::sync_types(
	argtypes& ltypes, const argtypes& rtypes, size_t larg, size_t rarg) {
	return sync_types(ltypes[larg], rtypes[rarg]);
}

bool bitsmeta::sync_types(
	argtypes& ltypes, multi_arg larg, const argtypes& rtypes, multi_arg rarg)
{
	arg_type& l = ltypes[larg.arg];
	const arg_type& r = rtypes[rarg.arg];
	if (larg.subarg == arg::none && rarg.subarg == arg::none)
		return sync_types(l, r);
	if (larg.subarg != arg::none && rarg.subarg != arg::none)
		return sync_types(l[larg], r[rarg]);
		//return sync_types(l[larg.subarg], r[rarg.subarg]);
	
	// TODO: needs extra handling for none compound or non-primitive comps etc.
	//if (larg.subarg != arg::none && r.isPrimitive())
	//	return sync_types(l[larg.subarg], r.primitive);
	//if (rarg.subarg != arg::none && l.isPrimitive())
	//	return sync_types(l.primitive, r[rarg.subarg]);

	if (larg.subarg != arg::none) {
		//arg_type& lsub = l[larg.subarg];
		arg_type& lsub = l[larg];
		if (r.isPrimitive() && lsub.isPrimitive())
			return sync_types(lsub.primitive, r.primitive);
		return sync_types(lsub, r);
		//return sync_types(lsub, r.primitive);
	}
	if (rarg.subarg != arg::none) {
		//const arg_type& rsub = r[rarg.subarg];
		const arg_type& rsub = r[rarg];
		if (l.isPrimitive() && rsub.isPrimitive())
			return sync_types(l.primitive, rsub.primitive);
		return sync_types(l, rsub);
		//return sync_types(l.primitive, rsub);
	}

	return false;
}

bool bitsmeta::sync_types(argtypes& ltypes, multi_arg larg, const arg_type& r) {
	arg_type& l = ltypes[larg.arg];
	if (larg.subarg == arg::none)
		return sync_types(l, r);
	// TODO: needs extra handling for none compound or non-primitive comps etc.
	if (r.isPrimitive()) // this isn't optimal, but should wind down below
		return sync_types(l[larg], r.primitive);
		//return sync_types(l[larg.subarg], r.primitive);
	return false;
}

bool bitsmeta::sync_types(arg_type& l, const arg_type& r) {
	if (!l.isCompatible(r)) return false;
	if (r.isNone()) return false; // non-deterministic, can't help us
	if (l.isNone()) return l = r, true;
	// either branch or use an iterator similar to get_types()
	// 'r' is a 'concrete' type (non-NONE), so test it instead of the type
	if (r.isPrimitive()) // either both are primitive or NONE + primitive
		return sync_types(l.primitive, r.primitive);
	else if (r.isCompound()) {
		//primtypes& ltypes = l.compound.types;
		//const primtypes& rtypes = r.compound.types;
		const primtypes& ltypes = l.get_primitives();
		const primtypes& rtypes = r.get_primitives();
		if (ltypes.size() != rtypes.size()) {
			o::dump() << L"sync_types: ltypes.size() != rtypes.size()??"<<endl;
			return false;
		}
		bool changed = false;
		if (l.sig != r.sig) {
			if (r.sig.empty()) {} // r.sig = l.sig;
			else if (l.sig.empty()) l.sig = r.sig, changed = true;
			else {
				if (!l.isCompatible(r))
					throw runtime_error("sync_types const: different signatures?");
			}
			//changed = true;
		}

		l.r_iterate([&](primitive_type& subtype, size_t, sizes, size_t i) {
			changed |= sync_types(subtype, rtypes[i]);
		});
		//for (size_t i = 0; i != ltypes.size(); ++i)
		//	changed |= sync_types(ltypes[i], rtypes[i]);

		if (changed && l.sig != r.sig)
			l.sig = r.sig;
		return changed;
	}
	else throw 0;
}

bool bitsmeta::sync_types(primitive_type& l, const primitive_type& r)
{
	bool changed = false;
	bool lnone = l.isNone(), rnone = r.isNone();
	if (rnone) return false;
	else if (lnone) return l = r, true;
	if (l.type != r.type) 
		throw runtime_error("sync_types: type mismatch?");
	if (l.type == base_type::INT && r.num > l.num) {
		//l.num = r.num;
		l.set_num(r.num);
		changed = true;
	}
	if (r.bitness > l.bitness) {
		//l.bitness = r.bitness;
		l.set_bitness(r.bitness);
		changed = true;
	}
	//DBG(assert(l.bitness < 100););
	//DBG(assert(r.bitness < 100););
	return changed;
}

bool bitsmeta::sync_types(
	argtypes& ltypes, multi_arg larg, argtypes& rtypes, multi_arg rarg) {
	bool lchng, rchng;
	return sync_types(ltypes, larg, rtypes, rarg, lchng, rchng);
}

bool bitsmeta::sync_types(
	argtypes& ltypes, multi_arg larg, argtypes& rtypes, multi_arg rarg,
	bool& lchng, bool& rchng) 
{
	lchng = rchng = false;
	arg_type& l = ltypes[larg.arg];
	arg_type& r = rtypes[rarg.arg];
	if (larg.subarg == arg::none && rarg.subarg == arg::none)
		return sync_types(l, r, lchng, rchng);
	if (larg.subarg != arg::none && rarg.subarg != arg::none)
		return sync_types(l[larg], r[rarg], lchng, rchng);
		//return sync_types(l[larg.subarg], r[rarg.subarg], lchng, rchng);
	// TODO: needs extra handling for none compound or non-primitive comps etc.
	// TODO: here we map comp sub to comp, not handled atm.
	if (larg.subarg != arg::none) {
		//arg_type& lsub = l[larg.subarg];
		arg_type& lsub = l[larg];
		if (r.isPrimitive() && lsub.isPrimitive())
			return sync_types(lsub.primitive, r.primitive, lchng, rchng);
		return sync_types(lsub, r, lchng, rchng);
	}
	if (rarg.subarg != arg::none) {
		//arg_type& rsub = r[rarg.subarg];
		arg_type& rsub = r[rarg];
		if (l.isPrimitive() && rsub.isPrimitive())
			return sync_types(l.primitive, rsub.primitive, lchng, rchng);
		return sync_types(l, rsub, lchng, rchng);
	}
	return false;
}

bool bitsmeta::sync_types(argtypes& ltypes, multi_arg larg, arg_type& r) {
	bool lchng, rchng;
	return sync_types(ltypes, larg, r, lchng, rchng);
}

bool bitsmeta::sync_types(
	argtypes& ltypes, multi_arg larg, arg_type& r, bool& lchng, bool& rchng) {
	lchng = rchng = false;
	arg_type& l = ltypes[larg.arg];
	if (larg.subarg == arg::none)
		return sync_types(l, r, lchng, rchng);
	// TODO: needs extra handling for none compound or non-primitive comps etc.
	//arg_type& lsub = l[larg.subarg];
	arg_type& lsub = l[larg];
	if (r.isPrimitive() && lsub.isPrimitive())
		return sync_types(lsub.primitive, r.primitive, lchng, rchng);
	return sync_types(lsub, r, lchng, rchng);
	//return false;
}

bool bitsmeta::sync_types(arg_type& l, arg_type& r) {
	bool lchng, rchng;
	return sync_types(l, r, lchng, rchng);
}

bool bitsmeta::sync_types(arg_type& l, arg_type& r, bool& lchng, bool& rchng) {
	lchng = rchng = false;
	if (!l.isCompatible(r)) return false;

	bool lnone = l.isNone(), rnone = r.isNone();
	if (lnone && rnone) return false;
	else if (rnone) return r = l, rchng = true;
	else if (lnone) return l = r, lchng = true;

	// at this point, both are of same type (as are compatible + not NONE)
	if (l.isPrimitive())
		return sync_types(l.primitive, r.primitive, lchng, rchng);
	else if (l.isCompound()) {
		//primtypes& ltypes = l.compound.types;
		//primtypes& rtypes = r.compound.types;
		const primtypes& ltypes = l.get_primitives();
		const primtypes& rtypes = r.get_primitives();
		// TODO: we need sizes upfront
		if (ltypes.size() != rtypes.size()) {
			o::dump() << L"sync_types: ltypes.size() != rtypes.size() ??"<<endl;
			return false;
		}
		bool changed = false;
		if (l.sig != r.sig) {
			if (r.sig.empty()) r.sig = l.sig, rchng = changed = true;
			else if (l.sig.empty()) l.sig = r.sig, lchng = changed = true;
			else {
				if (!l.isCompatible(r))
					throw runtime_error("sync_types: different signatures?");
			}
			//else throw runtime_error("sync_types: different signatures?");
			//changed = true;
		}

		l.r_iterate([&](primitive_type& subtype, size_t, sizes, size_t i) {
			bool lchanged, rchanged;
			changed |=
				sync_types(subtype, r.get_primitive(i), lchanged, rchanged);
			lchng |= lchanged;
			rchng |= rchanged;
		});
		//for (size_t i = 0; i != ltypes.size(); ++i) {
		//	bool lchanged, rchanged;
		//	primitive_type& ltype = l.get_primitive(i);
		//	primitive_type& rtype = r.get_primitive(i);
		//	changed |= 
		//		sync_types(ltype, rtype, lchanged, rchanged);
		//	lchng |= lchanged;
		//	rchng |= rchanged;
		//}

		if (l.sig != r.sig) {
			if (lchng && rchng) {
				// otherwise could happen, but not within compounds, l xor r
				o::dump() << L"sync_types: both left and right changed?" << endl;
				throw runtime_error("sync_types: both left and right changed?");
			}
			else if (lchng)
				l.sig = r.sig;
			else if (rchng)
				r.sig = l.sig;
		}
		return changed;
	}
	else throw 0;
}

bool bitsmeta::sync_types(
	primitive_type& l, primitive_type& r, bool& lchng, bool& rchng)
{
	lchng = rchng = false;
	bool lnone = l.isNone(), rnone = r.isNone();
	if (lnone && rnone) return false;
	else if (rnone) return r = l, rchng = true;
	else if (lnone) return l = r, lchng = true;
	if (l.type != r.type) 
		throw runtime_error("sync_types: type mismatch?");
	if (l.type == base_type::INT) {
		if (r.num > l.num) {
			//l.num = r.num;
			l.set_num(r.num);
			lchng = true;
		}
		else if (l.num > r.num) {
			//r.num = l.num;
			r.set_num(l.num);
			rchng = true;
		}
	}
	if (r.bitness > l.bitness) {
		//l.bitness = r.bitness;
		l.set_bitness(r.bitness);
		lchng = true;
	}
	else if (l.bitness > r.bitness) {
		//r.bitness = l.bitness;
		r.set_bitness(l.bitness);
		rchng = true;
	}
	//DBG(assert(l.bitness < 100););
	//DBG(assert(r.bitness < 100););
	return lchng || rchng;
}

bool bitsmeta::sync_types(argtypes& ltypes, argtypes& rtypes) {
	bool lchng, rchng;
	return sync_types(ltypes, rtypes, lchng, rchng);
}
bool bitsmeta::sync_types(
	argtypes& ltypes, argtypes& rtypes, bool& lchng, bool& rchng) {
	DBG(assert(ltypes.size() == rtypes.size()););
	for (size_t i = 0; i != ltypes.size(); ++i) {
		bool lchanged, rchanged;
		sync_types(ltypes[i], rtypes[i], lchanged, rchanged);
		lchng |= lchanged;
		rchng |= rchanged;
	}
	return lchng || rchng;
}

bool bitsmeta::sync_types(argtypes& rtypes) {
	return sync_types(*this, rtypes);
}
bool bitsmeta::sync_types(bitsmeta& l, argtypes& rtypes) {
	bool lchng = false, rchng = false, changed;
	changed =
		sync_types(l.types, rtypes, lchng, rchng);
	if (lchng) l.init_cache();
	//if (rchng) r.init_cache();
	return changed; // lchng || rchng;
}

//bool bitsmeta::sync_types(bitsmeta& l, term& t) {
//	return sync_types(l, t.types);
//}

bool bitsmeta::sync_types(bitsmeta& l, bitsmeta& r) {
	bool lchng = false, rchng = false, changed;
	changed = 
		sync_types(l.types, r.types, lchng, rchng);
	if (lchng) l.init_cache();
	if (rchng) r.init_cache();
	return changed; // lchng || rchng;
}
