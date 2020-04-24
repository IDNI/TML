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
#include <random>
#include <list>
#include "tables.h"
#include "dict.h"
#include "input.h"
#include "output.h"
#include "err.h"
#include "infer_types.h"
//#include "iterbdds.h"
#include "addbits.h"
using namespace std;

#define mkchr(x) (int_t(x))
#define mknum(x) (int_t(x))
#define mksym(x) (int_t(x))
#define un_mknum(x) (int_t(x))

size_t sig_len(const sig& s) {
	size_t r = 0;
	for (int_t x : get<ints>(s)) if (x > 0) r += x;
	return r;
}

void unquote(wstring& str) {
	for (size_t i = 0; i != str.size(); ++i)
		if (str[i] == L'\\') str.erase(str.begin() + i);
}

wstring _unquote(wstring str) { unquote(str); return str; }

#ifdef DEBUG
vbools tables::allsat(spbdd_handle x, size_t, const bitsmeta& bm) const {
//	const size_t args = siglens[tab];
	// TODO:
	// D: this no longer works, args * bits and (k+1)*bits below, bits too etc.
	// bits * args => bm.args_bits
	throw 0;
	vbools v = ::allsat(x, bm.args_bits), s;
	//for (bools b : v) {
	//	s.emplace_back(bm.args_bits);
	//	// D: this is bits-1st => args-1st conversion? what for? 
	//	// no longer works, but need to know the nature of this
	//	for (size_t n = 0; n != bits; ++n)
	//		for (size_t k = 0; k != args; ++k)
	//			s.back()[(k+1)*bits-n-1] = b[bm.pos(n, k, args)];
	//}
	return s;
}
#endif

/*
 primitive type's version of LEQ (?x < c  -  i.e. var < const).
- c - a const
- arg - var's arg #
- args - total # of arguments (for table, alt, body - or odd 'detached' bdd)
- bm - bitsmeta info to pass in (either table.bm or alt.bm or body.table.bm)
*/
spbdd_handle tables::leq_const(
	int_t c, size_t arg, size_t args, const bitsmeta& bm) const 
{
	if (!bm.types[arg].isPrimitive()) { throw 0; }
	size_t bits = bm.types[arg].get_bits();
	return leq_const(c, arg, args, bits, bits, bm);
	// D: should we cache this too, why not, I guess there could be many c-s?
	//static ekcmemo x;
	//static map<ekcmemo, spbdd_handle>::const_iterator it;
	//if ((it = leqcmemo.find(x = { c, arg, args, bm.vbits })) != leqcmemo.end())
	//	return it->second;
	//spbdd_handle r = leq_const(c, arg, args, bits, bits, bm);
	//return leqcmemo.emplace(x, r), r;
}

/*
 compound type's version of LEQ (?x < c  -  i.e. var < const).
- cs - a vector of consts (compound const) == limits
- arg - arg #
- args - total # of arguments (for table, alt, body - or odd 'detached' bdd)
- bm - bitsmeta info to pass in (either table.bm or alt.bm or body.table.bm)
*/
bdd_handles tables::leq_const(
	ints cs, size_t arg, size_t args, const bitsmeta& bm) const {
	if (!bm.types[arg].isCompound()) throw 0;
	//size_t bits = bm.types[arg].get_bits();
	//auto types = bm.types[arg].get_types();
	const primtypes& types = bm.types[arg].compound.types;
	if (types.size() != cs.size()) throw 0;
	size_t startbit = 0;
	bdd_handles v;
	//for (const primitive_type& type : types) {
	for (size_t i = 0; i != types.size(); ++i) {
		const primitive_type& type = types[i];
		int_t c = cs[i]; //if (cs[i] < 0) continue; // if NONE? who cares
		v.push_back(
			leq_const(c, arg, args, type.bitness, type.bitness, startbit, bm));
		startbit += type.bitness;
	}
	// we'll we ever need it backwards? subargs order is irrelevant? anyways
	//size_t startbit = bits;
	//for (int i = types.size()-1; i >= 0; --i) {
	//	const primitive_type& type = types[i];
	//	int_t c = cs[i];
	//	startbit -= type.bitness;
	//	leq_const(c, arg, args, type.bitness, type.bitness, startbit, bm);
	//}
	return v;
}

/*
 represents LEQ as in ?x < c (var < const).
 this is the compound type overload, see leq_const below for more.
- c - a const value
- arg - arg #
- args - total # of arguments (for table, alt, body - or odd 'detached' bdd)
- b - current bit
- bits - actually max # of bits (not the 'bit'), always start w/ (..., bits)
- startbit - real bit position start for this compound subarg
- bm - bitsmeta info to pass in (either table.bm or alt.bm or body.table.bm)
*/
spbdd_handle tables::leq_const(int_t c, size_t arg, size_t args, size_t b,
	size_t bits, size_t startbit, const bitsmeta& bm) const {
	// don't put bit() on both const/encode and pos(), either or.
	if (!--b)
		return (c & (1 << 0)) ? htrue : // (c & 1)
		::from_bit(bm.pos(startbit + bm.bit(0, bits), arg, args), false);
	return (c & (1 << b)) ?
		bdd_ite_var(bm.pos(startbit + bm.bit(b, bits), arg, args),
			leq_const(c, arg, args, b, bits, startbit, bm),
			htrue) :
		bdd_ite_var(bm.pos(startbit + bm.bit(b, bits), arg, args), hfalse,
			leq_const(c, arg, args, b, bits, startbit, bm));
}

/*
represents LEQ as in ?x < c (var < const even though param order is rev.).
(it's recursive but always invoke with leq_const(..., bits), or var-bits)
- c - a const value
- arg - arg #
- args - total # of arguments (for table, alt, body - or odd 'detached' bdd)
- bit - actually max # of bits (not the 'bit'), always start w/ (..., bits)
- bm - bitsmeta info to pass in (either table.bm or alt.bm or body.table.bm)
*/
spbdd_handle tables::leq_const(int_t c, size_t arg, size_t args, size_t b,
	size_t bits, const bitsmeta& bm) const {
	// why: we need to physically compare from higher to lower bits
	// b is as it is (for the sake of c), but we invert for pos to get right bit
	if (!--b)
		return (c & (1 << 0)) ? htrue : // (c & 1)
		::from_bit(bm.pos(bm.bit(0, bits), arg, args), false);
	return (c & (1 << b)) ? // (1 << b)
		bdd_ite_var(bm.pos(bm.bit(b, bits), arg, args), 
			leq_const(c, arg, args, b, bits, bm),
			htrue) :
		bdd_ite_var(bm.pos(bm.bit(b, bits), arg, args), hfalse,
			leq_const(c, arg, args, b, bits, bm));
	// this is for when bits are not reversed, so keep this code! (formalize it)
	//if (!--b)
	//	return (c & 1) ? htrue :
	//		::from_bit(bm.pos(0, arg, args), false);
	//return (c & (1 << b)) ?
	//	bdd_ite_var(bm.pos(b, arg, args), leq_const(c, arg, args, b, bits, bm),
	//		htrue) :
	//	bdd_ite_var(bm.pos(b, arg, args), hfalse,
	//		leq_const(c, arg, args, b, bits, bm));
}

typedef tuple<size_t, size_t, size_t, uints> skmemo;
typedef tuple<size_t, size_t, size_t, uints> ekmemo;
typedef tuple<int_t, size_t, size_t, uints> ekcmemo;
typedef tuple<ints, size_t, size_t, uints> skcompmemo;
map<skmemo, spbdd_handle> smemo;
map<ekmemo, spbdd_handle> ememo;
map<ekmemo, spbdd_handle> leqmemo;
map<ekcmemo, spbdd_handle> leqcmemo;
map<skcompmemo, spbdd_handle> scompmemo;

spbdd_handle tables::leq_var(size_t arg1, size_t arg2, size_t args, 
	const bitsmeta& bm) const {
	static ekmemo x;
	static map<ekmemo, spbdd_handle>::const_iterator it;
	size_t bits = bm.types[arg1].get_bits(); // .bitness;
	size_t bits2 = bm.types[arg2].get_bits(); // .bitness;
	// D: TODO: is this logic ok? we match bit by bit, if # bits differ => false
	// or should we actually throw an error here?
	if (bits != bits2) return hfalse;
	if (!(bm.types[arg1] == bm.types[arg2])) {
		o::dump() << L"leq_var: bm.types[arg1] != bm.types[arg2]?" << endl;
		//return hfalse;
	}
	// TODO: check if types are the same, that needs to match as well
	DBG(assert(!bm.vbits.empty() && bm.bitsfixed););
	if ((it = leqmemo.find(x = { arg1, arg2, args, bm.vbits })) != leqmemo.end())
		return it->second;
	spbdd_handle r = leq_var(arg1, arg2, args, bits, bm);
	return leqmemo.emplace(x, r), r;
}

/*
 note: this doesn't need to handle isCompound, as we just check all the bits
*/
spbdd_handle tables::leq_var(size_t arg1, size_t arg2, size_t args, size_t bit, 
	const bitsmeta& bm) const {
	if (!--bit)
		return	bdd_ite(::from_bit(bm.pos(0, arg2, args), true),
				htrue,
				::from_bit(bm.pos(0, arg1, args), false));
	return	bdd_ite(::from_bit(bm.pos(bit, arg2, args), true),
			bdd_ite_var(bm.pos(bit, arg1, args),
				leq_var(arg1, arg2, args, bit, bm), htrue),
			bdd_ite_var(bm.pos(bit, arg1, args), hfalse,
				leq_var(arg1, arg2, args, bit, bm)));
}

/*
 range - sets range conditions, universe limits
 note: we no longer have type encoded 'bits', so it's greatly simplified
*/
void tables::range(size_t arg, size_t args, bdd_handles& v, const bitsmeta& bm)
	const {
	if (bm.types[arg].isPrimitive()) {
		const arg_type& type = bm.types[arg];
		switch (type.primitive.type) {
		case base_type::CHR:
			v.push_back(
				leq_const((1 << type.primitive.bitness) - 1, arg, args, bm));
			break;
		case base_type::INT:
			// nums is set to max NUM, not universe size. For syms it's the size.
			v.push_back(leq_const(type.primitive.num, arg, args, bm));
			// bm.nums[arg]
			break;
		case base_type::STR:
			v.push_back(
				leq_const(type.get_syms(dict.nsyms())-1, arg, args, bm));
			break;
		default:
			v.push_back(hfalse);
			break;
		}
	} else if (bm.types[arg].isCompound()) {
		ints limits;
		for (const primitive_type& type : bm.types[arg].compound.types) {
			switch (type.type) {
			case base_type::CHR:
				//limits.push_back((1 << bm.types[arg].get_bits()) - 1); break;
				limits.push_back((1 << type.bitness) - 1); break;
			case base_type::INT:
				limits.push_back(type.num); break; // bm.nums[arg]
			case base_type::STR:
				// TODO: wrong but works for now, needs type.get_syms()
				limits.push_back(type.get_syms(dict.nsyms())-1); break;
			default:
				// just skip, shouldn't have NONE, but types/consts need 2 match
				limits.push_back(-1); break;
			}
		}
		// this's how Compounds should be done, gather all consts before call
		bdd_handles vhtemp = leq_const(limits, arg, args, bm);
		v.insert(v.end(), vhtemp.begin(), vhtemp.end());
	} else throw 0;
}

spbdd_handle tables::range(size_t arg, ntable tab, const bitsmeta& bm) {
	size_t args = tbls[tab].len;
	if (bm.types[arg].isPrimitive()) {
		const primitive_type& type = bm.types[arg].primitive;
		size_t bits = type.bitness; // .get_bits();
		int_t nums = 0, chars = 0, syms = 0;
		// limits are wrong here, should be -1, like for compound below...
		switch (type.type) {
		case base_type::CHR: 
			chars = 1 << type.bitness; break;
		case base_type::INT: 
			nums = type.num + 1; break; // bm.nums[arg]
		case base_type::STR: 
			syms = type.get_syms(dict.nsyms()); break;
		default: break;
		}
		// TODO: maybe 'bits' here is not right, same as leq_const, use vbits?
		array<int_t, 6> k =
			{ syms, nums, chars, (int_t)args, (int_t)arg, (int_t)bits };
		auto it = range_memo.find(k);
		if (it != range_memo.end()) return it->second;
		bdd_handles v;
		return	range(arg, args, v, bm),
			range_memo[k] = bdd_and_many(move(v));
	} else if (bm.types[arg].isCompound()) {
		const primtypes& types = bm.types[arg].compound.types;
		ints nums(types.size(), 0);
		ints chars(types.size(), 0);
		ints syms(types.size(), 0);
		//for (const primitive_type& type : bm.types[arg].compound.types) {
		for (size_t i = 0; i != types.size(); ++i) {
			const primitive_type& type = types[i];
			switch (type.type) {
			case base_type::CHR:
				chars[i] = (1 << type.bitness) - 1; break;
			case base_type::INT: 
				// TODO: ** this's wrong, we need nums stored per primitive
				nums[i] = type.num; break; // bm.nums[arg]
			case base_type::STR:
				// TODO: wrong but works for now, we need primitive::get_syms()
				syms[i] = type.get_syms(dict.nsyms()) - 1; break;
			default: break;
			}
		}
		// TODO: maybe 'bits' here is not right, same as leq_const, use vbits?
		tuple<ints, ints, ints, int_t, int_t, uints> k =
			{ syms, nums, chars, (int_t)args, (int_t)arg, bm.vbits };
		auto it = range_comp_memo.find(k);
		if (it != range_comp_memo.end()) return it->second;
		bdd_handles v;
		return	range(arg, args, v, bm),
			range_comp_memo[k] = bdd_and_many(move(v));
	} else throw 0;
}

uints perm_init(size_t n) {
	uints p(n);
	while (n--) p[n] = n;
	return p;
}

uints perm_init(const bitsmeta& bm) {
	size_t n = bm.args_bits;
	uints p(n);
	while (n--) p[n] = n;
	return p;
}

/* inits table's bitsmeta / bits info (after all facts are loaded) */
spbdd_handle table::init_bits(ntable tab, AddBits& addbits){ //tables&rtables){
	spbdd_handle x = tq;
	size_t args = len;
	bm.init(dict);

	// this below is completely useless for 'no facts', we'll overwrite w/ facts

	// this is for 2nd prog pass, if init and none changed, don't destroy .t
	// problem is what if smth changed? we should only init added bits, keep .t
	if (bm.bitsfixed) return tq;
	//bm.bitsfixed = true;
	uints vbits = bm.vbits; // old vbits, to know which bits 2 add_bit
	//bool isfullinit = vbits.empty();
	bool isaddbit = !vbits.empty();
	bm.init_bits();
	// TODO: for the moment we support only full reset, all bits are cleared
	// we should keep track of added bits (could be one or more)
	// and do only those bits here + do the proper live / dynamic add_bit / perm
	// this is important for tbls in between 2 progs (if changes) <- auto addbit

	if (!isaddbit) {
		// no need to permute, we init all bits in one pass, we know arg bits. 
		// only in add_bit later, when enlarging universe, we'd need to permute
		// x is hfalse, then we have and_many, how is this working? ok w/o perm?
		bdd_handles v = { x }; // ^ perm 
		for (size_t arg = 0; arg != args; ++arg) {
			// we don't care about type's kind, compound etc., just need bits
			size_t bits = bm.types[arg].get_bits();
			for (size_t b = 0; b != bits; ++b)
				v.push_back(::from_bit(bm.pos(b, arg, args), false));
		}
		// these bdd changes only 'stick' for table for rules that aren't facts. 
		// (.t bdd gets 'eaten' by the get_rules/get_facts for facts tables)
		return tq = bdd_and_many(move(v));
	} else {
		o::dump() << L"bits changed, addbit required, not implemented!" << endl;
		for (size_t arg = 0; arg != args; ++arg) {
			// this is safe/assumed only for primitives atm, others need work.
			if (!bm.types[arg].isPrimitive()) throw 0;
			size_t nbits = bm.types[arg].get_bits() - vbits[arg];
			if (nbits > 0) {
				addbits.clear();
				// set bits to 'ready', meaning bm bits is where it should be
				addbits.permute_type({ tab, arg }, nbits, true);
			}
		}
		return tq; // = bdd_and_many(move(v));
		//throw 0;
	}
}

void tables::init_bits() {
	range_clear_memo();
	
	for (size_t tab = 0; tab < tbls.size(); ++tab)
		tbls[tab].init_bits(tab, addBits);
	//for (auto& x : tbls)
	//	x.init_bits(); // x.t = x.init_bits();
	//++bits;
}

spbdd_handle tables::from_sym(
	size_t arg, size_t args, const arg_type& type, 
	int_t val, ints vals, c_bitsmeta& bm) const 
{
	if (type.isPrimitive())
		return from_sym(arg, args, val, bm);
	else if (type.isCompound())
		return from_sym(arg, args, vals, bm);
	else throw 0; // not implemented exception or something
}

/*
arg, args relate to 
1) alt's vm/varslen or
2) table term's ints/elems (or to facts terms)
3) body (get_body) is always having table behind, so is the same as (2)
Also, all bdd-s created must adhere to either of these 3 cases (as any bdd is 
always defined by its total arguments/size, arg order, arg-types/bitness and 
universe). The only exception seems to be the ALU/arithmetics handler which 
is creating some temp bdds (and args), TODO: not sure how to handle those.
We also can't 'mix' the bdd-s of different origin (unless we adjust/permute 1st)
*/
spbdd_handle tables::from_sym(
	size_t arg, size_t args, int_t val, c_bitsmeta& bm) const {
	// TODO: this needs Compound version
	if (!bm.types[arg].isPrimitive()) throw 0;
	static skmemo x;
	static map<skmemo, spbdd_handle>::const_iterator it;
	size_t bits = bm.types[arg].get_bits();
	// fix: cache on full bits-vector not just arg bits as pos-s need to be same
	DBG(assert(!bm.vbits.empty() && bm.bitsfixed););
	if ((it = smemo.find(x = { val, arg, args, bm.vbits })) != smemo.end())
		return it->second;
	spbdd_handle r = htrue;
	for (size_t b = 0; b != bits; ++b)
		r = r && bm.from_bit_re(b, bits, arg, args, val); // from_bit
	return smemo.emplace(x, r), r;
}

spbdd_handle tables::from_sym(
	size_t arg, size_t args, ints vals, c_bitsmeta& bm) const 
{
	// TODO: this needs Compound version
	if (!bm.types[arg].isCompound()) throw 0;

	static skcompmemo x;
	static map<skcompmemo, spbdd_handle>::const_iterator it;
	//size_t bits = bm.types[arg].get_bits();
	DBG(assert(!bm.vbits.empty() && bm.bitsfixed););
	it = scompmemo.find(x = { vals, arg, args, bm.vbits });
	if (it != scompmemo.end())
		return it->second;

	const primtypes& types = bm.types[arg].compound.types;
	if (types.size() != vals.size()) throw 0;
	size_t startbit = 0;
	spbdd_handle r = htrue;
	for (size_t i = 0; i != types.size(); ++i) {
		const primitive_type& type = types[i];
		int_t val = vals[i];
		size_t bits = type.bitness;
		// bits are 'per compound-arg' (used to encode the val only)
		for (size_t b = 0; b != bits; ++b)
			r = r && ::from_bit(
				bm.pos(startbit + b, arg, args), 
				val & (1 << bm.bit(b, bits)));
		// don't put bit() on both const/encode and pos(), either or.
		startbit += type.bitness;
	}
	return scompmemo.emplace(x, r), r;
}

/*
 note: no need to check against isCompound, we do / match all bits regardless
*/
spbdd_handle tables::from_sym_eq(
	size_t arg1, size_t arg2, size_t args, c_bitsmeta& bm) const {
	static ekmemo x;
	static map<ekmemo, spbdd_handle>::const_iterator it;
	size_t bits = bm.types[arg1].get_bits();
	size_t bits2 = bm.types[arg2].get_bits();
	// D: TODO: is this logic ok? we match bit by bit, if bits differ it's false
	if (bits != bits2) return hfalse;
	if (bm.types[arg1] != bm.types[arg2]) {
		o::dump() << L"from_sym_eq: bm.types[arg1] != bm.types[arg2]?" << endl;
		//return hfalse;
	}
	// TODO: check if types are the same as well
	DBG(assert(!bm.vbits.empty() && bm.bitsfixed););
	if ((it = ememo.find(x = { arg1, arg2, args, bm.vbits })) != ememo.end())
		return it->second;
	spbdd_handle r = htrue;
	for (size_t b = 0; b != bits; ++b)
		r = r && ::from_eq(bm.pos(b, arg1, args), bm.pos(b, arg2, args));
	return ememo.emplace(x, r), r;
}

spbdd_handle tables::from_fact(const term& t) {
	// TODO: memoize
	spbdd_handle r = htrue;
	static varmap vs;
	vs.clear();
	auto it = vs.end();
	// D: we need table for any bdd ops (e.g. from_sym etc.)
	DBG(assert(t.tab != -1););
	table& tbl = tbls[t.tab];
	for (size_t n = 0, args = t.size(); n != args; ++n) {
		if (t[n] >= 0) { 
			if (t.types[n].isPrimitive())
				r = r && from_sym(n, args, t[n], tbl.bm);
			else if (t.types[n].isCompound())
				r = r && from_sym(n, args, t.compvals[n], tbl.bm);
			else throw 0; // not implemented exception or something
		}
		else if (vs.end() != (it = vs.find(t[n])))
			r = r && from_sym_eq(n, it->second, args, tbl); // .bm);
		else if (vs.emplace(t[n], n), !t.neg)
			r = r && range(n, t.tab, tbl.bm);
	}
	return r;
}

sig tables::get_sig(const raw_term&r) {
	return{ dict.get_rel(r.e[0].e), r.arity };
}
sig tables::get_sig(const lexeme& rel, const ints& arity) {
	return { dict.get_rel(rel), arity };
}

term tables::from_raw_term(const raw_term& r, bool isheader, size_t orderid) {
	// D: use new raw_term.nargs to preinit nums, simplifies code/nums handling.
	ints t, vals;
	vector<ints> compvals;
	lexeme l;
	size_t nvars = 0;
	term::textype extype = (term::textype)r.extype;
	// D: header builtin is treated as rel, but differentiated later (decomp.)
	bool realrel = extype == term::REL || (extype == term::BLTIN && isheader);
	// skip the first symbol unless it's EQ/LEQ/ARITH (which has VAR/CONST as 1st)
	bool isrel = realrel || extype == term::BLTIN;
	// D: use -1, numeric_limits<int>::min()
	//ints nums = ints((!isrel ? r.nargs : r.nargs-1), 0);
	vector<arg_type> types, ptypes;
	//vector<vector<primitive_type>> comptypes; // primtypes
	//vector<primtypes> comptypes;
	primtypes comptypes;
	bool isprevarg = false, iscomp = false, hascomp = false,
		 is1stparenth = extype == term::REL || extype == term::BLTIN; // true;
	size_t nparenth = 0;
	// skip the first symbol unless it's EQ/LEQ/ALU (which has VAR/CONST as 1st)
	for (size_t n = !isrel ? 0 : 1; n < r.e.size(); ++n) {
		bool isarg = false;
		size_t tsize = t.size();
		switch (r.e[n].type) {
		case elem::NUM:
			t.push_back(mknum(r.e[n].num));
			// D: calc bitness only if needed (leave it for tbl in setargs)
			if (n + 1 < r.e.size() && r.e[n + 1].type == elem::ARGTYP) {
				// use dict just to store strings, avoid parsing twice
				// TODO: do we really want nums to be size_t? negatives anybody?
				types.push_back(
					dict.get_type_info(r.e[n + 1].e, r.e[n].num));
				//size_t num;
				//types.push_back(dict.get_type_info(r.e[n + 1].e, num));
				//if (num > 0)
				//	nums[t.size() - 1] = num;
			}
			else
				types.emplace_back(
					base_type::INT,
					(!realrel ? bitsmeta::BitScanR(r.e[n].num) : 0),
					r.e[n].num); // 0); // 
					//(!realrel ? bitsmeta::BitScanR(r.e[n].num) + 2 : 0),
			isarg = true;
			break;
		case elem::CHR:
			t.push_back(mkchr(r.e[n].ch));
			if (n + 1 < r.e.size() && r.e[n + 1].type == elem::ARGTYP) {
				types.push_back(dict.get_type_info(r.e[n + 1].e));
			}
			else // there's a bug with tight bits (dycks example), safe bits
				//types.emplace_back(base_type::CHR, 10); // chars = 255;
				types.emplace_back(base_type::CHR, 8); // chars = 255;
			isarg = true;
			break;
		case elem::VAR:
			t.push_back(dict.get_var(r.e[n].e));
			if (n + 1 < r.e.size() && r.e[n + 1].type == elem::ARGTYP) {
				types.push_back(dict.get_type_info(r.e[n + 1].e));
				//size_t num;
				//if (num > 0)
				//	nums[t.size()-1] = num;
			}
			else
				types.emplace_back(base_type::NONE, 0);
			++nvars;
			isarg = true;
			break;
		case elem::STR:
			l = r.e[n].e;
			++l[0], --l[1];
			t.push_back(dict.get_sym(dict.get_lexeme(
				_unquote(lexeme2str(l)))));
			if (n + 1 < r.e.size() && r.e[n + 1].type == elem::ARGTYP) {
				types.push_back(dict.get_type_info(r.e[n + 1].e));
				//size_t num;
				//if (num > 0)
				//	nums[t.size()-1] = num;
			}
			else
				types.emplace_back(base_type::STR, 0);
			//syms = dict.nsyms();
			isarg = true;
			break;
		case elem::SYM:
			t.push_back(dict.get_sym(r.e[n].e));
			if (n + 1 < r.e.size() && r.e[n + 1].type == elem::ARGTYP) {
				types.push_back(dict.get_type_info(r.e[n + 1].e));
				//size_t num;
				//if (num > 0)
				//	nums[t.size()-1] = num;
			}
			else
				types.emplace_back(base_type::STR, 0);
			//syms = dict.nsyms();
			isarg = true;
			break;
		case elem::OPENP:
			if (!is1stparenth) {
				++nparenth;
				if (isprevarg && !iscomp) {
					iscomp = true;
					hascomp = true;
				}
			}
			is1stparenth = false;
			break;
		case elem::CLOSEP:
			if (nparenth > 0) {
				--nparenth;
				if (iscomp) {
					iscomp = false;
					ptypes.pop_back();
					ptypes.emplace_back(compound_type{ comptypes });
					//arg_type& type = ptypes.back();
					//type = arg_type{ compound_type{comptypes} };
					////type = arg_type{ compound_type{comptypes.back()} };
				}
			}
			break;
		default:;
		}

		if (tsize < t.size()) {
			int_t val = t.back();
			const arg_type& type = types.back();
			if (!iscomp) {
				vals.push_back(val);
				compvals.push_back(ints{ val });
				ptypes.push_back(type);
				if (!type.isPrimitive()) throw 0;
				comptypes = primtypes{ type.primitive };
				//comptypes.push_back(primtypes{ type.primitive });
			} else {
				compvals.back().push_back(val);
				if (!type.isPrimitive()) throw 0;
				comptypes.push_back(type.primitive);
				//comptypes.back().push_back(type.primitive);
			}
		}

		isprevarg = isarg;
	}

	if (hascomp) {// vals, compvals, ptypes - is safe in both case, just to test
		// our arity is different as parser is not 'aware' of compounds (yet?)
		ints arity{ int_t(compvals.size()) };
		sig sign{ dict.get_rel(r.e[0].e), arity }; // t.arity };
		return to_tbl_term(
			realrel ? sign : sig{}, vals, compvals, ptypes, nvars,
			r.neg, extype, realrel, r.e[0].e, r.arith_op, orderid);
	}
	DBG(assert(t.size() == vals.size()););
	DBG(assert(t.size() == compvals.size()););
	DBG(assert(types.size() == ptypes.size()););
	return to_tbl_term(realrel ? get_sig(r) : sig{}, t, compvals, types, nvars,
		r.neg, extype, realrel, r.e[0].e, r.arith_op, orderid);
}

term tables::to_tbl_term(sig s, ints t, vector<ints> compvals, argtypes types, 
	size_t nvars, bool neg, term::textype extype, bool realrel, lexeme rel, 
	t_arith_op arith_op, size_t orderid){
	//bool realrel = extype == term::REL || (extype == term::BLTIN && isheader);
	ntable tab = realrel ? get_table(s) : -1;
	if (tab != -1)
		tbls[tab].bm.set_args(t, types); // , nums);
	return to_tbl_term(
		tab, t, compvals, types, nvars, neg, extype, rel, arith_op, orderid);
}

term tables::to_tbl_term(ntable tab, ints t, vector<ints> compvals, 
	argtypes types, size_t nvars, bool neg, term::textype extype, lexeme rel, 
	t_arith_op arith_op, size_t orderid) 
{
	if (extype == term::BLTIN) {
		int_t idbltin = dict.get_bltin(rel);
		if (tab > -1) {
			// header BLTIN rel w table, save alongside table (for decomp. etc.)
			tbls[tab].idbltin = idbltin;
			tbls[tab].bltinargs = t; // if needed, for rule/header (all in tbl)
			tbls[tab].bltinsize = nvars; // number of vars (<0)
		}
		return term(neg, tab, t, compvals, types, orderid, idbltin, nvars);
	}
	return term(neg, extype, arith_op, tab, t, compvals, types, orderid, nvars);
	// ints t is elems (VAR, consts) mapped to unique ints/ids for perms.
}

form::ftype transformer::getdual( form::ftype type) {
	switch (type) {
		case form::ftype::OR : return form::ftype::AND;
		case form::ftype::AND : return form::ftype::OR;
		case form::ftype::FORALL1 : return form::ftype::EXISTS1 ;
		case form::ftype::FORALL2 : return form::ftype::EXISTS2 ;
		case form::ftype::EXISTS1 : return form::ftype::FORALL1 ;
		case form::ftype::EXISTS2 : return form::ftype::FORALL2 ;
		default: throw 0;
	}
}

bool demorgan::push_negation( form *&root) {

	if(!root) return false;
	if( root->type == form::ftype::AND ||
		root->type == form::ftype::OR ) {

			root->type = getdual(root->type);
			if( ! push_negation(root->l) ||
				! push_negation(root->r))
				throw 0;
			return true;
	}
	else if ( allow_neg_move_quant && root->isquantifier()) {
			root->type = getdual(root->type);
			if( ! push_negation(root->r) ) throw 0;

			return true;
	}
	else {
		if( root->type == form::ftype::NOT) {
			form *t = root;
			root = root->l;
			t->l = t->r = NULL;
			delete t;
			return true;
		}
		else if ( root->type == form::ftype::ATOM)	{
			form* t = new form(form::ftype::NOT, 0 , NULL, root);
			root = t;
			return true;
		}
		return false;
	}

}

bool demorgan::apply( form *&root) {

	if(root && root->type == form::ftype::NOT  &&
		root->l->type != form::ftype::ATOM ) {

		bool changed = push_negation(root->l);
		if(changed ) {
			form *t = root;
			root = root->l;
			t->l = t->r = NULL;
			delete t;
			return true;
		}

	}
	return false;
}

bool implic_removal::apply(form *&root) {
	if( root && root->type == form::ftype::IMPLIES ) {
		root->type = form::OR;
		form * temp = new form( form::NOT);
		temp->l = root->l;
		root->l = temp;
		return true;
	}
	return false;
}

bool substitution::apply(form *&phi){
	if( phi && phi->type == form::ATOM) {
		if(phi->tm == NULL) {
				// simple quant leaf declartion
			auto it = submap_var.find(phi->arg);
			if( it != submap_var.end())		//TODO: Both var/sym should have mutually excl.
				return phi->arg = it->second, true;
			else if	( (it = submap_sym.find(phi->arg)) != submap_sym.end())
				return phi->arg = it->second, true;
			else return false;
		}
		else {
			bool changed = false;
			for( int &targ:*phi->tm) {
				auto it = submap_var.find(targ);
				if( it != submap_var.end())		//TODO: Both var/sym should have mutually excl.
					targ = it->second, changed = true;
				else if	( (it = submap_sym.find(targ)) != submap_sym.end())
					targ = it->second, changed =true;

			}
			return changed;
		}

	}
	return false;
}

void findprefix(form* curr, form*&beg, form*&end){

	if( !curr ||  !curr->isquantifier()) return;

	beg = end = curr;
	while(end->r && end->r->isquantifier())
		end = end->r;
}

bool pull_quantifier::dosubstitution(form *phi, form * prefend){

	substitution subst;
	form *temp = phi;

	int_t fresh_int;
	while(true) {
		if( temp->type == form::FORALL1 ||
			temp->type == form::EXISTS1 ||
			temp->type == form::UNIQUE1 )

			fresh_int = dt.get_fresh_var(temp->l->arg);
		else
			fresh_int = dt.get_fresh_sym(temp->l->arg);

		subst.add( temp->l->arg, fresh_int );

		wprintf(L"\nNew fresh: %d --> %d ", temp->l->arg, fresh_int);
		if( temp == prefend) break;
		else temp = temp->r;
	}

	return subst.traverse(phi);
}

bool pull_quantifier::apply( form *&root) {

	bool changed = false;
	if( !root || root->isquantifier()) return false;

	form *curr = root;
	form *lprefbeg = NULL, *lprefend = NULL, *rprefbeg = NULL, *rprefend= NULL;

	findprefix(curr->l, lprefbeg, lprefend);
	findprefix(curr->r, rprefbeg, rprefend);

	if( lprefbeg && rprefbeg ) {

		if(!dosubstitution(lprefbeg, lprefend) ||
			!dosubstitution(rprefbeg, rprefend) )
			throw 0;
		curr->l = lprefend->r;
		curr->r = rprefend->r;
		lprefend->r = rprefbeg;
		rprefend->r = curr;
		root = lprefbeg;
		changed = true;
		wprintf(L"\nPulled both: ");
		wprintf(L"%d %d , ", lprefbeg->type, lprefbeg->arg );
		wprintf(L"%d %d\n", rprefbeg->type, rprefbeg->arg );
	}
	else if(lprefbeg) {
		if(!dosubstitution(lprefbeg, lprefend))
			throw 0;
		curr->l = lprefend->r;
		lprefend->r = curr;
		root = lprefbeg;
		changed = true;
		wprintf(L"\nPulled left: ");
		wprintf(L"%d %d\n", lprefbeg->type, lprefbeg->arg );
	}
	else if (rprefbeg) {
		if(!dosubstitution(rprefbeg, rprefend))
			throw 0;
		curr->r = rprefend->r;
		rprefend->r = curr;
		root = rprefbeg;
		changed = true;
		wprintf(L"\nPulled right: ");
		wprintf(L"%d %d\n", rprefbeg->type, rprefbeg->arg );
	}
	return changed;
}

bool pull_quantifier::traverse( form *&root ) {

	bool changed  = false;
	if( root == NULL ) return false;
	if( root->l ) changed |= traverse( root->l );
	if( root->r ) changed |= traverse( root->r );

	changed = apply(root);

	return changed;
}

bool transformer::traverse(form *&root ) {
	bool changed  = false;
	if( root == NULL ) return false;

	changed = apply(root);

	if( root->l ) changed |= traverse(root->l );
	if( root->r ) changed |= traverse(root->r );


	return changed;
}

/* Populates froot argument by creating a binary tree from raw formula in rfm.
It is caller's responsibility to manage the memory of froot. If the function,
returns false or the froot is not needed any more, the caller should delete the froot pointer.
For a null input argument rfm, it returns true and makes froot null as well.
	*/
bool tables::from_raw_form(const raw_form_tree *rfm, form *&froot) {

	form::ftype ft = form::NONE;
	bool ret =false;
	form *root = NULL;
	int_t arg= 0;

	if(!rfm) return froot=root,  true;

	if(rfm->rt) {
		ft = form::ATOM;
		term t = from_raw_term(*rfm->rt);
		root = new form(ft, 0, &t );
		froot = root;
		if(!root) return false;
		return true;
	}
	else {
		switch(rfm->type) {
			case elem::NOT:
				root = new form(form::NOT);
				if(root ) {
					ret =  from_raw_form(rfm->l, root->l);
					froot = root;
					return ret;
				}
				else return false;

			case elem::VAR:
			case elem::SYM:
				ft = form::ATOM;
				if( rfm->type == elem::VAR)
					arg = dict.get_var(rfm->el->e);
				else arg = dict.get_sym(rfm->el->e);
				root = new form(ft, arg);
				froot = root;
				if(!root) return false;
				return true;

			case elem::FORALL: if(rfm->l->type == elem::VAR) ft = form::FORALL1; else ft = form::FORALL2; break;
			case elem::UNIQUE: if(rfm->l->type == elem::VAR) ft = form::UNIQUE1; else ft = form::UNIQUE2; break;
			case elem::EXISTS: if(rfm->l->type == elem::VAR) ft = form::EXISTS1; else ft = form::EXISTS2; break;
			case elem::OR:
			case elem::ALT: ft = form::OR; break;
			case elem::AND: ft = form::AND; break;
			case elem::IMPLIES: ft= form::IMPLIES; break;
			case elem::COIMPLIES: ft= form::COIMPLIES; break;
			default: return froot= root, false;
		}
		root =  new form(ft,0, 0);
		if( root ) {
			ret= from_raw_form(rfm->l, root->l);
			if(ret) ret = from_raw_form(rfm->r, root->r);
			froot = root;
			return ret;
		}
		return false;
	}
}

void form::printnode(int lv) {
	if(r) r->printnode(lv+1);
	wprintf(L"\n");
	for( int i=0; i <lv; i++)
		wprintf(L"\t");
	wprintf(L" %d %d", type, arg);
	if(l) l->printnode(lv+1);
}

void tables::out(wostream& os) const {
	//strs_t::const_iterator it;

	if (sort_tables) {
		// sort tables for easier comparing (new vs old code), leave it for now.
		uints otbls = perm_init(tbls.size()); // std::transform?
		sort(otbls.begin(), otbls.end(), 
			[this](const uint_t& x, const uint_t& y) {
				lexeme l = dict.get_rel(get<0>(tbls[x].s));
				lexeme r = dict.get_rel(get<0>(tbls[y].s));
				size_t llen = l[1] - l[0], rlen = r[1] - r[0];
				int_t cmp = wcsncasecmp(l[0], r[0], min(llen, rlen));
				if (cmp == 0)
					return llen < rlen;
				return cmp < 0;
			});
		for (size_t i = 0; i != otbls.size(); ++i)
			if (!has(tmprels, otbls[i]))
				out(os, tbls[otbls[i]].tq, otbls[i]);
		return;
	}
	
	for (ntable tab = 0; (size_t)tab != tbls.size(); ++tab)
//		if ((it = strs.find(dict.get_rel(tab))) == strs.end())
			out(os, tbls[tab].tq, tab);
//		else os << it->first << L" = \"" << it->second << L'"' << endl;
}

void tables::out(const rt_printer& f) const {
	for (ntable tab = 0; (size_t)tab != tbls.size(); ++tab)
		out(tbls[tab].tq, tab, f);
}

void tables::out(wostream& os, spbdd_handle x, ntable tab) const {
	//out(x, tab, [&os](const raw_term& rt) { os << rt << L'.' << endl; });

	// we're sorting tuples so it's not random, this is more natural, consistent
	//const table& tbl = tbls.at(tab);
	//const bitsmeta& bm = tbl.bm;
	set<term> r;
	decompress(x && tbls.at(tab).tq, tab, [&r](const term& t) {
		r.insert(t);
		});
	// TODO: make out_term / out_elem instead using raw_term/elem
	for(const term& t: r) os << to_raw_term(t) << L'.' << endl;
}

#ifdef __EMSCRIPTEN__
// o is `tabular_collector` - JS object with methods:
// - length(relation_name) - returns number of rows (or index of next new row)
// - set(relation_name, row, col, value) - sets value of the cell of a table
void tables::out(emscripten::val o) const {
	out([&o](const raw_term& t) {
		wstring relation = lexeme2str(t.e[0].e);
		int row = o.call<int>("length", ws2s(relation));
		int col = 0;
		for (size_t ar = 0, n = 1; ar != t.arity.size();) {
			wstringstream es;
			while (t.arity[ar] == -1) ++ar, es << L'(';
			if (n >= t.e.size()) break;
			while (t.e[n].type == elem::OPENP) ++n;
			for (int_t k = 0; k != t.arity[ar];)
				if ((es<<t.e[n++]),++k!=t.arity[ar]) {
					o.call<void>("set", relation, row,col++,
						ws2s(es.str()));
					es.str(L"");
				}
			while (n<t.e.size() && t.e[n].type == elem::CLOSEP) ++n;
			++ar;
			while (ar < t.arity.size()
				&& t.arity[ar] == -2) ++ar, es<<L')';
			if (es.str() != L"")
				o.call<void>("set", relation, row, col++,
					ws2s(es.str()));
		}
	});
}
#endif

void tables::decompress(spbdd_handle x, ntable tab, const cb_decompress& f,
	size_t len, bool allowbltins) const {
	const table& tbl = tbls.at(tab);
	// D: bltins are special type of REL-s, mostly as any but no decompress.
	if (!allowbltins && tbl.idbltin > -1) return;
	if (!len) len = tbl.len;
	allsat_cb(x/*&&ts[tab].tq*/, tbl.bm.args_bits, //len * bits,
		[tab, &f, len, this](const bools& p, int_t DBG(y)) {
		//DBG(assert(abs(y) == 1);) // D: not sure about this, turn on again?
#ifdef DEBUG
		if (abs(y) != 1) {
			wcout << L"decompress:   \t" << y << endl;
		}
#endif
		const bitsmeta& bm = tbls.at(tab).bm;
		DBG(assert(bm.types.size() == len););
		term r(false, term::REL, NOP, tab, 
			   ints(len, 0), vector<ints>(len), bm.types, 0, 0);
		// ints(len, 0), 
		// TODO: this needs Compound version
		for (size_t arg = 0; arg != len; ++arg) {
			if (bm.types[arg].isPrimitive()) {
				size_t bits = bm.get_bits(arg);
				for (size_t b = 0; b != bits; ++b)
					if (p[bm.pos(b, arg, len)])
						r[arg] |= 1 << bm.bit(b, bits); 
						//(bits - b -1); //  1 << b;
			} else if (bm.types[arg].isCompound()) {
				const primtypes& types = bm.types[arg].compound.types;
				size_t startbit = 0;
				ints vals(types.size(), 0);
				for (size_t i = 0; i != types.size(); ++i) {
					const primitive_type& type = types[i];
					size_t bits = type.bitness;
					int_t& val = vals[i];
					// bits are 'per compound-arg' (used to encode the val)
					for (size_t b = 0; b != bits; ++b)
						if (p[bm.pos(startbit + b, arg, len)])
							val |= 1 << bm.bit(b, bits); 
					// put bit() on either const/encode or pos(), not both.
					startbit += type.bitness;
				}
				r.compvals[arg] = vals;
			} else throw 0;
		}
		f(r);
	})();
}

set<term> tables::decompress() {
	set<term> r;
	for (ntable tab = 0; (size_t)tab != tbls.size(); ++tab)
		decompress(tbls[tab].tq, tab, [&r](const term& t){r.insert(t);});
	return r;
}

// D: TODO: just a quick & dirty fix, get_elem, to_raw_term (out etc.) is const
#define rdict() ((dict_t&)dict)
//#define get_var_lexeme(v) dict.get_lexeme(wstring(L"?v") + to_wstring(-v))
#define get_var_lexeme(v) rdict().get_lexeme(wstring(L"?v") + to_wstring(-v))

elem tables::get_elem(int_t val, const arg_type& type) const {
	if (!type.isPrimitive()) throw 0;
	if (val < 0) return elem(elem::VAR, get_var_lexeme(val));
	//arg_type etype = dumptype ? type : arg_type{base_type::NONE, size_t(-1)};
	arg_type etype = arg_type{ base_type::NONE, size_t(-1) };
	switch (type.primitive.type) {
		case base_type::CHR: 
			{
			const wchar_t ch = un_mknum(val);
			if (iswprint(ch)) return elem(ch, etype);
			return	elem(elem::SYM, rdict().get_lexeme(wstring(L"\"#") +
				to_wstring((unsigned char)(ch)) + L"\""), etype);
			}
			break;
		case base_type::INT:
			return elem((int_t)un_mknum(val), etype);
			break;
		case base_type::STR:
			return elem(elem::SYM, rdict().get_sym(val), etype);
			break;
		case base_type::NONE:
			return elem(elem::SYM, rdict().get_lexeme(L"???"), etype);
		default: throw 0;
	}
}

elem tables::get_elem(ints vals, const arg_type& type) const {
	if (!type.isCompound()) throw 0;
	// TODO: what if we really have vars inside compound? or just one var?
	//if (val < 0) return elem(elem::VAR, get_var_lexeme(val));
	std::wstringstream os, ss;
	primtypes types = type.compound.types;
	os << L"(";
	for (size_t i = 0; i != types.size(); ++i) {
		const primitive_type& type = types[i];
		int_t val = vals[i];
		if (i != 0)
			os << L" ";
		//if (val < 0) return elem(elem::VAR, get_var_lexeme(val));
		if (val < 0) { 
			os << get_var_lexeme(val);
			continue;
		}
		switch (type.type) {
			case base_type::CHR: 
				{
				const wchar_t ch = un_mknum(val);
				if (iswprint(ch)) 
					os << ch;
				else
					os << 
					wstring(L"\"#") + to_wstring((unsigned char)(ch)) + L"\"";
				}
				break;
			case base_type::INT:
				os << (int_t)un_mknum(val);
				break;
			case base_type::STR:
				os << rdict().get_sym(val);
				break;
			case base_type::NONE:
				os << L"???";
			default: throw 0;
		}
	}
	os << L")";
	return	elem(elem::SYM, rdict().get_lexeme(os.str()));
}

raw_term tables::to_raw_term(const term& r) const {
	raw_term rt;
	rt.neg = r.neg;
	size_t args;
	if (r.extype == term::EQ) {
		args = 2;
		rt.e.resize(args + 1);
		rt.e[0] = get_elem(r[0], r.types[0]);
		rt.e[1] = elem(elem::SYM, rdict().get_lexeme(r.neg ? L"!=" : L"="));
		rt.e[2] = get_elem(r[1], r.types[1]);
		rt.arity = { 2 };
	} else if (r.extype == term::LEQ) {
		args = 2;
		rt.e.resize(args + 1);
		rt.e[0] = get_elem(r[0], r.types[0]);
		// D: TODO: is this a bug (never used)? for neg it should be > not <= ?
		rt.e[1] = elem(elem::SYM, rdict().get_lexeme(r.neg ? L"<=" : L">"));
		rt.e[2] = get_elem(r[1], r.types[1]);
		rt.arity = { 2 };
	} else {
		args = tbls.at(r.tab).len, rt.e.resize(args + 1);
		rt.e[0] = elem(elem::SYM,
			dict.get_rel(get<0>(tbls.at(r.tab).s)));
		rt.arity = get<ints>(tbls.at(r.tab).s);
		for (size_t n = 1; n != args + 1; ++n) {
			if (r.types[n-1].isPrimitive())
				rt.e[n] = get_elem(r[n-1], r.types[n-1]);
			else if (r.types[n-1].isCompound())
				rt.e[n] = get_elem(r.compvals[n-1], r.types[n-1]);
			else throw 0;
		}
		rt.insert_parens(dict.op, dict.cl);
	}
	// TODO: BLTINS: add term::BLTIN handling
	DBG(assert(args == r.size());)
	return rt;
}

void tables::out(spbdd_handle x, ntable tab, const rt_printer& f) const {
	decompress(x&&tbls.at(tab).tq, tab, [f, this](const term& r) {
		f(to_raw_term(r)); });
}

void term::replace(const map<int_t, int_t>& m) {
	auto it = m.end();
	for (int_t& i : *this) if (m.end() != (it = m.find(i))) i = it->second;
}

void align_vars(vector<term>& v) {
	map<int_t, int_t> m;
	for (size_t k = 0; k != v.size(); ++k)
		for (size_t n = 0; n != v[k].size(); ++n)
			if (v[k][n] < 0 && !has(m, v[k][n]))
				m.emplace(v[k][n], -m.size() - 1);
	if (!m.empty()) for (term& t : v) t.replace(m);
}

uints tables::get_perm(
	const ints& poss, const bitsmeta& tblbm, const bitsmeta& altbm) 
{
	uints perm = perm_init(tblbm.args_bits);
	size_t args = tblbm.get_args();
	size_t len = altbm.get_args();
	for (size_t n = 0, b; n != args; ++n)
		if (poss[n] != -1) // if (vals[n] < 0)
			for (b = 0; b != tblbm.get_bits(n); ++b)
				perm[tblbm.pos(b, n, args)] = altbm.pos(b, poss.at(n), len);
	return perm;
}

uints tables::get_perm(const term& t, const varmap& vm, size_t len,
	const bitsmeta& tblbm, const bitsmeta& altbm) const {
	uints perm = perm_init(tblbm.args_bits); // t.size()* bits);
	DBG(assert(tblbm.get_args() == t.size()););
	DBG(assert(altbm.get_args() == len););
	size_t args = t.size(); // tblbm.get_args()
	for (size_t n = 0, b; n != args; ++n)
		if (t[n] < 0)
			for (b = 0; b != tblbm.get_bits(n); ++b)
				perm[tblbm.pos(b, n, args)] = altbm.pos(b, vm.at(t[n]), len);
	return perm;
}

map<size_t, int_t> varmap_inv(const varmap& vm) {
	map<size_t, int_t> inv;
	for (auto x : vm) {
		assert(!has(inv, x.second));
		inv.emplace(x.second, x.first);
	}
	return inv;
}

// D: this an alt method really, we need to change vm, varslen, inv, and now bm.
// TODO: any real need for this to be a template?
void tables::init_varmap(alt& a, const term& h, const term_set& al) {
	varmap m;
	// D: copy all header types + add below the body vars' types.
	ints ats = (ints)h; // , nums = h.nums;
	argtypes types = h.types; // nums are part of this now
	a.varslen = h.size();
	// D: why we're 'counting' all header args (varslen==h.size), not just vars?
	// how is this working for/w header-builtins?
	for (size_t n = 0; n != h.size(); ++n)
		if (h[n] < 0 && !has(m, h[n])) m.emplace(h[n], n);
	for (const term& t : al)
		for (size_t n = 0; n != t.size(); ++n)
			if (t[n] < 0) { // && !has(m, t[n])) {
				size_t arg;
				if (!has(m, t[n])) {
					m.emplace(t[n], a.varslen++);
					ats.push_back(t[n]);
					types.push_back(t.types[n]);
					//nums.push_back(t.nums[n]);
					arg = a.varslen-1;
				} else {
					arg = m[t[n]];
					// we don't care about this, this's pre-inference, remove it
					if (types[arg].isPrimitive() && t.types[n].isPrimitive()) {
						if (types[arg].primitive.type == base_type::NONE) {
							if (t.types[n].primitive.type != base_type::NONE)
								types[arg] = t.types[n];
							else if (t.tab != -1 &&
								tbls[t.tab].bm.types[n].primitive.type !=
								base_type::NONE)
								types[arg] = tbls[t.tab].bm.types[n];
						}
					}
				}
				// TODO: type inference is used now instead, remove the above?
				if (t.tab == -1) continue; // skip eq and stuff, for now
			}
	DBG(assert(a.varslen == ats.size() && a.varslen == types.size()););
	a.vm = m;
	a.inv = varmap_inv(a.vm);
	a.bm = bitsmeta(types.size());
	a.bm.set_args(ats, types); // , nums);
	// as alt-s are on-the-fly, we have too init right away, tbls differ
	a.bm.init(dict);
	// D: Q: for tbl we also 0 each bit into .t bdd, don't alts have this?
}

spbdd_handle tables::get_alt_range(const term& h, const term_set& a, 
	const varmap& vm, size_t len, const alt& at) {
	return get_alt_range(h, a, vm, len, at.bm);
}
spbdd_handle tables::get_alt_range(const term& h, const term_set& a,
	const varmap& vm, size_t len, const bitsmeta& bm) {
	set<int_t> pvars, nvars, eqvars, leqvars, arithvars;
	std::vector<const term*> eqterms, leqterms, arithterms;
	// first pass, just enlist eq terms (that have at least one var)
	for (const term& t : a) {
		bool haseq = false, hasleq = false, hasarith = false;
		for (size_t n = 0; n != t.size(); ++n)
			if (t[n] >= 0) continue;
			else if (t.extype == term::EQ) haseq = true; // .iseq
			else if (t.extype == term::LEQ) hasleq = true; // .isleq
			else if (t.extype == term::ARITH) hasarith= true; // .isarith
			else (t.neg ? nvars : pvars).insert(t[n]);
		// TODO: BLTINS: add term::BLTIN handling
		// only if iseq and has at least one var
		if (haseq) eqterms.push_back(&t);
		else if (hasleq) leqterms.push_back(&t);
		else if (hasarith) arithterms.push_back(&t);
	}
	for (const term* pt : eqterms) {
		const term& t = *pt;
		bool noeqvars = true;
		std::vector<int_t> tvars;
		for (size_t n = 0; n != t.size(); ++n)
			if (t[n] >= 0) continue;
			// nvars add range already, so skip all in that case...
			// and per 1.3 - if any one is contrained (outside) bail
			// out
			else if (has(nvars, t[n])) { noeqvars = false; break; }
			// if neither pvars has this var it should be ranged
			else if (!has(pvars, t[n])) tvars.push_back(t[n]);
			else if (!t.neg) { noeqvars = false; break; }
			// if is in pvars and == then other var is covered too,
			// skip. this isn't covered by 1.1-3 (?) but further
			// optimization.
		if (noeqvars)
			for (const int_t tvar : tvars)
				eqvars.insert(tvar);
			// 1.3 one is enough (we have one constrained, no need
			// to do both). but this doesn't work well, we need to
			// range all that fit.
			//break;
	}
	for (const term* pt : leqterms) {
	// - for '>' (~(<=)) it's enough if 2nd var is in nvars/pvars.
		// - for '<=' it's enough if 2nd var is in nvars/pvars.
		// - if 1st/greater is const, still can't skip, needs to be
		// ranged.
		// - if neither var appears elsewhere (nvars nor pvars) => do
		// both.
		//   (that is a bit strange, i.e. if appears outside one is
		//   enough)
		// ?x > ?y => ~(?x <= ?y) => ?y - 2nd var is limit for both LEQ
		// and GT.
		const term& t = *pt;
		assert(t.size() == 2);
		const int_t v1 = t[0], v2 = t[1];
		if (v1 == v2) {
			if (!has(nvars, v2)) leqvars.insert(v2);
			continue;
		}
		if (v2 < 0) {
			if (has(nvars, v2) || has(pvars, v2))
				continue; // skip both
			leqvars.insert(v2); // add and continue to 1st
		}
		if (v1 < 0 && !has(nvars, v1) && !has(pvars, v1))
			leqvars.insert(v1);
	}

	//XXX: arith support - Work in progress
	for (const term* pt : arithterms) {
		const term& t = *pt;
		assert(t.size() >= 3);
		const int_t v1 = t[0], v2 = t[1], v3 = t[2];
		if (v1 < 0 && !has(nvars, v1) && !has(pvars, v1))
			arithvars.insert(v1);
		if (v2 < 0 && !has(nvars, v2) && !has(pvars, v2))
			arithvars.insert(v2);
		if (v3 < 0 && !has(nvars, v3) && !has(pvars, v3))
			arithvars.insert(v3);
	}

	for (int_t i : pvars) nvars.erase(i);
	if (h.neg) for (int_t i : h) if (i < 0)
		nvars.erase(i), eqvars.erase(i), leqvars.erase(i); // arithvars.erase(i);
	bdd_handles v;
	for (int_t i : nvars) 
		range(vm.at(i), len, v, bm);
	for (int_t i : eqvars) 
		range(vm.at(i), len, v, bm);
	for (int_t i : leqvars) 
		range(vm.at(i), len, v, bm);
	for (int_t i : arithvars) 
		range(vm.at(i), len, v, bm);
	if (!h.neg) {
		set<int_t> hvars;
		for (int_t i : h) if (i < 0) hvars.insert(i);
		for (const term& t : a) for (int_t i : t) hvars.erase(i);
		for (int_t i : hvars) 
			range(vm.at(i), len, v, bm);
	}
	return bdd_and_many(v);
}

body tables::get_body(
	const term& t, const varmap& vm, size_t len, const alt& a) const {
	return get_body(t, vm, len, a.bm);
}
body tables::get_body(
	const term& t, const varmap& vm, size_t len, const bitsmeta& altbm) const {
	body b;
	DBG(assert(t.tab != -1););
	const table& tbl = tbls[t.tab];
	b.neg = t.neg, b.tab = t.tab,
	b.q = htrue, 
	b.ex = bools(tbl.bm.args_bits, false), // bools(t.size() * bits, false)
	b.perm = get_perm(t, vm, len, tbl.bm, altbm);
	// instead of saving ints, for permex_add_bit, caches better (alts, bodies)
	b.poss = ints(t.size(), -1);
	//b.vals = (ints)t;
	varmap m;
	auto it = m.end();
	for (size_t n = 0; n != t.size(); ++n) {
		if (t[n] >= 0) {
			if (t.types[n].isPrimitive())
				b.q = b.q && from_sym(n, t.size(), t[n], tbl.bm);
			else if (t.types[n].isCompound())
				b.q = b.q && from_sym(n, t.size(), t.compvals[n], tbl.bm);
			else throw 0; // not implemented exception or something
			get_var_ex(n, t.size(), b.ex, tbl.bm); 
		}
		else { // it's a var (<0)
			b.poss[n] = vm.at(t[n]);
			if (m.end() == (it = m.find(t[n]))) 
				m.emplace(t[n], n);
			else	
				b.q = b.q && from_sym_eq(n, it->second, t.size(), tbl), //.bm),
				get_var_ex(n, t.size(), b.ex, tbl); // .bm);
		}
	}
	return b;
}

void tables::get_facts(const flat_prog& m) {
	map<ntable, set<spbdd_handle>> f;
	for (const auto& r : m)
		if (r.size() != 1) continue;
		else if (r[0].goal) goals.insert(r[0]);
		else f[r[0].tab].insert(from_fact(r[0]));
	clock_t start, end;
	if (optimize) measure_time_start();
	bdd_handles v;
	for (auto x : f) {
		spbdd_handle r = hfalse;
		for (auto y : x.second) r = r || y;
		//tbls[x.first].tq = r;
		// fix for sequences anulling previous tq, but not sure if this's right?
		tbls[x.first].tq = (tbls[x.first].tq || r); //% d;
	}
	if (optimize)
		(o::ms() << L"# get_facts: "),
		measure_time_end();
}

// D: this is no longer valid, there're no 'global' nums, chars, syms, bits
void tables::get_nums(const raw_term&) {}
//void tables::get_nums(const raw_term& t) { 
//	for (const elem& e : t.e)
//		if (e.type == elem::NUM) _nums = max(_nums, e.num);
//		else if (e.type == elem::CHR) _chars = 255;
//}

bool tables::to_pnf( form *&froot) {

	implic_removal impltrans;
	demorgan demtrans(true);
	pull_quantifier pullquant(this->dict);

	bool changed = false;
	changed = impltrans.traverse(froot);
	changed |= demtrans.traverse(froot);
	wprintf(L"\n ........... \n");
	froot->printnode();
	changed |= pullquant.traverse(froot);
	wprintf(L"\n ........... \n");
	froot->printnode();

	return changed;

}
// D: this iterates & creates all terms (and into flat_prog) and inits tables.
flat_prog tables::to_terms(const raw_prog& p) {
	flat_prog m;
	vector<term> v;
	term t;

	for (const raw_rule& r : p.r)
		if (r.type == raw_rule::NONE && !r.b.empty())
			for (const raw_term& x : r.h) {
				get_nums(x), t = from_raw_term(x, true),
				v.push_back(t);
				for (const vector<raw_term>& y : r.b) {
					int i = 0;
					for (const raw_term& z : y) // term_set(
						v.push_back(from_raw_term(z, false, i++)),
						get_nums(z);
					align_vars(v), m.insert(move(v));
				}
			}
		else if(r.prft != NULL) {
			form* froot = NULL;
			from_raw_form(r.prft.get(), froot);
			wprintf(L"\n ........... \n");
			r.prft.get()->printTree();
			wprintf(L"\n ........... \n");
			froot->printnode();
			to_pnf(froot);
			if(froot) delete froot;
		}
		else for (const raw_term& x : r.h)
			t = from_raw_term(x, true), t.goal = r.type == raw_rule::GOAL,
			m.insert({t}), get_nums(x);

	return m;
}

int_t freeze(vector<term>& v, int_t m = 0) {
	map<int_t, int_t> p;
	map<int_t, int_t>::const_iterator it;
	// varbits: we need to go through 'types' now, anything we do
	for (const term& t : v) 
		for (size_t n = 0; n != t.size(); ++n) {
			if (t.types[n].isPrimitive()) {
				if (t.types[n].primitive.type == base_type::INT)
					m = max(m, un_mknum(t[n]));
			} else if (t.types[n].isCompound()) {
				const primtypes& types = t.types[n].compound.types;
				//for (const primitive_type& type : t.types[n].compound.types) {
				for (size_t i = 0; i != types.size(); ++i) {
					const primitive_type& type = types[i];
					if (type.type == base_type::INT)
						m = max(m, un_mknum(t.compvals[n][i]));
				}
			} else throw 0; // not implemented exception or something
		}
	for (term& t : v)
		for (int_t& i : t)
			if (i >= 0) continue;
			else if ((it = p.find(i)) != p.end()) i = it->second;
			else p.emplace(i, mknum(m)), i = mknum(m++);
	return m;
}

enum cqc_res { CONTAINED, CONTAINS, BOTH, NONE };

cqc_res maybe_contains(const vector<term>& x, const vector<term>& y) {
	if (x.size() == 1 || y.size() == 1) return NONE;
	set<ntable> tx, ty;
	for (size_t n = 1; n != x.size(); ++n)
		if (x[n].neg) return NONE; else tx.insert(x[n].tab);
	for (size_t n = 1; n != y.size(); ++n)
		if (y[n].neg) return NONE; else ty.insert(y[n].tab);
	bool maybe_contained, maybe_contains;
	if ((maybe_contained = tx.size() < ty.size()))
		for (ntable n : tx)
			if (!has(ty, n)) { maybe_contained = false; break; }
	if ((maybe_contains = tx.size() > ty.size()))
		for (ntable n : ty)
			if (!has(tx, n))
				return maybe_contained ? CONTAINED : NONE;
	return maybe_contained ? BOTH : CONTAINS;
}

flat_prog& get_canonical_db(vector<term>& x, flat_prog& p) {
	freeze(x);
	for (size_t n = 1; n != x.size(); ++n) p.insert({x[n]});
	return p;
}

flat_prog& get_canonical_db(vector<vector<term>>& x, flat_prog& p) {
	int_t m = 0;
	for (vector<term>& v : x)
		for (const term& t : v)
			for (size_t n = 0; n != t.size(); ++n) {
				if (t.types[n].isPrimitive()) {
					if (t.types[n].primitive.type == base_type::INT)
						m = max(m, un_mknum(t[n]));
				} else if (t.types[n].isCompound()) {
					const primtypes& types = t.types[n].compound.types;
					for (size_t i = 0; i != types.size(); ++i) {
						const primitive_type& type = types[i];
						if (type.type == base_type::INT)
							m = max(m, un_mknum(t.compvals[n][i]));
					}
				} else throw 0; // not implemented exception or something
			}
	for (vector<term>& t : x) {
		freeze(t, m);
		for (size_t n = 1; n != t.size(); ++n) p.insert({t[n]});
	}
	return p;
}

void tables::run_internal_prog(flat_prog p, set<term>& r, size_t nsteps) {
	dict_t tmpdict(dict); // copy ctor, only here, if this's needed at all?
	tables t(move(tmpdict), false, false, true);
	//t.dict = dict;
	t.bcqc = false;
	// D: just temp to recheck initial universe for str_rels tbls
	//t._chars = _chars, t._nums = _nums;
	if (!t.run_nums(move(p), r, nsteps)) throw 0;
}

void tables::getvars(
	const term& t, vector<set<arg_info>>& vars, map<int_t, arg_info>& mvars) {
	//for (int_t i : t) if (i < 0) v.insert(i);
	// we still have type inference in progress, best we can do is tbl or term
	set<arg_info> v;
	//const argtypes& types = t.tab != -1 ? tbls[t.tab].bm.types : t.types;
	//const ints& nums = t.tab != -1 ? tbls[t.tab].bm.nums : t.nums;
	for (size_t n = 0; n != t.size(); ++n)
		if (t[n] < 0) {
			//arg_info newinfo{ t[n], types[n], nums[n] };
			auto it = mvars.find(t[n]);
			if (it != mvars.end()) {
				arg_info& info = it->second; // mvars.at(t[n]);
				if (t.tab != -1)
					bitsmeta::sync_types(tbls[t.tab].bm.types[n], info.type);
				// , tbls[t.tab].bm.nums[n], info.num
				bitsmeta::sync_types(info.type, t.types[n]);
				// , info.num, t.nums[n]
				v.insert(info);
			} else {
				if (t.tab != -1) {
					//tbls[t.tab].bm.nums[n],
					arg_info info{ t[n], tbls[t.tab].bm.types[n], {t.tab, n} };
					mvars.emplace(t[n], info);
					v.insert(info);
				} else {
					arg_info info{ t[n], t.types[n] }; // , t.nums[n]
					mvars.emplace(t[n], info);
					v.insert(info);
				}
			}
			//v.insert({ t[n], types[n], nums[n] });
		}
	vars.push_back(move(v));
}

void tables::getvars(const vector<term>& t, 
	vector<set<arg_info>>& vars, map<int_t, arg_info>& mvars) {
	for (const term& x : t) getvars(x, vars, mvars);
}

void create_head(vector<term>&, ntable) {
/*	set<int_t> v;
	getvars(x, v);
	term h;
	h.tab = tab, h.insert(h.begin(), vx.begin(), vx.end());
	x.insert(x.begin(), move(h));*/
}

ntable tables::create_tmp_rel(size_t len, const argtypes& types) {
//, const ints& nums) 
	ntable tab = get_new_tab(dict.get_rel(get_new_rel()), {(int_t)len});
	// TODO: just some basic init, make it better
	table& tbl = tbls[tab];
	tbl.bm.set_args(ints(len), types); // , nums);
	tbl.bm.init(dict);
	return tmprels.insert(tab), tab;
}

//vector<term>& x, vector<set<arg_info>>& vars, map<int_t, arg_info>& mvars) {
void tables::create_tmp_head(
	vector<term>&, vector<set<arg_info>>&, map<int_t, arg_info>&) {
	throw 0;
	////set<int_t> v;
	//size_t n = vars.size();
	//getvars(x, vars, mvars); // v);
	//n = vars.size() - n;
	//create_head(x, create_tmp_rel(n));
	////create_head(x, create_tmp_rel(v.size()));
}

/*flat_prog tables::cqc(vector<term> x, vector<term> y) const {
	if (x == y) return {x};
	cqc_res r = maybe_contains(x, y), r1;
	if (r == NONE) return { x, y };
	const vector<term> xx = x, yy = y;
	flat_prog p;
	if (x[0].tab == y[0].tab) {
		if (r == BOTH) get_canonical_db({x, y}, p = { x, y });
		else if (r == CONTAINED) get_canonical_db({x}, p = { y });
		else get_canonical_db({y}, p = { x });
	}
	term f[2];
	f[0] = x[0], f[1] = y[0], x.erase(x.begin()), y.erase(y.begin());
	set<int_t> vx, vy;
	getvars(x, vx), getvars(y, vy);
	bool b;
	term hx, hy;
	if ((b = vx.size() == vy.size())) // TODO: support otherwise
		create_tmp_head(x), create_head(y, x[0].tab),
		hx = x[0], hy = y[0],
		get_canonical_db({ x, y }, p), p.insert(x), p.insert(y);
	run_internal_prog(p, r);
	if (has(r, f[0])) return has(r, f[1]) ? { x } : { y };
	if (has(r, f[1])) return { x };
	if (!b) return { x, y };
	if (has(r, x[0])) {
		if (has(r, y[0]))
			return	x[0] = hx, y[0] = hy,
				{ x, { xx[0], x[0] }, y, { yy[0], y[0] } };
		if (has(tmprels, x) && has(tmprels, y)) return { y };
	} else if (has(r, y[0]) && has(tmprels, x) && has(tmprels, y))
		return { x };
	return { x, y };
//	if (has(r, y[0]))
//		return print(print(o::out(),x)<<L" is a generalization of ",yy),
//		       true;
//	return false;
}*/

/*bool tables::cqc(const vector<term>& v, const flat_prog& m) const {
	for (const vector<term>& x : m) if (cqc(x, v)) return true;
	return false;
}

void tables::cqc_minimize(vector<term>& v) const {
	if (v.size() < 2) return;
	const vector<term> v1 = v;
	term t;
	for (size_t n = 1; n != v.size(); ++n) {
		t = move(v[n]), v.erase(v.begin() + n);
		if (!cqc(v1, v)) v.insert(v.begin() + n, t);
	}
	DBG(if (v.size() != v1.size())
		print(print(o::err()<<L"Rule\t\t", v)<<endl<<L"minimized into\t"
		, v1)<<endl;)
}*/

void replace_rel(const map<ntable, ntable>& m, vector<term>& x) {
	auto it = m.end();
	for (term& t : x) if (m.end() != (it = m.find(t[0]))) t[0] = it->second;
}

void replace_rel(const map<ntable, ntable>& m, flat_prog& p) {
	flat_prog q(move(p));
	for (vector<term> v : q) replace_rel(m, v), p.insert(v);
}

ntable tables::prog_add_rule(flat_prog& p, map<ntable, ntable>&,// r,
	vector<term> x) {
	return p.emplace(x), x[0].tab;
/*	if (!bcqc || x.size() == 1) return p.emplace(x), x[0].tab;
	for (const vector<term>& y : p)
		if (x == y || y.size() == 1) continue;
		else if (bodies_equiv(x, y)) {
			if (has(tmprels, x[0].tab) && has(tmprels, y[0].tab)) {

			}
			return y[0].tab;
		}
	if (has(tmprels, x[0][0])) {
		for (const vector<term>& y : p)
			if (has(tmprels, y[0].tab) && cqc(x, y) && cqc(y, x))
				return (tbls[x[0].tab].priority >
					tbls[y[0].tab].priority ? x : y)[0].tab;
		return x[0].tab;
	}
	if (x.size() > 3) cqc_minimize(x);
	if (!cqc(x, p)) p.emplace(x);
	return x[0].tab;*/
}

wostream& tables::print(wostream& os, const vector<term>& v) const {
	os << to_raw_term(v[0]);
	if (v.size() == 1) return os << L'.';
	os << L" :- ";
	for (size_t n = 1; n != v.size(); ++n) {
		if (v[n].goal) os << L'!';
		os << to_raw_term(v[n]) << (n == v.size() - 1 ? L"." : L", ");
	}
	return os;
}

wostream& tables::print(wostream& os, const flat_prog& p) const {
	for (const auto& x : p)
		print(os << x[0].tab << L'\t' << (x[0].tab == -1 ? 0 : tbls[x[0].tab].priority) <<
			L'\t', x) << endl;
/*	map<size_t, flat_prog> m;
	for (const auto& x : p) m[tbls[x[0].tab].priority].insert(x);
	size_t n = m.rbegin()->first;
	vector<flat_prog> v(n);
	for (const auto& x : m) v[n--] = move(x.second);
	for (n = 0; n != v.size(); ++n)
		for (const vector<term>& y : v[n])
			print(os << n << L'\t', y) << endl;*/
	return os;
}

wostream& tables::print_dict(wostream& os) const {
	return os << dict;
}

/* 
 altid is now needed as we go through alts twice, during inference and here 
 (i.e. we need to sync/match individual alts for type inference purposes)
*/
void tables::get_alt(
	const term_set& al, const term& h, alt_set& as, size_t altid) {
	alt a;
	set<int_t> vs;
	set<pair<body, term>> b;
	spbdd_handle leq = htrue, q;
	pair<body, term> lastbody;

	if (autotype) {
		map<tbl_arg, alt>::const_iterator ait = 
			infer.altstyped.find({h.tab,altid});
		if (ait != infer.altstyped.end()) {
			init_varmap(a, h, al); // we get varmaps, varslen, inv and bm set
			a.bm = ait->second.bm; // just copy bm, leave varmap for init
			if (a.vm.size() != ait->second.vm.size() ||
				a.vm != ait->second.vm ||
				a.bm.types.size() != ait->second.bm.types.size() ||
				a.bm.args_bits != ait->second.bm.args_bits ||
				a.bm.get_args() != ait->second.bm.get_args()) {
				wcout << L"get_alt a.bm != altstyped->bm:" << 
					h.tab << L"," << altid << L"," << endl;
			}
			DBG(assert(a.vm.size() == ait->second.vm.size()););
			DBG(assert(a.vm == ait->second.vm););
			DBG(assert(a.bm.types.size() == ait->second.bm.types.size()););
			DBG(assert(a.bm.args_bits == ait->second.bm.args_bits););
			DBG(assert(a.bm.get_args() == ait->second.bm.get_args()););
			// ideally we should just take alt saved, 
			// but there could be issues w/ varmap remapping etc.
			// we could move here safely as it's no longer needed?
			//a = ait->second;
		} else {
			if (optimize)
				wcout << L"altstyped: ?" << h.tab << L"," << altid << endl;
			throw 0;
			// D: this makes alt's bitmeta bits (for alt specific args/bdds).
			init_varmap(a, h, al); // we get varmaps, varslen, inv and bm set
			// this could now be removed if -autotype is on, done in get_types()?
			tbls[h.tab].bm.update_types(a.bm.types); // , a.bm.nums);
		}
	}

	for (const term& t : al) {
		if (t.extype == term::REL) {
			b.insert(lastbody = { get_body(t, a.vm, a.varslen, a), t });//.bm
			// track which bodies/tbls relate to tbls - for addbit/types
			a.bodytbls.insert(t.tab);
		} else if (t.extype == term::BLTIN) {
			DBG(assert(lastbody.second.size() > 0););
			DBG(assert(t.idbltin >= 0););
			a.idbltin = t.idbltin; // store just a dict id, fetch type on spot
			a.bltinargs = t;
			// TODO: check that vars match - in number and names too?
			// this is only relevant for 'count'? use size differently per type
			term& bt = lastbody.second;
			a.bltinsize = count_if(bt.begin(), bt.end(),
				[](int i) { return i < 0; });
		} else if (t.extype == term::ARITH) {
			// TODO: we might want to sync types for all builtins
			//// alt types/nums are up-to-date, sync that into our term
			//for (size_t n = 0; n != t.size(); ++n)
			//	if (t[n] < 0) {
			//		size_t arg = a.vm.at(t[n]);
			//		const argtypes& types = a.bm.types;
			//		const ints& nums = a.bm.nums;
			//		bitsmeta::sync_types(
			//			t.types[n], types[arg], t.nums[n], nums[arg]);
			//		//bitsmeta::sync_types(t.types, types, t.nums, nums, n,arg);
			//	}
			//returning bdd handler on leq variable
			if (!isarith_handler(t, a, h.tab, leq)) return;
			continue;
		}
		else if (t.extype == term::EQ) { //.iseq
			DBG(assert(t.size() == 2););
			if (t[0] == t[1]) {
				if (t.neg) return;
				continue;
			}
			if (t[0] >= 0 && t[1] >= 0) {
				if (t.neg == (t[0] == t[1])) return;
				continue;
			}
			if (t[0] < 0 && t[1] < 0)
				q = from_sym_eq(a.vm.at(t[0]), a.vm.at(t[1]), a.varslen, a);
			else if (t[0] < 0) {
				q = from_sym(a.vm.at(t[0]), a.varslen, t.types[1], t[1], 
							 t.compvals[1], a.bm);
				//q = from_sym(a.vm.at(t[0]), a.varslen, t[1], a.bm);
			}
			else if (t[1] < 0) {
				q = from_sym(a.vm.at(t[1]), a.varslen, t.types[0], t[0],
							 t.compvals[0], a.bm);
				//q = from_sym(a.vm.at(t[1]), a.varslen, t[0], a.bm);
			}
			a.eq = t.neg ? a.eq % q : (a.eq && q);
		} else if (t.extype == term::LEQ) {
			DBG(assert(t.size() == 2););
			if (t[0] == t[1]) {
				if (t.neg) return;
				continue;
			}
			if (t[0] >= 0 && t[1] >= 0) {
				if (t.neg == (t[0] <= t[1])) return;
				continue;
			}
			// TODO: this needs Compound version (if const is compound)
			if (t[0] < 0 && t[1] < 0)
				q = leq_var(a.vm.at(t[0]), a.vm.at(t[1]), a.varslen, a); //.bm);
			else if (t[0] < 0)
				q = leq_const(t[1], a.vm.at(t[0]), a.varslen, a); // .bm);
			/*
			//XXX:replacement of leq_const by leq_var, needs further test and cleanup
			else if (t[0] < 0) {
				size_t args = t.size();
				// D: this will now fail (variable pos), args should be varslen?
				spbdd_handle aux = from_sym(1, args, t[1], a.bm);
				// D: this's changed, you need to pass a.bm (or specific bm),
				// problem is you seem to shift vars by one here, i.e. you need
				// to make your own bitsmeta struct based on a.bm and args/ops.
				q = leq_var(a.vm.at(t[0]), a.vm.at(t[0])+1, a.varslen+1, bits, aux, a.bm);

				bools exvec;
				for (size_t i = 0; i < bits; ++i) {
					exvec.push_back(false);
					exvec.push_back(true);
				}
				q = q/exvec;

				uints perm1;
				perm1 = perm_init(2*bits);
				for (size_t i = 1; i < bits; ++i) {
					perm1[i*2] = perm1[i*2]-i ;
				}
				q = q^perm1;
			}
			*/
			else if (t[1] < 0)
				// 1 <= v1, v1 >= 1, ~(v1 <= 1) || v1==1.
				// TODO: this needs Compound version (if const is compound)
				q = htrue % leq_const(t[0],
					a.vm.at(t[1]), a.varslen, a.bm) ||
					from_sym(a.vm.at(t[1]), a.varslen, t.types[0], t[0],
							 t.compvals[0], a.bm);
					//from_sym(a.vm.at(t[1]), a.varslen, t[0], a);
			leq = t.neg ? leq % q : (leq && q);
		}
		// we use LT/GEQ <==> LEQ + reversed args + !neg
	}

	a.rng = bdd_and_many({ get_alt_range(h, al, a.vm, a.varslen, a), leq });

	// D: body caching here (and alt above) messes up permex_add_bit later, we
	// need a way to calc perm/ex again at any later point. perm/ex/a.vm is 
	// normally enough (for bdds/ops), but to recreate it, happens on addbit etc
	// we need full info. If we save term/ints that turns off caching. Solution
	// is to use poss map from a.vm to body positions, cache seems to work fine,
	// and we can do permex/add_bit.
	static set<body*, ptrcmp<body>>::const_iterator bit;
	body* y;
	for (auto x : b) {
		a.t.push_back(x.second);
		if ((bit=bodies.find(&x.first)) != bodies.end())
			a.push_back(*bit);
		else *(y=new body) = x.first, a.push_back(y), bodies.insert(y);
	}
	// D: we permute (prune) from alt to header/tbl (i.e. alt bm => tbl bm)
	// (if needed we could make custom bm w/ its types... but this seems clear)
	const table& tbl = tbls[h.tab];
	auto d = deltail(a.varslen, h.size(), a.bm, tbl.bm);
	a.ex = d.first, a.perm = d.second, as.emplace(a, altid);
}

lexeme tables::get_new_rel() {
	static size_t last = 1;
	wstring s = L"r";
	size_t sz;
	lexeme l;
retry:	sz = dict.nrels(), l = dict.get_lexeme(s + to_wstring(last));
	dict.get_rel(l);
	if (dict.nrels() == sz) { ++last; goto retry; }
	return l;
}

template<typename T>
void dag_get_reachable(const map<T, set<T>>& g, const T& t, set<T>& r) {
	if (has(r, t)) return;
	auto it = g.find(t);
	if (it != g.end())
		for (const T& x : it->second)
			dag_get_reachable(g, x, r);
	r.insert(t);
}

template<typename T>
set<T> dag_get_reachable(const map<T, set<T>>& g, const T& t) {
	set<T> r;
	return dag_get_reachable<T>(g, t, r), r;
}

void tables::table_increase_priority(ntable t, size_t inc) {
	for (ntable x : dag_get_reachable(deps, t)) tbls[x].priority += inc;
}

void tables::set_priorities(const flat_prog& p) {
	for (table& t : tbls) t.priority = 0;
	for (const vector<term>& x : p) {
		set<ntable>& s = deps[x[0].tab];
		for (size_t n = 1; n != x.size(); ++n)
			if (has(tmprels, x[n].tab))
				s.insert(x[n].tab);
	}
	for (const auto& x : deps)
		for (ntable y : x.second)
			if (has(tmprels, y))
				table_increase_priority(y);
}

/*set<term> tables::bodies_equiv(vector<term> x, vector<term> y) const {
//	if (x[0].size() != y[0].size()) return false;
	x[0].tab = y[0].tab;
	x.erase(x.begin()), y.erase(y.begin()),
	create_head(x, x[0].tab), create_head(y, y[0].tab);
	if (cqc(x, y)) {
		if (cqc(y, x)) return true;
	}
}*/

vector<term> tables::interpolate(
	vector<term> x, set<arg_info> v, const map<int_t, arg_info>& mvars) {
	term t;
	//set<int_t> done;
	for (size_t k = 0; k != x.size(); ++k)
		for (size_t n = 0; n != x[k].size(); ++n) {
			//if (has(mvars, x[k][n]) && !has(done, x[k][n])) {
			arg_info val{ x[k][n], {base_type::NONE, 0, 0} }; // , 0
			if (has(v, val)) {
				const arg_info& info = mvars.at(x[k][n]);
				t.push_back(x[k][n]);
				t.types.push_back(info.type);
				//t.nums.push_back(info.num); // part of the type now
				// we should map_type but we don't have a table yet, do it below
				v.erase(val); // x[k][n]);
				//done.insert(x[k][n]);
				//mvars.erase(x[k][n]);
			}
		}
	t.tab = create_tmp_rel(t.size(), t.types); // , t.nums);
	for (size_t n = 0; n != t.size(); ++n) {
		DBG(assert(t[n] < 0););
		if (has(mvars, t[n])) {
			const arg_info& info = mvars.at(t[n]);
			// this should preserve the original 'relationship' otherwise lost
			if (info.arg.tab != -1)
				infer.map_type({ t.tab, n }, {info.arg.tab, info.arg.arg});
			else
				o::dump() << L"interpolate, no tbl/arg?" << L"" << endl;
		}
	}
	x.insert(x.begin(), t);
	return x;
}

set<arg_info> intersect(const set<arg_info>& x, const set<arg_info>& y) {
	set<arg_info> r;
	set_intersection(x.begin(), x.end(), y.begin(), y.end(),
		inserter(r, r.begin()));
	return r;
}

flat_prog tables::transform_bin(const flat_prog& q) {
	//const flat_prog q = move(p);
	flat_prog p;
	vector<set<arg_info>> vars; //vector<set<int_t>> vars;
	map<int_t, arg_info> mvars;
	auto getterms = [&vars]
		(const vector<term>& x) -> vector<size_t> {
		if (x.size() <= 3) return {};
/*		vector<size_t> e;
		for (size_t n = 1; n != x.size(); ++n)
			if (has(exts, x[n].tab)) e.push_back(n);
		if (e.size() == x.size() - 1) return { 1, 2 };
		if (e.size() > 1) return { e[0], e[1] };*/
		size_t max = 0, b1 = 0, b2, n;
		for (size_t i = 2; i != x.size(); ++i)
			for (size_t j = 1; j != i; ++j)
				if (max < (n=intersect(vars[i],vars[j]).size()))
					max = n, b1 = j, b2 = i;
		if (!b1) b1 = 1, b2 = 2;
		return { b1, b2 };
	};
	vector<term> r;
	vector<size_t> m;
	for (vector<term> x : q) {
		if (x[0].goal) { goals.insert(x[0]); continue; }
			//prog_add_rule(p, x); continue; }
		for (const term& t : x) {
			getvars(t, vars, mvars);
		}
		while (!(m = getterms(x)).empty()) {
			for (size_t i : m) r.push_back(x[i]);
			for (size_t n = m.size(); n--;)
				x.erase(x.begin() + m[n]),
				vars.erase(vars.begin() + m[n]);
			set<arg_info> v; // set<int_t> v;
			for (const auto& s : vars)
				v.insert(s.begin(), s.end());
			r = interpolate(r, move(v), mvars);
			x.push_back(r[0]);
			getvars(r[0], vars, mvars);
			p.insert(move(r));
		}
		p.insert(move(x)), vars.clear(), mvars.clear();
	}
	if (print_transformed) print(o::out()<<L"after transform_bin:"<<endl,p);
	return p;
}

/*struct cqcdata {
	vector<term> r;
	size_t from;
	set<int_t> vars;
	set<ntable> tabs;
	cqcdata() {}
	cqcdata(const vector<term>& r) : r(r) {
		from = r.size();
		if (from == 1) return;
		sort(r.begin(), r.end());
		for (size_t n = 1; n < from;)
			if (tabs.insert(find(r[n].tab).second) ++n;
			else r.push_back(r[n]), r.erase(r.begin() + n), --from;
		for (size_t n = from; n != r.size(); ++n) getvars(r[n], vars);
		for (size_t n = 1, k; n != from; ++n)
			for (k = 0; k != r[n].size(); ++k)
				if (r[n][k] < 0) vars.erase(r[n][k]);
		align_vars(r);
	}
};
void tables::cqc_minimize(cqcdata& d) {
	if (d.from != d.r.size()) return;
}
void tables::cqc(flat_prog& p) {
	vector<cqcdata> v;
	for (const vector<term>& r : p)
		v.emplace_back(r), cqc_minimize(v.back());
}*/

/* compare tbl and alt types (given they're different in size, start is same) */
bool tables::equal_types(const table& tbl, const alt& a) const {
	//DBG(assert(a.bm.types.size() == tbl.bm.types.size()););
	//DBG(assert(a.bm.types == tbl.bm.types););
	return equal(tbl.bm.types.begin(), tbl.bm.types.end(), a.bm.types.begin());
}

void tables::get_rules(flat_prog p) {
	bcqc = false;
	get_facts(p);
	for (const vector<term>& x : p)
		for (size_t n = 1; n != x.size(); ++n)
			exts.insert(x[n].tab);
	for (const vector<term>& x : p) if (x.size() > 1) exts.erase(x[0].tab);
	if (bcqc) print(o::out()<<L"before cqc, "<<p.size()<<L" rules:"<<endl,p);
	flat_prog q(move(p));
	map<ntable, ntable> mt;
	for (const auto& x : q) prog_add_rule(p, mt, x);
	replace_rel(move(mt), p);
	if (bcqc) print(o::out()<<L"after cqc before tbin, "
		<<p.size()<<L" rules."<<endl, p);
#ifndef TRANSFORM_BIN_DRIVER
	if (bin_transform) {
		if (autotype && !pBin.empty()) 
			 p = move(pBin);
		else p = transform_bin(p); // move unnecessary 
	}
#endif
	if (bcqc) print(o::out()<<L"before cqc after tbin, "
		<<p.size()<< L" rules."<<endl, p);
	// TODO: see about this, it was removed cause of new transform_bin
	//q = move(p);
	//for (const auto& x : q) prog_add_rule(p, mt, x);
	//replace_rel(move(mt), p), set_priorities(p);
	if (bcqc) print(o::out()<<L"after cqc, "
		<<p.size()<< L" rules."<<endl, p);
	if (optimize) bdd::gc();

	// BLTINS: set order is important (and wrong) for e.g. REL, BLTIN, EQ
	map<term, set<term_set>> m;
	for (const auto& x : p)
		if (x.size() == 1) m[x[0]] = {};
		else m[x[0]].insert(term_set(x.begin() + 1, x.end()));
	set<rule> rs;
	varmap::const_iterator it;
	set<alt*, ptrcmp<alt>>::const_iterator ait;
	alt* aa;
	//map<ntable, size_t> altids;
	// TODO: maybe we shouldn't clear? as altids are for all progs
	// TEST: this w/ addbit and multiple progs, might not work
	infer.altordermap.clear();
	for (pair<term, set<term_set>> x : m) {
		const term& t = x.first;
		if (x.second.empty()) {
			// D: we need to process headers-only, for vars/types sync reasons.
			if (doemptyalts && t.nvars != 0)
				altids[t.tab]++;
			continue;
		}
		rule r;
		if (t.neg) datalog = false;
		tbls[t.tab].ext = false;
		varmap v;
		r.neg = t.neg, r.tab = t.tab, r.eq = htrue, r.t = t;
		// D: r.eq is rule bdd, i.e. header/term bdd, i.e. table bdd (and bm).
		// TODO: we might want to keep tbl/alt/bm attached to bdd-s? (to DBG)
		DBG(assert(t.tab != -1););
		table& tbl = tbls[t.tab];
		for (size_t n = 0; n != t.size(); ++n) {
			if (t[n] >= 0) { 
				if (t.types[n].isPrimitive())
					get_sym(t[n], n, t.size(), r.eq, tbl.bm);
				else if (t.types[n].isCompound())
					get_sym(t.compvals[n], n, t.size(), r.eq, tbl.bm);
				else throw 0; // not implemented exception or something
			}
			else if (v.end()==(it=v.find(t[n]))) v.emplace(t[n], n);
			else r.eq = r.eq && from_sym_eq(n, it->second, t.size(), tbl);
		}
		set<pair<alt,size_t>, altpaircmp> as; //set<alt> as;
		r.len = t.size();
		size_t& n = altids[t.tab], altstart = n;
		for (const term_set& al : x.second)
			get_alt(al, t, as, n++);
		// sync alts w/ altsmap map/pointers (to have right bm for addbit)
		n = altstart;
		for (pair<alt, size_t> ax : as) {
			alt& a = ax.first;
			size_t altid = ax.second;
			DBG(assert(equal_types(tbl, a)););
			// alts are reordered and cached hence => altordermap and altsmap
			infer.altordermap.
				emplace(tbl_alt{ r.tab, altid }, tbl_alt{ r.tab, n });
			if ((ait = alts.find(&a)) != alts.end()) {
				DBG(assert(equal_types(tbl, **ait)););
				r.push_back(*ait);
				infer.altsmap[{r.tab, n}] = *ait;
			} else {
				*(aa = new alt) = a;
				infer.altsmap[{r.tab, n}] = aa;
				r.push_back(aa), alts.insert(aa);
			}
			for (ntable btbl : a.bodytbls)
				infer.tblbodies[btbl].insert({r.tab, n});
			n++;
		}
		rs.insert(r);
	}
	for (rule r : rs)
		tbls[r.t.tab].r.push_back(rules.size()), rules.push_back(r);
	sort(rules.begin(), rules.end(), [this](const rule& x, const rule& y) {
			return tbls[x.tab].priority > tbls[y.tab].priority; });

	infer.tblrules.clear();
	size_t i = 0;
	for (const rule& r : rules) {
		infer.tblrules[r.tab].insert(i++);
	}
}

/* we have to split load_string to pre-table-init and post-table-init */
vector<ntable> tables::init_string_tables(lexeme r, const wstring& s) {
	int_t rel = dict.get_rel(r);
	str_rels.insert(rel);
	const ints ar = {0,-1,-1,1,-2,-2,-1,1,-2,-1,-1,1,-2,-2};

	// just init these to be in the dict
	dict.get_sym(L"space");
	dict.get_sym(L"alpha");
	dict.get_sym(L"alnum");
	dict.get_sym(L"digit");
	dict.get_sym(L"printable");

	// D: we have all for get_table and we now need it before from_fact/from_sym
	ntable tab1 = get_table({rel, ar});
	ntable tab2 = get_table({rel, {3}});

	// it's {num, chr, num}
	table& tbl1 = tbls[tab1];
	size_t len = tbl1.len;
	DBG(assert(len == 3););
	argtypes types(len);
	//ints nums(len, 0);
	types[1] = arg_type{ base_type::CHR, 0 };
	//types[1] = arg_type{ base_type::CHR, 12 }; //should be 8
	types[0] = types[2] = arg_type{ base_type::INT, 0 };
	tbl1.bm.set_args(ints(len), types); // , nums);

	// it's {str, num, num}
	table& tbl2 = tbls[tab2];
	len = tbl2.len;
	DBG(assert(len == 3););
	types = argtypes(len);
	//nums = ints(len, 0);
	types[0] = arg_type{ base_type::STR, 0 };
	//types[0] = arg_type{ base_type::STR, 12 };
	types[1] = types[2] = arg_type{ base_type::INT, 0 };
	tbl2.bm.set_args(ints(len), types); // , nums);

	// do this or use _nums, whichever, this is better, _nums includes other?
	ints maxnums(len, 0);
	for (int_t n = 0; n != (int_t)s.size(); ++n) {
		maxnums[0] = maxnums[1] = max(maxnums[0], n);
		maxnums[2] = max(maxnums[2], n + 1);
	}

	types[1] = arg_type{ base_type::CHR, 0, 0 };
	//types[1] = arg_type{ base_type::CHR, 12 };
	//nums[1] = 0;
	types[0] = types[2] = 
		arg_type{ base_type::INT, 0, max(maxnums[0], maxnums[2]) };
	//nums[0] = nums[2] = max(maxnums[0], maxnums[2]);
	tbl1.bm.set_args(ints(len), types); // , nums);

	types[0] = arg_type{ base_type::STR, 0, 0 };
	//types[0] = arg_type{ base_type::STR, 12 };
	//nums[0] = 0;
	types[1] = types[2] = 
		arg_type{ base_type::INT, 0, max(maxnums[1], maxnums[2]) };
	//nums[1] = nums[2] = max(maxnums[1], maxnums[2]);
	tbl2.bm.set_args(ints(len), types); // , nums);

	tbl1.bm.init(dict);
	tbl2.bm.init(dict);

	return { tab1, tab2 };
}

void tables::load_string(
	lexeme, const std::wstring& s, const std::vector<ntable> tabs) 
{
	DBG(assert(tabs.size() == 2););
	ntable tab1 = tabs[0];
	ntable tab2 = tabs[1];
	table& tbl1 = tbls[tab1];
	table& tbl2 = tbls[tab2];
	DBG(assert(tbl1.len == 3 && tbl2.len == 3););

	const int_t sspace = dict.get_sym(L"space"),
		salpha = dict.get_sym(L"alpha"),
		salnum = dict.get_sym(L"alnum"),
		sdigit = dict.get_sym(L"digit"),
		sprint = dict.get_sym(L"printable");
	term t;
	bdd_handles b1, b2;
	b1.reserve(s.size()), b2.reserve(s.size()), t.resize(3);

	//static AddBits addBits{ *this };
	// to be removed: I've just added to test if this changes anything, nope
	tbl1.init_bits(tab1, addBits);
	tbl2.init_bits(tab2, addBits);
	b1.push_back(tbl1.tq);
	b2.push_back(tbl2.tq);

	for (int_t n = 0; n != (int_t)s.size(); ++n) {
		// a temp hack (to inject tab), do this properly, separate terms etc.
		t.tab = tab1;
		// just in case, not really needed, but we may in the future (expected?)
		t.types = tbl1.bm.types;
		//t.nums = tbl1.bm.nums;
		t[0] = mknum(n), t[1] = mkchr(s[n]), t[2] = mknum(n + 1);
		b1.push_back(from_fact(t));

		t.tab = tab2;
		t.types = tbl2.bm.types;
		//t.nums = tbl2.bm.nums;
		t[1] = t[0];
		// this could be multiple entries? else if? if not simplify
		if (iswspace(s[n])) 
			t[0] = sspace, b2.push_back(from_fact(t));
		if (iswdigit(s[n])) 
			t[0] = sdigit, b2.push_back(from_fact(t));
		if (iswalpha(s[n])) 
			t[0] = salpha, b2.push_back(from_fact(t));
		if (iswalnum(s[n])) 
			t[0] = salnum, b2.push_back(from_fact(t));
		if (iswprint(s[n])) 
			t[0] = sprint, b2.push_back(from_fact(t));
	}
	clock_t start, end;
	if (optimize)
		(o::ms()<<"# load_string or_many: "),
		measure_time_start();
	// D: move get_table above, we now need table for all bdd ops (from_sym)
	tbl1.tq = bdd_or_many(move(b1)),
	tbl2.tq = bdd_or_many(move(b2));

	if (optimize) measure_time_end();
}

/*
 this is alternative impl which creates facts as for any  other tbl, test it
*/
//set<term> tables::load_string(lexeme r, const wstring& s) {
//	int_t rel = dict.get_rel(r);
//	str_rels.insert(rel);
//	const ints ar = { 0,-1,-1,1,-2,-2,-1,1,-2,-1,-1,1,-2,-2 };
//
//	// D: we have all for get_table and we now need it before from_fact/from_sym
//	ntable tab1 = get_table({ rel, ar });
//	ntable tab2 = get_table({ rel, {3} });
//
//	// it's {num, chr, num}
//	table& tbl1 = tbls[tab1];
//	size_t len = tbl1.len;
//	DBG(assert(len == 3););
//	argtypes types(len);
//	ints nums(len, 0);
//	//types[1] = arg_type{ base_type::CHR, 10 }; //should be 8
//	types[1] = arg_type{ base_type::CHR, 0 };
//	types[0] = types[2] = arg_type{ base_type::INT, 0 };
//	//nums[0] = nums[2] = _nums; // just to recheck
//	tbl1.bm.set_args(ints(len), types, nums);
//
//	// it's {str, num, num}
//	table& tbl2 = tbls[tab2];
//	len = tbl2.len;
//	DBG(assert(len == 3););
//	types = argtypes(len);
//	nums = ints(len, 0);
//	//types[1] = arg_type{ base_type::CHR, 10 }; //should be 8
//	types[0] = arg_type{ base_type::STR, 0 };
//	types[1] = types[2] = arg_type{ base_type::INT, 0 };
//	//nums[1] = nums[2] = _nums; // just to recheck
//	tbl2.bm.set_args(ints(len), types, nums);
//
//	// do this or use _nums, whichever, this is better, _nums includes other?
//	ints maxnums(len, 0);
//	for (int_t n = 0; n != (int_t)s.size(); ++n) {
//		maxnums[0] = maxnums[1] = max(maxnums[0], n);
//		maxnums[2] = max(maxnums[2], n + 1);
//	}
//
//	types[1] = arg_type{ base_type::CHR, 0 };
//	types[0] = types[2] = arg_type{ base_type::INT, 0 };
//	nums[1] = 0;
//	//nums[1] = nums[2] = _nums; // just to recheck
//	//nums[0] = maxnums[0];
//	//nums[2] = maxnums[2];
//	nums[0] = nums[2] = max(maxnums[0], maxnums[2]);
//	tbl1.bm.set_args(ints(len), types, nums);
//
//	types[0] = arg_type{ base_type::STR, 0 };
//	types[1] = types[2] = arg_type{ base_type::INT, 0 };
//	nums[0] = 0;
//	//nums[1] = nums[2] = _nums; // just to recheck
//	//nums[1] = maxnums[1];
//	//nums[2] = maxnums[2];
//	nums[1] = nums[2] = max(maxnums[1], maxnums[2]);
//	tbl2.bm.set_args(ints(len), types, nums);
//
//	tbl1.bm.init(dict);
//	tbl2.bm.init(dict);
//
//	const int_t sspace = dict.get_sym(L"space"),
//		salpha = dict.get_sym(L"alpha"),
//		salnum = dict.get_sym(L"alnum"),
//		sdigit = dict.get_sym(L"digit"),
//		sprint = dict.get_sym(L"printable");
//	set<term> facts;
//	//term t;
//	ints t;
//	t.resize(3);
//
//	for (int_t n = 0; n != (int_t)s.size(); ++n) {
//		//// a temp hack (to inject tab), do this properly, separate terms etc.
//		//t.tab = tab1;
//		//// just in case, not really needed, but we may in the future (expected?)
//		//t.types = tbl1.bm.types;
//		//t.nums = tbl1.bm.nums;
//		t[0] = mknum(n), t[1] = mkchr(s[n]), t[2] = mknum(n + 1);
//		facts.insert(to_tbl_term(tab1, t, tbl1.bm.types, tbl1.bm.nums));
//		//get_nums(x);
//
//		//b1.push_back(from_fact(t));
//
//		//t.tab = tab2;
//		//t.types = tbl2.bm.types;
//		//t.nums = tbl2.bm.nums;
//		t[1] = t[0];
//		// this could be multiple entries? else if? if not simplify
//		if (iswspace(s[n])) {
//			t[0] = sspace;
//			facts.insert(to_tbl_term(tab2, t, tbl2.bm.types, tbl2.bm.nums));
//			//b2.push_back(from_fact(t));
//		}
//		if (iswdigit(s[n])) {
//			t[0] = sdigit;
//			facts.insert(to_tbl_term(tab2, t, tbl2.bm.types, tbl2.bm.nums));
//			//b2.push_back(from_fact(t));
//		}
//		if (iswalpha(s[n])) {
//			t[0] = salpha;
//			facts.insert(to_tbl_term(tab2, t, tbl2.bm.types, tbl2.bm.nums));
//			//b2.push_back(from_fact(t));
//		}
//		if (iswalnum(s[n])) {
//			t[0] = salnum;
//			facts.insert(to_tbl_term(tab2, t, tbl2.bm.types, tbl2.bm.nums));
//			//b2.push_back(from_fact(t));
//		}
//		if (iswprint(s[n])) {
//			t[0] = sprint;
//			facts.insert(to_tbl_term(tab2, t, tbl2.bm.types, tbl2.bm.nums));
//			//b2.push_back(from_fact(t));
//		}
//	}
//	return facts;
//}

/*template<typename T> bool subset(const set<T>& small, const set<T>& big) {
	for (const T& t : small) if (!has(big, t)) return false;
	return true;
}*/

void tables::get_var_ex(
	size_t arg, size_t args, bools& vbs, c_bitsmeta& bm) { // const 
	size_t bits = bm.types[arg].get_bits();
	for (size_t b = 0; b != bits; ++b) vbs[bm.pos(b, arg, args)] = true;
}

void tables::get_sym(
	size_t arg, size_t args, const arg_type& type, 
	int_t val, ints vals, spbdd_handle& r, c_bitsmeta& bm) const
{
	if (type.isPrimitive())
		get_sym(val, arg, args, r, bm);
	else if (type.isCompound())
		get_sym(vals, arg, args, r, bm);
	else throw 0; // not implemented exception or something
}

// D: only called from get_rules, arg/args is rule header term's (i.e. =>table).
void tables::get_sym(
	int_t val, size_t arg, size_t args, spbdd_handle& r, c_bitsmeta& bm) const{
	// TODO: this needs Compound version
	if (!bm.types[arg].isPrimitive()) throw 0;
	size_t bits = bm.types[arg].primitive.bitness;// .get_bits();
	for (size_t b = 0; b != bits; ++b)
		r = r && bm.from_bit_re(b, bits, arg, args, val); // from_bit
}

void tables::get_sym(
	ints vals, size_t arg, size_t args, spbdd_handle& r, c_bitsmeta& bm) const {
	if (!bm.types[arg].isCompound()) throw 0;
	const primtypes& types = bm.types[arg].compound.types;
	if (types.size() != vals.size()) throw 0;
	size_t startbit = 0;
	for (size_t i = 0; i != types.size(); ++i) {
		const primitive_type& type = types[i];
		int_t val = vals[i];
		size_t bits = type.bitness;
		// bits are 'per compound-arg' (used to encode the val only)
		for (size_t b = 0; b != bits; ++b)
			r = r && ::from_bit(
				bm.pos(startbit + b, arg, args), 
				val & (1 << bm.bit(b, bits)));
			//r = r && bm.from_bit_re(startbit + b, bits, arg, args, val);
		// don't put bit() on both const/encode and pos(), either or.
		startbit += type.bitness;
	}
}

ntable tables::get_table(const sig& s) {
	auto it = smap.find(s);
	if (it != smap.end()) return it->second;
	ntable nt = tbls.size();
	size_t len = sig_len(s);
	max_args = max(max_args, len);
	// a proper ctor for table to init bm
	table tb(s, len, dict);
	return tbls.push_back(tb), smap.emplace(s, nt), nt;
	//return	tb.tq = hfalse, tb.s = s, tb.len = len,
	//	tbls.push_back(tb), smap.emplace(s,nt), nt;
}

term to_nums(term t) {
	for (int_t& i : t)  if (i > 0) i = mknum(i);
	return t;
}

//term from_nums(term t) {
//	for (int_t& i : t)  if (i > 0) i >>= 2;
//	return t;
//}

vector<term> to_nums(const vector<term>& v) {
	vector<term> r;
	for (const term& t : v) r.push_back(to_nums(t));
	return r;
}

//set<term> from_nums(const set<term>& s) {
//	set<term> ss;
//	for (const term& t : s) ss.insert(from_nums(t));
//	return ss;
//}

void to_nums(flat_prog& m) {
	flat_prog mm;
	for (auto x : m) mm.insert(to_nums(x));
	m = move(mm);
}

ntable tables::get_new_tab(int_t x, ints ar) { return get_table({ x, ar }); }

void tables::transform_grammar(vector<production> g, flat_prog& p) {
	if (g.empty()) return;
//	o::out()<<"grammar before:"<<endl;
//	for (production& p : g) o::out() << p << endl;
	for (size_t k = 0; k != g.size();) {
		if (g[k].p.size() < 2) parse_error(err_empty_prod, g[k].p[0].e);
		size_t n = 0;
		while (n < g[k].p.size() && g[k].p[n].type != elem::ALT) ++n;
		if (n == g[k].p.size()) { ++k; continue; }
		g.push_back({vector<elem>(g[k].p.begin(), g[k].p.begin()+n)});
		g.push_back({vector<elem>(g[k].p.begin()+n+1, g[k].p.end())});
		g.back().p.insert(g.back().p.begin(), g[k].p[0]);
		g.erase(g.begin() + k);
	}
//	o::out()<<"grammar after:"<<endl;
//	for (production& p : g) o::out() << p << endl;
	for (production& p : g)
		for (size_t n = 0; n < p.p.size(); ++n)
			if (p.p[n].type == elem::STR) {
				lexeme l = p.p[n].e;
				p.p.erase(p.p.begin() + n);
				bool esc = false;
				for (cws s = l[0]+1; s != l[1]-1; ++s)
					if (*s == L'\\' && !esc) esc = true;
					else p.p.insert(p.p.begin() + n++,
						elem(*s)), esc = false;
			}
	vector<term> v;
	static const set<wstring> b =
		{ L"alpha", L"alnum", L"digit", L"space", L"printable" };
	set<lexeme, lexcmp> builtins;
	for (const wstring& s : b) builtins.insert(dict.get_lexeme(s));

	// TODO: we set tbls from t-s, tbls/types change in get_types, update back?
	for (const production& x : g) {
		if (x.p.size() == 2 && x.p[1].e == L"null") {
			term t;
			t.resize(2);
			t[0] = t[1] = -1;
			// it's some rel(var var), and w/ null, means negated? (post proc.)
			t.tab = get_table({dict.get_rel(x.p[0].e),{2}});
			// TODO: just some basic init, make it better
			table& tbl = tbls[t.tab];
			//size_t len = t.size(); // tbl.len
			tbl.bm.init(dict);
			t.types = tbl.bm.types; // , t.nums = ints(len, 0);
			vector<term> v{t, t};
			v[0].neg = true;
			align_vars(v);
			prog_after_fp.insert(move(v));
			p.insert({move(t)});
			continue;
		}
		for (int_t n = 0; n != (int_t)x.p.size(); ++n) {
			term t;
			if (builtins.find(x.p[n].e) != builtins.end()) {
				// it's {sym, num, num} (tbl2 of str_rels or str often)
				// nums will be figured out by facts set up during load_string
				t.tab = get_table({*str_rels.begin(), {3}});
				t.resize(3), t[0] = dict.get_sym(x.p[n].e),
				t[1] = -n, t[2] = -n-1;
				table& tbl = tbls[t.tab];
				size_t len = t.size(); // tbl.len
				t.types = argtypes(len); // , t.nums = ints(len, 0);
				//t.types[0] = arg_type{ base_type::STR, 10 }; //bsr(nsyms())
				t.types[0] = arg_type{ base_type::STR, 0 }; //bsr(dict.nsyms())
				t.types[1] = t.types[2] = arg_type{ base_type::INT, 0 };
				tbl.bm.set_args(ints(len), t.types); // , t.nums);
				tbl.bm.init(dict);
			} else if (x.p[n].type == elem::SYM) {
				// it's just some rel(var var), types to be inferred from facts
				t.resize(2);
				t.tab = get_table({dict.get_rel(x.p[n].e),{2}});
				if (n) t[0] = -n, t[1] = -n-1;
				else t[0] = -1, t[1] = -(int_t)(x.p.size());
				// TODO: just some basic init, make it better
				// we can't infer any types here (seems), vars'll connect later
				table& tbl = tbls[t.tab];
				//size_t len = t.size(); // tbl.len
				tbl.bm.init(dict);
				t.types = tbl.bm.types; // , t.nums = ints(len, 0);
			} else if (x.p[n].type == elem::CHR) {
				// it's {num, chr, num} (the 1st str_rels table w/ funny sig/ar)
				t.resize(3);
				if (str_rels.size() > 1) er(err_one_input);
				if (str_rels.empty()) continue;
				// D: this assumes that dict.get_rel and tab are the same
				t.tab = *str_rels.begin();
				t[0] = -n, t[2] = -n-1,
				t[1] = mkchr((unsigned char)(x.p[n].ch));
				table& tbl = tbls[t.tab];
				size_t len = t.size(); // tbl.len
				t.types = argtypes(len); // , t.nums = ints(len, 0);
				//t.types[1] = arg_type{ base_type::CHR, 10 }; //should be 8
				t.types[1] = arg_type{ base_type::CHR, 0 };
				t.types[0] = t.types[2] = arg_type{ base_type::INT, 0 };
				tbl.bm.set_args(ints(len), t.types); // , t.nums);
				tbl.bm.init(dict);
			} else throw runtime_error(
				"Unexpected grammar element");
			v.push_back(move(t));
		}
		p.insert(move(v));
	}
	DBG(print(o::dbg() << L"transformed grammar: " << endl, p);)
	DBG(print(o::dbg() << L"run after transform: " << endl, prog_after_fp);)
}

void tables::add_prog(const raw_prog& p, const strs_t& strs_) {
	strs = strs_;
	// D: this might be an issue now, these 'args' are global, 
	// we don't have that now, arg should be only 'counted' if in term/tbl/alt
	// explained: it's not global, it's only for str_rels tables, so it's fine?
	if (!strs.empty()) {
		// D: just temp to recheck initial universe for str_rels tbls
		//_chars = 255;
		dict.get_sym(dict.get_lexeme(L"space"));
		dict.get_sym(dict.get_lexeme(L"alpha"));
		dict.get_sym(dict.get_lexeme(L"alnum"));
		dict.get_sym(dict.get_lexeme(L"digit"));
		dict.get_sym(dict.get_lexeme(L"printable"));
	}

	// D: turned chars, nums off as we don't have them like this any more
	// D: just temp to recheck initial universe for str_rels tbls
	//for (auto x : strs) _nums = max(_nums, (int_t)x.second.size()+1);

	add_prog(to_terms(p), p.g);
}

bool tables::run_nums(flat_prog m, set<term>& r, size_t nsteps) {
	map<ntable, ntable> m1, m2;
	auto f = [&m1, &m2](ntable *x) {
		auto it = m1.find(*x);
		if (it != m1.end()) return *x = it->second;
		const int_t y = (int_t)m2.size();
		m1.emplace(*x, y), m2.emplace(y, *x);
		return *x = y;
	};
	auto g = [&m2](const set<term>& s) {
		set<term> r;
		for (term t : s) {
			auto it = m2.find(t.tab);
			if (it == m2.end()) r.insert(t);
			else t.tab = it->second, r.insert(t);
		}
		return r;
	};
	auto h = [this, f](const set<term>& s) {
		set<term> r;
		for (term t : s)
			get_table({ f(&t.tab), {(int_t)t.size()}}), r.insert(t);
		return r;
	};
	flat_prog p;
	for (vector<term> x : m) {
		get_table({ f(&x[0].tab), { (int_t)x[0].size() } });
		auto s = h(set<term>(x.begin() + 1, x.end()));
		x.erase(x.begin() + 1, x.end()),
		x.insert(x.begin() + 1, s.begin(), s.end()), p.insert(x);
	}
//	DBG(print(o::out()<<L"run_nums for:"<<endl, p)<<endl<<L"returned:"<<endl;)
	add_prog(move(p), {});
	if (!pfp(nsteps)) return false;
	r = g(decompress());
	return true;
}

void tables::add_tml_update(const term& t, bool neg) {
	//static nlevel lnstep = -1;
	static size_t lnrels = -1;
	// ::STR is always BitScanR(dict.nsyms()), all syms share one universe still
	// just say '0' and it'll calc automatically (STR, CHR), INT too if you have 
	// nums set
	static arg_type rel_type, nstep_type{ base_type::INT, 2 },
		add_del_type{ base_type::STR, 0 }; // BitScanR(max(sym_add, sym_del)) };
	//ints nums(3, 0);
	ints args{ mknum(nstep), (neg ? sym_del : sym_add),
		dict.get_sym(dict.get_rel(tbls[t.tab].s.first)) };
	//if (nstep != lnstep) lnstep = nstep, nstep_type =
	//	arg_type{ base_type::INT, bitsmeta::BitScanR(nstep+1) };
	if (dict.nrels() != lnrels) lnrels = dict.nrels(),
		rel_type = arg_type{ base_type::STR, 0 }; // BitScanR(lnrels)};
	argtypes types{ nstep_type, add_del_type, rel_type };
	types.insert(types.end(), t.types.begin(), t.types.end());
	//nums .insert(nums .end(), t.nums .begin(), t.nums .end());
	args .insert(args .end(), t      .begin(), t      .end());
	ints arity = tbls.at(t.tab).s.second; arity[0] += 3;
	ntable maxtab=tbls.size()-1, tab = get_table({ rel_tml_update, arity });
	table& tbl = tbls.at(tab);
	term nt(false, tab, args, vector<ints>(types.size()), types, 0, -1, 0);
	//static AddBits addBits{ *this };
	if (tab > maxtab) { // new table. init, set args (types) and dumptype
		tbl.bm.set_args(ints(nt.size(), 0), nt.types); // , ints(nt.size()));
		tbl.bm.init(dict);
		// tbl.init_bits is the last thing, then bdd op-s can start
		tbl.init_bits(tab, addBits);
		if (dumptype) o::dump() << dict.get_rel(tbl.s.first) << L"("
			<< tbl.bm.types << L")" << endl;
	}
	tbl.add.push_back(from_fact(nt));
}

wostream& tables::decompress_update(wostream& os, spbdd_handle& x, const rule& r) {
	if (print_updates) print(os << L"# ", r) << L"\n# \t-> ";
	decompress(x, r.tab, [&os, &r, this](const term& x) {
		if (print_updates)
			os << (r.neg ? L"~" : L"") << to_raw_term(x) << L". ";
		if (populate_tml_update) add_tml_update(x, r.neg);
	});
	if (print_updates) os << endl;
	return os;
}

void tables::init_tml_update() {
	rel_tml_update = dict.get_rel(L"tml_update");
	sym_add        = dict.get_sym(L"add");
	sym_del        = dict.get_sym(L"delete");
}

void tables::add_prog(flat_prog m, const vector<production>& g, bool mknums) {
	smemo.clear(), ememo.clear(), leqmemo.clear();
	if (mknums) to_nums(m);
	if (populate_tml_update) init_tml_update();
	rules.clear(), datalog = true;

	//// for to recheck the initial empty universe and str_rels (grammar, dyck)
	//_syms = dict.nsyms();
	////while (max(max(_nums, _chars), _syms) >= (1 << (_bits - 2))) ++_bits;
	//while (max(max(_nums, _chars), _syms) >= (1 << _bits)) ++_bits;

	// only one string is supported (transform_grammar), make this map if more
	vector<ntable> strtabs;
	DBG(assert(strs.size() <= 1););
	
	if (autotype) {
		// tables are already in place from from_raw_term or later in grammar
		// just init string tables, types first, no bdd-s, facts etc.
		for (auto x : strs) 
			strtabs = init_string_tables(x.first, x.second);
		//// this is load_string which adds all str stuff as proper facts
		//for (auto x : strs)
		//	for (const term& t : load_string(x.first, x.second)) 
		//		m.insert({t});
		transform_grammar(g, m);

		// init tables before hand, to make facts count e.g. find bits from nums
		for (auto& tbl : tbls) tbl.bm.init(dict);

		// inference has to be a member as we need 1 instance for multiple progs
		// (we could've inference service passed to tables add_prog from driver)
		// map/sync types (type inference), find matching and root types etc.
		infer.get_types(m);
		infer.propagate_types();

		// just check tables, catch any new type/bit sync/map changes (new prog)
		for (size_t tab = 0; tab < tbls.size(); ++tab)
			if (tbls[tab].bm.bits_changed())
				tbls[tab].bm.bitsfixed = false; // 'un-fix' the bits, for addbit

		// init tables now, as types are done...
		//// this is for load_string which adds all str stuff as proper facts
		//init_bits();
		range_clear_memo();
		// ...now we can load string
		for (auto x : strs)
			load_string(x.first, x.second, strtabs);
		for (size_t tab = 0; tab < tbls.size(); ++tab)
			if (strs.empty() || !hasf(strtabs, tab))
				tbls[tab].init_bits(tab, addBits);

		// ...and init alt-s/bm-s as well (will include empty alts, redundant)
		for (auto& akeyval : infer.altstyped) { // will be empty if no autotype
			alt& a = akeyval.second;
			a.bm.init(dict); // this should be enough?
			// to 'fix' the bits (any changes to be recorded for add_bits later)
			// irrelevant for alts but we still have to do it cause of bm-s
			a.bm.init_bits();
			// alt-s are copied / reused later in get_alt
		}
	} else {
		// TODO: this wasn't tested, -autotype is on by default
		for (auto x : strs)
			strtabs = init_string_tables(x.first, x.second);
		//set<term> facts = load_string(x.first, x.second);
		//for (const term& t : facts) m.insert({ t });
		//for (auto x : strs)
		//	for (const term& t : load_string(x.first, x.second))
		//		m.insert({ t });
		transform_grammar(g, m);
		//init_bits();
		range_clear_memo();
		for (auto x : strs)
			load_string(x.first, x.second, strtabs);
		for (size_t tab = 0; tab < tbls.size(); ++tab)
			if (size_t(strtabs[0]) != tab && size_t(strtabs[1]) != tab)
				tbls[tab].init_bits(tab, addBits);
	}

	if (dumptype) {
		for (size_t tab = 0; tab < tbls.size(); ++tab) {
			wstring name = lexeme2str(dict.get_rel(tbls.at(tab).s.first));
			//o::dump() << name << L"(" << tbls[tab].bm << L")" << endl;
			o::dump() << name << L"(" << tbls[tab].bm.types << L")" << endl;
		}
	}

	get_rules(move(m));

//	clock_t start, end;
//	o::dbg()<<"load_string: ";
//	measure_time_start();
//	measure_time_end();
	if (optimize) bdd::gc();
}

xperm tables::deltail(const bitsmeta& abm, const bitsmeta& tblbm) {
	size_t args = abm.get_args();
	size_t newargs = tblbm.get_args();
	bools ex(abm.args_bits, false);
	uints perm = perm_init(abm.args_bits); // abm.perm_init();
	for (size_t n = 0; n != args; ++n)
		for (size_t k = 0; k != abm.get_bits(n); ++k)
			if (n >= newargs) ex[abm.pos(k, n, args)] = true;
			else perm[abm.pos(k, n, args)] = tblbm.pos(k, n, newargs);
	// permute is not applied right away, rather saved into alt ex/perm
	return { ex, perm };
}
/*
shrinks from alt to tbl domain/bits (temp right-side args are being removed)
(TODO: args/newargs are not needed)
*/
xperm tables::deltail(size_t args, size_t newargs,
	const bitsmeta& abm, const bitsmeta& tblbm) const {
	DBG(assert(args == abm.get_args()););
	DBG(assert(newargs == tblbm.get_args()););
	// args * bits => bm.args_bits
	bools ex(abm.args_bits, false); 
	uints perm = perm_init(abm.args_bits); // abm.perm_init();
	for (size_t n = 0; n != args; ++n)
		for (size_t k = 0; k != abm.get_bits(n); ++k)
			if (n >= newargs) ex[abm.pos(k, n, args)] = true;
			else perm[abm.pos(k, n, args)] = tblbm.pos(k, n, newargs);
	// permute is not applied right away, rather saved into alt ex/perm
	return { ex, perm };
}

/*
expands from header/rule/tbl into alt domain/bits
(TODO: args/newargs are not needed)
*/
uints tables::addtail(size_t args, size_t newargs,
	const bitsmeta& tblbm, const bitsmeta& abm) const{
	DBG(assert(args == tblbm.get_args()););
	DBG(assert(newargs == abm.get_args()););
	// args * bits => tblbm.args_bits
	uints perm = perm_init(tblbm.args_bits); // tblbm.perm_init();
	for (size_t n = 0; n != args; ++n)
		for (size_t k = 0; k != tblbm.get_bits(n); ++k)
			perm[tblbm.pos(k, n, args)] = abm.pos(k, n, newargs);
	// D: shouldn't we fill in the 'blanks' (i.e. 0- the new bits)
	return perm;
}

/* 
expands from header/rule/tbl into alt domain/bits 
(TODO: args/newargs are not needed)
*/
spbdd_handle tables::addtail(cr_spbdd_handle x, size_t args, size_t newargs,
	const bitsmeta& tblbm, const bitsmeta& abm) const{
	DBG(assert(args == tblbm.get_args()););
	DBG(assert(newargs == abm.get_args()););
	if (args == newargs) return x;
	// permute is applied right away
	//operator^(x, addtail(args, newargs, tblbm, abm));
	return x ^ addtail(args, newargs, tblbm, abm);
}

spbdd_handle tables::body_query(body& b, size_t /*DBG(len)*/) {
//	if (b.a) return alt_query(*b.a, 0);
//	if (b.ext) return b.q;
//	DBG(assert(bdd_nvars(b.q) <= b.ex.size());)
//	DBG(assert(bdd_nvars(get_table(b.tab, db)) <= b.ex.size());)
	if (b.tlast && b.tlast->b == tbls[b.tab].tq->b) return b.rlast;
	b.tlast = tbls[b.tab].tq;
	return b.rlast = (b.neg ? bdd_and_not_ex_perm : bdd_and_ex_perm)
		(b.q, tbls[b.tab].tq, b.ex, b.perm, tbls[b.tab].bm.vbits);
//	DBG(assert(bdd_nvars(b.rlast) < len*bits);)
//	if (b.neg) b.rlast = bdd_and_not_ex_perm(b.q, ts[b.tab].tq, b.ex,b.perm);
//	else b.rlast = bdd_and_ex_perm(b.q, ts[b.tab].tq, b.ex, b.perm);
//	return b.rlast;
//	return b.rlast = bdd_permute_ex(b.neg ? b.q % ts[b.tab].tq :
//			(b.q && ts[b.tab].tq), b.ex, b.perm);
}

auto handle_cmp = [](const spbdd_handle& x, const spbdd_handle& y) {
	return x->b < y->b;
};

spbdd_handle tables::alt_query(alt& a, size_t /*DBG(len)*/) {
/*	spbdd_handle t = htrue;
	for (auto x : a.order) {
		bdd_handles v1;
		v1.push_back(t);
		for (auto y : x.first) v1.push_back(body_query(*a[y]));
		t = bdd_and_many(move(v1)) / x.second;
	}
	v.push_back(a.rlast = deltail(t && a.rng, a.varslen, len));*/
//	DBG(bdd::gc();)
	bdd_handles v1 = { a.rng, a.eq };
	spbdd_handle x;
	//DBG(assert(!a.empty());)

	for (size_t n = 0; n != a.size(); ++n)
		if (hfalse == (x = body_query(*a[n], a.varslen))) {
			a.insert(a.begin(), a[n]), a.erase(a.begin() + n + 1);
			return hfalse;
		} else v1.push_back(x);

	if (a.idbltin > -1) {
		lexeme bltintype = dict.get_bltin(a.idbltin);
		int_t bltinout = a.bltinargs.back(); // for those that have ?out

		// for bitwise and pairwise operators that take bdds as inputs
		// these bdds are result of body query executed above
		std::vector<int_t> bltininputs;
		for(size_t i = 0; i < a.bltinargs.size(); i++) {
			if (a.bltinargs[i] < 0) bltininputs.push_back(a.bltinargs[i]);
		}

		if (bltintype == L"count") {
			body& b = *a[a.size() - 1];
			// old, official satcount algorithm, improved, hopefully works?
			int_t cnt = bdd::satcount_k(x->b, b.ex, b.perm);

			//// this doesn't now work well, too slow?? off
			// new satcount based on the adjusted allsat_cb::sat (decompress)
			//if (b.inv.empty()) b.init_perm_inv(a.bm.args_bits); // b.inv =
			//int_t cnt = bdd::satcount(x, b.inv);

			// just equate last var (output) with the count
			x = from_sym(a.vm.at(bltinout), a.varslen, mknum(cnt), a.bm);
			v1.push_back(x);
			o::dbg() << L"alt_query (cnt):" << cnt << L"" << endl;
		}
		else if (bltintype == L"rnd") {
			DBG(assert(a.bltinargs.size() == 3););
			// TODO: check that it's num const
			int_t arg0 = int_t(un_mknum(a.bltinargs[0]));
			int_t arg1 = int_t(un_mknum(a.bltinargs[1]));
			if (arg0 > arg1) swap(arg0, arg1);

			//int_t rnd = arg0 + (std::rand() % (arg1 - arg0 + 1));
			std::random_device rd;
			std::mt19937 gen(rd());
			std::uniform_int_distribution<> distr(arg0, arg1);
			int_t rnd = distr(gen);

			x = from_sym(a.vm.at(bltinout), a.varslen, mknum(rnd), a); // .bm);
			v1.push_back(x);
			o::dbg() << L"alt_query (rnd):" << rnd << L"" << endl;
		}
		else if (bltintype == L"print") {
			wstring ou{L"output"};
			size_t n{0};
			// D: args are now [0,1,...] (we no longer have the bltin as 0 arg)
			if (a.bltinargs.size() >= 2) {
				++n;
				// TODO: make this work for compounds, other? if it makes sense?
				if (a.bm.types[0].isPrimitive()) {
					switch (a.bm.types[0].primitive.type) {
						case base_type::STR:
							// D: get_sym no longer handles ints/chrs, just syms. 
							ou = lexeme2str(dict.get_sym(a.bltinargs[0]));
							break;
						case base_type::CHR:
						case base_type::INT:
						default: throw 0;
					}
				}
				//ou = lexeme2str(dict.get_sym(a.bltinargs[0]));
			}
			wostream& os = output::to(ou);
			do {
				int_t arg = a.bltinargs[n++];
				if      (arg < 0) os << get_var_lexeme(arg) << endl;
				else if (arg & 1) os << (wchar_t)un_mknum(arg);
				else if (arg & 2) os << (int_t)  un_mknum(arg);
				else              os << dict.get_sym(arg);
			} while (n < a.bltinargs.size());
		}
		// D: turned off till this is reworked for varbits
		//else if (t_arith_op op = get_bwop(bltintype); op != t_arith_op::NOP) {
		//	size_t arg0_id = a.vm.at(bltininputs[0]);
		//	size_t arg1_id = a.vm.at(bltininputs[1]);
		//	spbdd_handle arg0 = v1[2];
		//	spbdd_handle arg1 = v1[3];
		//	x = bitwise_handler(arg0_id, arg1_id, a.vm.at(bltinout),
		//						arg0, arg1, a.varslen, op);
		//	v1.push_back(x);
		//}
		//else if (t_arith_op op = get_pwop(bltintype); op != t_arith_op::NOP) {
		//	size_t arg0_id = a.vm.at(bltininputs[0]);
		//	size_t arg1_id = a.vm.at(bltininputs[1]);
		//	spbdd_handle arg0 = v1[2];
		//	spbdd_handle arg1 = v1[3];
		//	x = pairwise_handler(arg0_id, arg1_id, a.vm.at(bltinout),
		//						 arg0, arg1, a.varslen, op);
		//	v1.push_back(x);
		//}
	}

	sort(v1.begin(), v1.end(), handle_cmp);
	if (v1 == a.last) return a.rlast;// { v.push_back(a.rlast); return; }
	//bdd::cleancache();
	if (!bproof) {
		a.rlast =
			bdd_and_many_ex_perm(a.last = move(v1), a.ex, a.perm, a.bm.vbits);
		return a.rlast;
	}
	a.levels.emplace(nstep, x = bdd_and_many(v1));
//	if ((x = bdd_and_many_ex(a.last, a.ex)) != hfalse)
//		v.push_back(a.rlast = x ^ a.perm);
//	bdd_handles v;
	a.rlast = bdd_permute_ex(x, a.ex, a.perm, a.bm.vbits);
	return a.rlast;

//	if ((x = bdd_and_many_ex_perm(a.last, a.ex, a.perm)) != hfalse)
//		v.push_back(a.rlast = x);
//	return x;
//	DBG(assert(bdd_nvars(a.rlast) < len*bits);)
}

bool table::commit(DBG(size_t /*bits*/)) {
	if (add.empty() && del.empty()) return false;
	spbdd_handle x;
	if (add.empty()) x = tq % bdd_or_many(move(del));
	else if (del.empty()) add.push_back(tq), x = bdd_or_many(move(add));
	else {
		spbdd_handle a = bdd_or_many(move(add)),
				 d = bdd_or_many(move(del)), s = a % d;
//		DBG(assert(bdd_nvars(a) < len*bits);)
//		DBG(assert(bdd_nvars(d) < len*bits);)
		if (s == hfalse) return unsat = true;
		x = (tq || a) % d;
	}
//	DBG(assert(bdd_nvars(x) < len*bits);)
	return x != tq && (tq = x, true);
}

char tables::fwd() noexcept {
	for (rule& r : rules) {
		bdd_handles v(r.size());
		for (size_t n = 0; n != r.size(); ++n)
			v[n] = alt_query(*r[n], r.len);
		spbdd_handle x;
		if (v == r.last) { if (datalog) continue; x = r.rlast; }
		// applying the r.eq and or-ing all alt-s
		else r.last = v, x = r.rlast = bdd_or_many(move(v)) && r.eq;
//		DBG(assert(bdd_nvars(x) < r.len*bits);)
		if (x == hfalse) continue;
		(r.neg ? tbls[r.tab].del : tbls[r.tab].add).push_back(x);
		if (print_updates || populate_tml_update)
			decompress_update(o::inf(), x, r);
	}
	bool b = false;
	// header builtins support: this tracks if any recent changes/commits
	for (ntable tab = 0; (size_t)tab != tbls.size(); ++tab) {
		table& tbl = tbls[tab];
		bool changes = tbl.commit(DBG(0)); // bits));
		b |= changes;

		//if (tbl.unsat) return unsat = true;
		//continue;

		//if (!changes && tbl.idbltin > -1) {
		//if (tbl.idbltin > -1) {
		if (changes && tbl.idbltin > -1) {
			//lexeme bltintype = dict.get_bltin(tbl.idbltin);
			set<term>& ts = mhits[tab];
			bool ishalt = false, isfail = false;
			decompress(tbl.tq, tab, [&ts, &tbl, &ishalt, &isfail, this]
			(const term& t) {
				if (ts.end() == ts.find(t)) {
					// ...we have a new hit
					ts.insert(t);
					// do what we have to do, we have a new tuple
					lexeme bltintype = dict.get_bltin(tbl.idbltin);
					wostream& os = o::dump() << endl; // o::dbg() << endl;
					if (bltintype == L"lprint") {
						// this is supposed to be formatted r-term printout
						pair<raw_term, wstring> rtp{ to_raw_term(t), L"p:"};
						os << L"printing: " << rtp << L'.' << endl;
					}
					else if (bltintype == L"halt") {
						ishalt = true;
						//wostream& os = o::dbg() << endl;
						pair<raw_term, wstring> rtp{ to_raw_term(t), L"p:" };
						os << L"program halt: " << rtp << L'.' << endl;
					}
					else if (bltintype == L"fail") {
						ishalt = isfail = true;
						//wostream& os = o::dbg() << endl;
						pair<raw_term, wstring> rtp{ to_raw_term(t), L"p:" };
						os << L"program fail: " << rtp << L'.' << endl;
					}
				}
			}, 0, true);
			// 'true' to allow decompress to handle builtins too
			if (isfail) return unsat = true; // to throw exception, TODO:
			if (ishalt) return false;
		}
		if (tbl.unsat) return unsat = true;
	}

	//out(wcout);

	// this does a test for addbit
	static bool isfirst = testaddbit;
	if (isfirst) {
		isfirst = false;
		// theoretically, iter handles any dynamic permutes, add_bit, reorder...
		//static iterbdds bdditer(*this);
		//static AddBits bdditer(*this);
		addBits.clear();
		addBits.permute_type({0, 0});
	}
	return b;
/*	if (!b) return false;
	for (auto x : goals)
		for (auto y : x.second)
			b &= (y && ts[x.first].t) == y;
	if (b) return (o::out() <<"found"<<endl), false;
	return b;*/
}

level tables::get_front() const {
	level r(tbls.size());
	for (ntable n = 0; n != (ntable)tbls.size(); ++n) r[n] = tbls.at(n).tq;
	return r;
}

bool tables::pfp(size_t nsteps, size_t break_on_step) {
	set<level> s;
	if (bproof) levels.emplace_back(get_front());
	level l;
	for (;;) {
		if (print_steps || optimize)
			o::inf() << L"# step: " << nstep << endl;
		++nstep;
		if (!fwd()) return true; // FP found
		if (unsat) throw contradiction_exception();
		if ((break_on_step && nstep == break_on_step) ||
			(nsteps && nstep == nsteps)) return false; // no FP yet
		l = get_front();
		if (!datalog && !s.emplace(l).second) throw infloop_exception();
		if (bproof) levels.push_back(move(l));
	}
	throw 0;
}

bool tables::run_prog(const raw_prog& p, const strs_t& strs, size_t steps,
	size_t break_on_step)
{
	clock_t start, end;
	double t;
	if (optimize) measure_time_start();
	add_prog(p, strs);
	if (optimize) {
		end = clock(), t = double(end - start) / CLOCKS_PER_SEC;
		o::ms() << L"# pfp: ";
		measure_time_start();
	}
	bool r = pfp(steps ? nstep + steps : 0, break_on_step);
	if (r && prog_after_fp.size())
		add_prog(move(prog_after_fp), {}, false), r = pfp();
	if (optimize)
		(o::ms() <<L"add_prog: "<<t << L" pfp: "),
		measure_time_end();
	return r;
}

tables::tables(dict_t dict_, bool bproof_, bool optimize_, bool bin_transform_,
	bool print_transformed_, bool autotype_, bool dumptype_, bool addbit_,
	bool bitsfromright_, bool optimize_memory_, bool sort_tables_) :
	dict(move(dict_)), bproof(bproof_), optimize(optimize_),
	bin_transform(bin_transform_), print_transformed(print_transformed_),
	autotype(autotype_), dumptype(dumptype_), testaddbit(addbit_),
	doemptyalts(true), optimize_memory(optimize_memory_),
	sort_tables(sort_tables_), infer(*this), addBits(*this) {
	// just a quick fix, we should have some global settings or something
	bitsmeta::BITS_FROM_LEFT = !bitsfromright_;
	if (optimize_memory)
		bdd::init_cache();
}

tables::~tables() {
	while (!bodies.empty()) {
		body *b = *bodies.begin();
		bodies.erase(bodies.begin());
		delete b;
	}
	while (!alts.empty()) {
		alt *a = *alts.begin();
		alts.erase(alts.begin());
		delete a;
	}
}

//set<body*, ptrcmp<body>> body::s;
//set<alt*, ptrcmp<alt>> alt::s;
