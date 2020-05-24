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
#include "addbits.h"
#include "tables.h"
#include "infer_types.h"
#include "dict.h"
#include "input.h"
#include "err.h"
using namespace std;

uints perm_init(size_t n);

#define tbls rtables.tbls
#define altsmap rtables.infer.altsmap
#define get_root_type rtables.infer.get_root_type
#define minvtyps rtables.infer.minvtyps
#define tblrules rtables.infer.tblrules
#define tblbodies rtables.infer.tblbodies
#define altordermap rtables.infer.altordermap

//   if it's a table...
// - permute the main table/arg, test/save to tblperms (no argtbls)
// - go through all the tblrules[tab], process rules (just core)
// - go through all tbl bodies (in all alts, tblbodies), do tbl/arg regardless 
//   if var/const? we do one perm for each tbl/arg? that also means again going 
//   through some rules, alts...and we need to have bdone also
// - rinse and repeat for all tbl-s in the 'related' set (just tbls)
// - we could have same body affected by multiple tbl/arg combos?
// - we cover all bodies w this (we have affected tbls i.e. bodies)
//   that's regardles of alts/bodies relations (via vars etc.)
// - if body is affected, alt is too - if tbl/arg is var, if const? then we 
//   could just be processing body w/o alt (and no aperm?). For that to work, 
//   dont' set last/rlast, just null them and that way we could just do 
//   tbls/bodies, alts later?
//   ----------------------------
//   ...then go through all alts...
// - don't do argsdep/tables or bodies - we've already done those?
//   ...or go like this...
// - first tables, rules
// - then go through alts, skip tbls, but do some bodies (w a perm)
// - or do just alts, but cache perms (tbl/arg). if alt/body is affected 
//   (var)->body/tbl var will be listed here and we'll cover body via tbl, if 
//   body is via const, alt doesn't matter anyways (different tbl/arg, different 
//   permute, null it). This is an issue, if use alt perm, we need var 
//   dependency (arg). Easier is just to null body tlast/rlast or sln is make 
//   proper alt perm, i.e. if alt is 'involved', then gather/use all alt's args 
//   permuted, and apply one final perm. if alt has no perms involved, then just 
//   make an identity perm! so body if affected will be permuted via tbl/arg-s 
//   (could be more than once, multiple args, each adds its perm)
// - to sum it up, if body is affected, it's here in the set/args.
// - each body change/perm is listed in one of tbl/arg-s here
//   (or we don't care, just check algo to have here all tbl/arg-s)
// - so go through all tbls and tbl/arg-s, perm tbls, construct end tbl perm (by
//   joining multiple perms for all args affected?) or if we hate that, then 
//   just cache perms, map all body args.
// - cache all (per tbl/arg, and use just tblperms, not argtbls).
// - we could have multiple args for one tbl, so multi-perm
//   just apply one by one, on tbl, or bodies (or ctor result perm?)
// - then go through alts, do core alt stuff, 
// - construct alt's final perm (if multiple args involved) for body
// - or just null bodies (rlast/tlast), as it's mucho easier
// - don't do anything else in alts, no tbls, no bodies
// - but cache alt's perms, to use later for bodies, unless anulling
// - then go through bodies as affected (by tbl/arg), one by one,
// - find tbl/arg-s final perm (cached) or apply one by one perm/arg
//   (that's for body bdd-s, not tlast/rlast)
// - find alt's perm if exists, use that for rlast/tlast
// - or if none, then ctor one identity alt perm, use that
// - or simply just null tlast and that's it
// - recheck if we need to consider bodies w/ consts affected, but I don't see 
//   why not, bdd-s change? so we need to perm, may be unnecessary at worst(?)
// - to loop bodies, a) use tbl/args one by one, tblbodies for each apply each 
//   tbl/arg perm
// - or b) easier I think is to gather all args per tbl, do at once
// - keep track of all done, tbls, rules, alts, bodies 
// - cache tables, alts perms (nothing else?)
// - then go through all tbls' all bodies' to cover any noncovered
// - or we've just done alts, go through all bodies now, 
//   use alts' perms if available (from cache), if not just null it.

void AddBits::clear() {
	altperms.clear();
	tblargperms.clear();
	altdone.clear();
	rdone.clear();
	bodydone.clear();
}

/*
 - call permute_type({}, nbits) - to increase bits and update bm
 - call permute_type({}, nbits, true) - if bm's already changed, just to do bdds
 - change bm.vargs (var order) + call permute_type({}, 0, true) - should work?
 - no compounds support yet, tbd.
*/
void AddBits::permute_type(const multi_arg& intype, size_t nbits, bool bitsready){
	DBG(assert(intype.tab != -1););
	// check input, as it could be anything really, other types below are fine
	if (tbls.size() <= size_t(intype.tab) ||
		tbls[intype.tab].len <= intype.arg ||
		tbls[intype.tab].bm.get_args() <= intype.arg)
		return; // or error?
	o::dump() << L"increasing universe / bitness (tbl:" 
		<< intype.tab << L", arg:" << intype.tab << L"):" << endl;
	if (bitsready)
		o::dump() << L"from:\t" <<
		tbls[intype.tab].bm.get_bits(intype.arg) - nbits << endl;
	else
		o::dump() << 
			L"from:\t" << tbls[intype.tab].bm.get_bits(intype.arg) << endl;

	clear();
	multi_arg type = get_root_type(intype);
	if (!has((minvtyps), type)) { // protect minvtyps from insert (like .at)
		o::dump() << L"addbit: in type not found?" << endl;
		return;
	}
	set<alt_arg>& types = minvtyps[type];
	auto& bm = tbls[type.tab].bm;

	// if we actually have just that one type, could happen, 'types' w/o refs...
	if (types.empty()) {
		// make sure conversion is ok here, should be if it gets here...
		if (!bm.types[type.arg][type].can_discard_path(type))
			throw runtime_error("discarding type not allowed?!");
		types.insert(alt_arg{ type, -1 });
	}
	DBG(assert(has(types, (alt_arg{ type, -1 })));); // make sure we have 'self'
	// make sure we have the in type as well (it should be under the root type)
	DBG(assert(type == intype || has(types, (alt_arg{ intype, -1 }))););

	// TODO: this fails for comps, need bm.types[type.arg][type] etc.
	init_target(bm.types[type.arg][type], bitsready, nbits);

	// first, process all tables, prepare tbls cache...
	for (const alt_arg& atype : types) {
		if (atype.alt != -1) continue;
		//ntable tab = atype.tab;
		//size_t arg = atype.arg;
		// TODO: this is likely wrong for comps, use alt-s subarg/path etc.
		multi_arg targ{atype}; // tab, arg, arg::none, {}};
		DBG(assert(targ.arg < tbls[targ.tab].bm.get_args()););
		bits_perm perm = permute_table(targ, nbits, bitsready);
		for (size_t i : tblrules[targ.tab]) {
			rule& r = rtables.rules[i];
			DBG(assert(targ.arg < r.t.size()););
			//if (r.t[targ.arg] >= 0) continue; // invalidates all alt-s too?
			if (has(rdone, targ))
				continue;
			rdone.insert(targ);
			r.eq = add_bit(r.eq, perm);
			r.rlast = add_bit(r.rlast, perm);
			r.h = add_bit(r.h, perm);
			for (spbdd_handle& rl : r.last)
				rl = add_bit(rl, perm);
		}
	}

	// now process alts...
	for (const alt_arg& atype : types) {
		if (atype.alt == -1) continue;
		//ntable tab = atype.tab;
		//size_t arg = atype.arg;
		multi_arg targ{atype};
		auto it = altordermap.find({ atype.tab, size_t(atype.alt) });
		DBG(assert(it != altordermap.end()););
		tbl_alt altkey = it->second;
		// TODO: a bit iffy given compounds, subarg/path? tbl_alt is none like
		// recheck altordermap and similar
		alt_arg altype{altkey.tab, int_t(altkey.arg), atype}; // atype.arg
		if (has(altperms, altype))
			continue;
		DBG(assert(has(altsmap, altkey)););
		alt& a = *altsmap[altkey];
		map<pair<alt*, size_t>, alt_arg>::const_iterator ait =
			altdone.find({ altsmap[altkey], targ.arg });
		if (ait != altdone.end()) continue;
		altdone.insert({ { altsmap[altkey], targ.arg }, altype });
		if (a.bm.types.empty())
			continue; // shouldn't happen?
		DBG(assert(targ.arg < a.bm.get_args()););
		size_t args = a.bm.get_args(); // a.varslen;
		DBG(check_bits(a.bm.types[targ.arg][targ], bitsready, nbits););
		perminfo info = add_bit_perm(a.bm, targ, args, nbits, bitsready);
		bits_perm perm{ targ.tab, targ, args, info, nbits };
		altperms[altype] = info;
		a.bm = info.bm;
		a.eq = add_bit(a.eq, perm);
		a.rng = add_bit(a.rng, perm);
		// this is the right way, we use rule's tbl perm (we should have it by now)
		// some issue here, need to pass right tbl perm directly, may not have it?
		////bits_perm& rperm = argtbls.at(targ.tab);
		////a.rlast = add_bit(a.rlast, rperm); //rp.perm, rp.arg, rp.args);
		//for (spbdd_handle& al : a.last)
		//	al = add_bit(al, perm);
		auto pex = tables::deltail(a, a.bm, tbls[targ.tab].bm);
		a.ex = pex.first;
		a.perm = pex.second;
		// this is to reset and re-query on next step (last is synced w/ rlast)
		a.last.clear();
		// or do this to imitate alt_query
		//a.rlast = bdd_and_many_ex_perm(a.last, a.ex, a.perm);
	}

	// now go through bodies as we need all tbls and alts to be done (bms/perms)
	for (const alt_arg& atype : types) {
		if (atype.alt != -1) continue;
		//ntable tab = atype.tab;
		//size_t arg = atype.arg;
		multi_arg targ{ atype }; // multi_arg targ{ tab, arg, arg::none, {} };
		DBG(assert(targ.arg < tbls[targ.tab].bm.get_args()););
		DBG(assert(has(tblargperms, targ)););
		perminfo& info = tblargperms[targ];
		size_t len = info.bm.get_args();
		bits_perm perm{ targ.tab, targ, len, info, nbits };
		if (!has(tblbodies, targ.tab))
			continue;
		for (const tbl_alt& talt : tblbodies[targ.tab]) {
			alt* palt = get_alt(talt);
			auto it = bodydone.find({ targ, palt });
			if (it != bodydone.end()) continue;
			bodydone.insert({ targ, palt });
			permute_bodies(perm, *palt);
		}
	}

	o::dump() << L"to:  \t" << tbls[intype.tab].bm.get_bits(intype.arg) << endl;
}

alt* AddBits::get_alt(const tbl_alt& talt) const {
	auto it = altordermap.find(talt);
	DBG(assert(it != altordermap.end()););
	DBG(assert(has(altsmap, it->second)););
	return altsmap[it->second];
}

bits_perm AddBits::permute_table(
	const multi_arg& targ, size_t nbits, bool bitsready) {
	//ntable tab = targ.tab;
	//size_t arg = targ.arg;
	if (targ.tab == -1) {
		o::dump() << L"permute_table(-1)???" << endl;
		throw 0; // return bits_perm{};
	}
	if (has(tblargperms, targ)) {
		perminfo& info = tblargperms[targ];
		return bits_perm{ targ.tab, targ, info.bm.get_args(), info, nbits };
	}
	else {
		table& tb = tbls[targ.tab];
		//size_t args = tb.len;
		DBG(check_bits(tb.bm.types[targ.arg][targ], bitsready, nbits););
		perminfo info = add_bit_perm(tb.bm, targ, tb.len, nbits, bitsready);
		DBG(assert(info.bm.get_args() == tb.len););
		bits_perm perm{ targ.tab, targ, tb.len, info, nbits };
		tblargperms[targ] = info;
		tb.bm = info.bm;
		tb.tq = add_bit(tb.tq, perm);
		for (spbdd_handle& tadd : tb.add)
			tadd = add_bit(tadd, perm);
		for (spbdd_handle& tdel : tb.del)
			tdel = add_bit(tdel, perm);
		return perm;
	}
}

bool AddBits::permute_bodies(const bits_perm& p, alt& a) {
	for (size_t n = 0; n != a.size(); ++n) {
		DBG(assert(a[n] != nullptr););
		body& b = *a[n];
		if (b.tab == p.tab) {
			DBG(check_bits(p.perm.bm.types[p.arg.arg][p.arg]););

			// the perm bm is 'stale', contains only data valid per single perm.
			// - we need to perform addbit on single perm at the time (b by bit)
			// - but permex structs need to be calced for all perms/changes.
			// - thus, keep bit-by-bit perms to addbit, & final tbl bm to permex
			// ...or alternative, calc final 'addbits' and perms, do at once
			//const bitsmeta& tblbm = p.perm.bm;
			const bitsmeta& tblbm = tbls[p.tab].bm; // the latest bm for permex

			// Q: seems that bdd ^ perm ^ perm ... doesn't change anything, t/f?
			// i.e. that it's safe to apply this multiple times for same b/t/arg
			b.q = add_bit(b.q, p); // p.perm, p.arg, p.args, p.nbits);

			// anull it and it'll be recalced on next step
			b.tlast = nullptr;

			// this won't be right till the last permute (if body has multiple)
			// TODO: make one superimposed final permute w/ all tbl permutes
			auto pex =
				permex_add_bit(b.poss, tblbm, a.bm);
			b.ex = pex.first;
			b.perm = pex.second;

			// TODO: make the final alt permute & we can do this, otherwise null
			////b.tlast = add_bit(b.tlast, p); // p.perm, p.arg, p.args);
			// rlast is alt-based, not tbl-based, the right way, using alt perm
			////b.rlast = add_bit(b.rlast, altp); // ap.perm, ap.arg, ap.args);
			// tlast and rlast need to be in sync, and rlast is wrong, needs alt
			// this resets next body_query, same as below
			////b.tlast = nullptr;

			// D: should we do body_query here again? everything changed e.g.
			// fix: this is actually required, some pos/bits ordering just won't
			// work otherwise
			////if (b.tlast && b.tlast->b == tbls[b.tab].tq->b) {} else 
			//{
			//	b.tlast = tbls[b.tab].tq;
			//	b.rlast = (b.neg ? bdd_and_not_ex_perm : bdd_and_ex_perm)
			//		(b.q, tbls[b.tab].tq, b.ex, b.perm);
			//}
		}
	}
	return true;
}

/* add bit to permute/ex (of a body) */
xperm AddBits::permex_add_bit(
	const map<multi_arg, int_t>& poss, const bitsmeta& bm, const bitsmeta& abm)
{
	//DBG(assert(bm.get_args() == poss.size()););

	bools ex = bools(bm.args_bits, false);
	size_t args = bm.get_args();
	map<int_t, multi_arg> m;
	// poss & vals/ints are similar, if 2 vals are same <--> poss are also same
	for (size_t n = 0; n != args; ++n) {
		bm.types[n].iterate([&](arg_type::iter& it) {
			auto itpos = poss.find({n, it.i, it.path});
			if (poss.end() == itpos || has(m, itpos->second))
				tables::get_var_ex(
					{n, it.i, it.path}, args, it.startbit, it.bits, ex, bm);
			else
				m.emplace(itpos->second, multi_arg{n, it.i, it.path});
		});
	}
	uints perm = tables::get_perm(poss, bm, abm);
	return { ex, perm };
}

/* 
 make a permute and a new bitsmeta from the previous bm (support method) 
 - make new bm (just for this arg, bits + nbits)
 - permute from old args/bm to new-args/new-bm, like del/add tail/get_perm
 - important (for optimization) is the actual bits layout
*/
perminfo AddBits::add_bit_perm(
	const bitsmeta& bm, multi_arg arg, size_t args, size_t nbits, bool bitsready) {
	if (bitsready) {
		bitsmeta oldbm(bm, arg, -nbits);
		return add_bit_perm(oldbm, bm, arg, args, nbits);
	} else {
		bitsmeta newbm(bm, arg, nbits); // make new bm, arg's bits += nbits
		return add_bit_perm(bm, newbm, arg, args, nbits);
	}
	//uints perm = perm_init(bm.args_bits);
	//// map from old to new pos, affects all args for the arg shift bits by nbits 
	//// (bits+1) is handled internally by newbm.pos (it 'knows' each arg's bits)
	//// doubled consts fix: reverse bits tb from-left (as consts), empty bits-1
	//for (size_t n = 0; n != args; ++n)
	//	for (size_t b = 0; b != bm.types[n].bitness; ++b)
	//		if (n==arg && !bitsmeta::BITS_FROM_LEFT) // reversed for consts
	//			perm[bm.pos(b, n, args)] = newbm.pos(b + nbits, n, args);
	//		else
	//			perm[bm.pos(b, n, args)] = newbm.pos(b, n, args);
	//return { newbm, perm };
}

perminfo AddBits::add_bit_perm(const bitsmeta& oldbm, const bitsmeta& newbm,
	multi_arg arg, size_t args, size_t nbits)
{
	uints perm = perm_init(oldbm.args_bits);
	// map from old to new pos, affects all args for the arg shift bits by nbits 
	// (bits+1) is handled internally by newbm.pos (it 'knows' each arg's bits)
	// doubled consts fix: reverse bits tb from-left (as consts), empty bits-1.
	for (size_t n = 0; n != args; ++n) {
		const arg_type& type = oldbm.types[n];
		const arg_type& newtype = newbm.types[n];
		type.iterate([&](arg_type::iter& it) {
			// startbit is different for old/new but we iterate old, so adjust
			// only works for 'natural order' (w/ subargs)
			//size_t newstartbit = (n == arg.arg) && it.i > arg.subarg ?
			//	it.startbit + nbits : it.startbit;
			size_t newstartbit = newtype.get_start({n, it.i, {}});
			for (size_t b = 0; b != it.bits; ++b) {
				// TODO: does it work for reverse? is entire arg 'from right'?
				if (n == arg.arg && 
					it.i == arg.subarg && 
					!bitsmeta::BITS_FROM_LEFT) // reversed
					perm[oldbm.pos(it.startbit + b, n, args)] = 
						 newbm.pos(newstartbit + b + nbits, n, args);
				else
					perm[oldbm.pos(it.startbit + b, n, args)] = 
						 newbm.pos(newstartbit + b, n, args);
			}
		});
	}
	return { newbm, perm };
	//for (size_t n = 0; n != args; ++n)
	//	for (size_t b = 0; b != oldbm.types[n].get_bits(); ++b)
	//		if (n == arg && !bitsmeta::BITS_FROM_LEFT) // reversed for consts
	//			perm[oldbm.pos(b, n, args)] = newbm.pos(b + nbits, n, args);
	//		else
	//			perm[oldbm.pos(b, n, args)] = newbm.pos(b, n, args);
	//return { newbm, perm };
}


/* adds a bit to an existing bdd */
spbdd_handle AddBits::add_bit(spbdd_handle h, 
	const perminfo& perm, multi_arg arg, size_t args, size_t nbits) {
	if (h == nullptr) return h;
	bdd_handles v = { h ^ perm.perm };
	const arg_type& type = perm.bm.types[arg.arg];
	size_t startbit = type.get_start(arg);
	const arg_type& subtype = type[arg];
	size_t bits = subtype.get_bits();
	for (size_t b = 0; b != nbits; ++b) {
		if (!bitsmeta::BITS_FROM_LEFT) { // i.e. reversed/consts, from-right
			v.push_back(::from_bit(perm.bm.pos(
				startbit + b, arg.arg, args), false));
		}
		else {
			// doubled consts: reverse, as consts, from-left, empty bits-1
			// addbit only makes sense on primitives, so specific bits
			v.push_back(::from_bit(perm.bm.pos(
				startbit + bits-nbits+b, arg.arg, args), false));
		}
	}
	return bdd_and_many(move(v));

	//type.iterate([&](arg_type::iter& it) {
	//	if (it.i != arg.subarg) return;
	//	for (size_t b = 0; b != nbits; ++b) {
	//		if (!bitsmeta::BITS_FROM_LEFT) { // i.e. reversed/consts, from-right
	//			v.push_back(::from_bit(perm.bm.pos(
	//				it.startbit + b, arg.arg, args), false));
	//		}
	//		else {
	//			// doubled consts: reverse, as consts, from-left, empty bits-1
	//			// addbit only makes sense on primitives, so specific bits
	//			v.push_back(::from_bit(perm.bm.pos(
	//				it.startbit + it.bits-nbits+b, arg.arg, args), false));
	//		}
	//	}
	//});
	//return bdd_and_many(move(v));

	//if (!bitsmeta::BITS_FROM_LEFT) // i.e. reversed for consts, from-right
	//	for (size_t b = 0; b != nbits; ++b)
	//		v.push_back(::from_bit(perm.bm.pos(b, arg, args), false));
	//else {
	//	// doubled consts: reverse bits, same as consts, from-left, empty bits-1
	//	// all we need is total bits, but addbit only makes sense on primitives?
	//	size_t bits = perm.bm.types[arg].get_bits();
	//	for (size_t b = 0; b != nbits; ++b)
	//		v.push_back(::from_bit(perm.bm.pos(bits-nbits+b, arg, args), false));
	//		//v.push_back(::from_bit(perm.bm.pos(bits-1-b, arg, args), false));
	//}
	//return bdd_and_many(move(v));
}


