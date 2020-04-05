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
#include "iterbdds.h"
#include "tables.h"
#include "dict.h"
#include "input.h"
#include "err.h"
using namespace std;

#define add_bit rtbls.add_bit
#define add_bit_perm rtbls.add_bit_perm
#define permex_add_bit rtbls.permex_add_bit
#define deltail rtbls.deltail
#define tbls rtbls.tbls
#define altsmap rtbls.altsmap
#define get_root_type rtbls.inference.get_root_type
#define minvtyps rtbls.inference.minvtyps
#define tblrules rtbls.tblrules
#define tblbodies rtbls.tblbodies
#define rulealts rtbls.rulealts
#define altrule rtbls.altrule
#define altordermap rtbls.altordermap

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

void iterbdds::permute_type(const tbl_arg& intype, size_t addbits) {
	// we don't yet support more than 1 bit at the time
	DBG(assert(addbits == 1););
	DBG(assert(intype.tab != -1););

	// check input, as it could be anything really, other types below are fine
	if (tbls.size() <= size_t(intype.tab) ||
		tbls[intype.tab].len <= intype.arg || 
		tbls[intype.tab].bm.get_args() <= intype.arg)
		return; // or error?

	wcout << L"increasing universe / bitness (tbl:0, arg:0):" << endl;
	wcout << L"from:\t" << tbls[intype.tab].bm.get_bits(intype.arg) << endl;

	tbl_arg type = get_root_type(intype);
	//if (type != intype) {}
	set<alt_arg>& types = minvtyps[type];
	if (types.empty()) {
		// we actually have just that one type to process, so do that...
		types.insert(type); // could happen, 'types' w/o references
	}
	DBG(assert(has(types, alt_arg{type}));); // make sure we have 'self'
	// make sure we have the in type as well (it should be under the root type)
	DBG(assert(type == intype || has(types, alt_arg{intype})););

	auto& bm = tbls[type.tab].bm;
	size_t bits = bm.types[type.arg].bitness + 1;
	base_type bitype = bm.types[type.arg].type;
	// first, process all tables, prepare tbls cache...
	for (const alt_arg& atype : types) {
		if (atype.alt != -1) continue;
		ntable tab = atype.tab;
		size_t arg = atype.arg;
		tbl_arg targ{tab, arg}; //  = {tab, arg};
		//auto& tblbm = tbls[tab].bm;
		DBG(assert(arg < tbls[tab].bm.get_args()););
		permute_table({tab, arg}, bits, bitype);
		perminfo& info = tblargperms[{tab, arg}];
		//table& tb = tbls[tab];
		size_t len = info.bm.get_args();
		bits_perm perm{ tab, arg, len, info }; // tb.len
		for (size_t i : tblrules[tab]) {
			rule& r = rtbls.rules[i];
			// if rule/arg is already done skip it
			//if (has(rdone, tbl_arg{ tab, arg })) continue;
			DBG(assert(arg < r.t.size()););
			//int_t var = r.t[arg];
			//if (var >= 0) continue; // this should invalidate all alt-s too?
			if (has(rdone, targ)) 
				continue;
			rdone.insert(targ);
			r.eq = add_bit(r.eq, perm.perm, arg, perm.args);
			r.rlast = add_bit(r.rlast, perm.perm, arg, perm.args);
			r.h = add_bit(r.h, perm.perm, arg, perm.args);
			for (spbdd_handle& rl : r.last)
				rl = add_bit(rl, perm.perm, arg, perm.args);
			//r.eq = add_bit(r.eq, info, arg, len);
			//r.rlast = add_bit(r.rlast, info, arg, len);
			//for (spbdd_handle& rl : r.last)
			//	rl = add_bit(rl, info, arg, len);
		}
	}

	// now process alts...
	for (const alt_arg& atype : types) {
		if (atype.alt == -1) continue;
		ntable tab = atype.tab;
		size_t arg = atype.arg;
		tbl_arg targ{ tab, arg };
		auto it = altordermap.find({ atype.tab, size_t(atype.alt) });
		DBG(assert(it != altordermap.end()););
		tbl_alt altkey = it->second; //altkey{ atype.tab, size_t(atype.alt) };
		alt_arg altype = { altkey.tab, int_t(altkey.arg), atype.arg };
		if (has(altperms, altype)) // atype
			continue;
		//wcout << L"processing alt: \t" << altype << endl;
		DBG(assert(has(altsmap, altkey)););
		alt& a = *altsmap[altkey];
		map<pair<alt*, size_t>, alt_arg>::const_iterator ait = 
			altdone.find({ altsmap[altkey], arg });
		if (ait != altdone.end()) {
			//wcout << L"found alt: \t" << ait->second << endl;
			continue;
		}
		altdone.insert({ { altsmap[altkey], arg }, altype });
		if (a.bm.types.empty())
			continue; // shouldn't happen?
		DBG(assert(atype.arg < a.bm.get_args()););

		size_t args = a.bm.get_args(); // a.varslen;
		DBG(assert(a.bm.types[arg].bitness + 1 == bits););
		DBG(assert(a.bm.types[arg].type == bitype););
		perminfo info = add_bit_perm(a.bm, arg, args);
		altperms[altype] = info; // atype
		a.bm = info.bm;
		a.eq = add_bit(a.eq, info, arg, args);
		a.rng = add_bit(a.rng, info, arg, args);
		// this is the right way, we use rule's tbl perm (we should have it by now)
		// some issue here, need to pass right tbl perm directly, may not have it?
		////bits_perm& rperm = argtbls.at(tab);
		////a.rlast = add_bit(a.rlast, rperm.perm, rperm.arg, rperm.args);
		//for (spbdd_handle& al : a.last)
		//	al = add_bit(al, info, arg, args);
		auto pex = deltail(a.bm, tbls[tab].bm);
		a.ex = pex.first;
		a.perm = pex.second;
		// this is to reset and re-query on next step (last is synced w/ rlast)
		a.last.clear(); // a.rlast = hfalse;
		// or do this to imitate alt_query
		//a.rlast = bdd_and_many_ex_perm(a.last, a.ex, a.perm);
	}

	// now go through bodies as we need all tbls and alts to be done (bms/perms)
	for (const alt_arg& atype : types) {
		if (atype.alt != -1) continue;
		ntable tab = atype.tab;
		size_t arg = atype.arg;
		tbl_arg targ{ tab, arg };
		//wcout << L"processing alt (bodies): \t" << atype << endl;
		DBG(assert(arg < tbls[tab].bm.get_args()););
		DBG(assert(has(tblargperms, targ)););
		perminfo& info = tblargperms[{tab, arg}];
		size_t len = info.bm.get_args();
		bits_perm perm{ tab, arg, len, info }; // tb.len
		if (!has(tblbodies, tab)) 
			continue;
		for (const tbl_alt& talt : tblbodies[tab]) {
			//wcout << L"processing body: \t" << talt << endl;
			alt* palt = get_alt(talt); // alt& a = *get_alt(talt);
			auto it = bodydone.find({ targ, palt });
			if (it != bodydone.end()) {
				//wcout << L"found body: \t" << it->first << L"," << talt << endl;
				continue;
			}
			bodydone.insert({ targ, palt }); // altdone
			permute_bodies(targ, perm, *palt, bits, bitype);
		}
	}

	wcout << L"to:  \t" << tbls[intype.tab].bm.get_bits(intype.arg) << endl;
}

alt* iterbdds::get_alt(const tbl_alt& talt) const {
	auto it = altordermap.find(talt);
	DBG(assert(it != altordermap.end()););
	DBG(assert(has(altsmap, it->second)););
	return altsmap[it->second];
}

bool iterbdds::permute_table(ntable tab, size_t arg) {
	table& tb = tbls[tab];
	size_t bits = tb.bm.types[arg].bitness + 1;
	base_type type = tb.bm.types[arg].type;
	return permute_table({ tab, arg }, bits, type);
}

bool iterbdds::permute_table(const tbl_arg& targ, size_t bits, base_type type) {
	ntable tab = targ.tab;
	size_t arg = targ.arg;
	if (tab == -1) return false; // continue;
	//if (has(tdone, targ)) return false;
	if (has(tblargperms, targ)) { //if (has(tdone, targ)) {
		//perminfo& rinfo = tblargperms[targ]; // [{tab, arg}];
		//argtbls[tab] = { tab, arg, tb.len, rinfo };
		return false; // continue;
	}
	table& tb = tbls[tab];
	//size_t args = tb.len; // .bm.get_args();
	DBG(assert(tb.bm.types[arg].bitness + 1 == bits););
	DBG(assert(tb.bm.types[arg].type == type););

	perminfo info = add_bit_perm(tb.bm, arg, tb.len);
	DBG(assert(info.bm.get_args() == tb.len););
	tblargperms[targ] = info; // {tab, arg}
	//tdone.insert(targ);
	tb.bm = info.bm;
	tb.tq = add_bit(tb.tq, info, arg, tb.len);
	// add/del should be "table's" though not entirely clear (but mixes w/ t)
	for (spbdd_handle& tadd : tb.add)
		tadd = add_bit(tadd, info, arg, tb.len);
	for (spbdd_handle& tdel : tb.del)
		tdel = add_bit(tdel, info, arg, tb.len);
	// D: not sure if add/del is enough? maybe run the full rule alt_query loop?
	// stack to do all its dependencies (including rule)
	//bits_perm tperm{ tab, arg, tb.len, info }; // move(info)
	//argtbls[tab] = tperm; // save to process body below
	//vperms.push_back(tperm);
	return true;
}

// const bits_perm& altp, 
bool iterbdds::permute_bodies(const tbl_arg& targ, const bits_perm& p, alt& a, 
	size_t bits, base_type type)
{
	DBG(assert(targ.tab == p.tab && targ.arg == p.arg););
	//ntable tab = targ.tab;
	//size_t arg = targ.arg;
	for (size_t n = 0; n != a.size(); ++n) {
		DBG(assert(a[n] != nullptr););
		body& b = *a[n];
		if (b.tab == p.tab) {
			//wcout << L"processing body: \t" << targ << L"," << b.vals << endl;
			// permute body bdd-s (eq, last...)
			DBG(assert(p.perm.bm.get_bits(p.arg) == bits););
			DBG(assert(p.perm.bm.types[p.arg].type == type););

			// the perm bm is 'stale', contains only data valid per single perm.
			// - we need to perform addbit on single perm at the time (b by bit)
			// - but permex structs need to be calced for all perms/changes.
			// - thus, keep bit-by-bit perms to addbit, & final tbl bm to permex
			// ...or alternative, calc final 'addbits' and perms, do at once
			//const bitsmeta& tblbm = p.perm.bm;
			const bitsmeta& tblbm = tbls[p.tab].bm; // the latest bm for permex
			#ifdef DEBUG
			//size_t args = tblbm.get_args();
			//for (size_t n = 0; n != args; ++n) {
			//	DBG(assert((b.vals[n] < 0) == (b.poss[n] >= 0));); // warning
			//	if (b.vals[n] < 0)
			//		DBG(assert(size_t(b.poss[n]) == a.vm[b.vals[n]]););
			//	//if (b.vals[n] < 0) //if (has(a.vm, b.vals[n]))
			//	//	DBG(assert(
			//	//	tblbm.get_bits(n)==a.bm.get_bits(a.vm[b.vals[n]])););
			//}
			#endif

			// Q: seems that bdd ^ perm ^ perm ... doesn't change anything, t/f?
			// i.e. that it's safe to apply this multiple times for same b/t/arg
			b.q = add_bit(b.q, p.perm, p.arg, p.args);

			b.tlast = nullptr;
			//continue;
			// this won't be right till the last permute (if body has multiple)
			// TODO: make one superimposed final permute w/ all tbl permutes
			auto pex = 
				permex_add_bit(b.poss, tblbm, a.bm);
				//permex_add_bit(b.vals, a.vm, tblbm, a.bm);
				//permex_add_bit(b.vals, a.vm, p.perm.bm, a.bm);
			b.ex = pex.first;
			b.perm = pex.second;

			// TODO: make the final alt permute & we can do this, otherwise null
			////b.tlast = add_bit(b.tlast, p.perm, p.arg, p.args);
			// rlast is alt-based, not tbl-based, the right way, using alt perm
			////b.rlast = add_bit(b.rlast, altp.perm, altp.arg, altp.args);
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
