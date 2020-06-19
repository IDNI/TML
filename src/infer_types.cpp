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
#include "infer_types.h"
#include "types.h"
#include "bitsmeta.h"
#include "err.h"
#include "term.h"
#include "tables.h"
#include "dict.h"
#include "input.h"

using namespace std;

#define tbls rtables.tbls

void replace_rel(const map<ntable, ntable>& m, vector<term>& x);
void replace_rel(const map<ntable, ntable>& m, flat_prog& p);
map<size_t, int_t> varmap_inv(const varmap& vm) {
	map<size_t, int_t> inv;
	for (auto x : vm) {
		assert(!has(inv, x.second.id));
		// VM: we only need arg.id/pos (& inv use is questionable, see proof.*)
		inv.emplace(x.second.id, x.first);
	}
	return inv;
}

infer_types::infer_types(tables& tables_) : rtables(tables_) {}

/*
maps tbl to tbl, it should always be from > to, if not swap.
(we always call map_type w/ rvalues, we don't care if they change)
{ table/rule, alt|-1, arg } // nothing for body|term?
*/
bool infer_types::map_type(multi_arg from, multi_arg to, bool noswap) {
	if (from == to) return true; // do nothing
	bool ret = true;
	if (!noswap && from < to) {
		swap(from, to);
		ret = false; // it's flipped
	} else if (noswap && from < to) {
		o::dump() << L"no swap but wrong order map?" << endl;
	}
	// TODO: alt_arg needs no path?
	map_type(alt_arg{ from, -1 }, to);
	return ret;
}

/*
maps alt to tbl.
(we always call map_type w/ rvalues, we don't care if they change)
*/
void infer_types::map_type(alt_arg from, multi_arg to) {
	DBG(assert(from.alt != -1 || multi_arg{ from } > to););
	DBG(assert(to.arg < tbls[to.tab].bm.get_args()););
	//wcout << L"map(a->t):" << from << L"," << to << L"," << endl;
#ifdef DEBUG
	if (from.alt != -1) {
		alt& a = altstyped[{from.tab, size_t(from.alt)}];
		if (!a.bm.types.empty())
			assert(from.arg < a.bm.get_args());
	}
	else assert(from.arg < tbls[from.tab].bm.get_args());
#endif
	to = get_root_type(to);
	alt_arg toalt(to, -1);
	set<alt_arg>& related = minvtyps[to]; // totbl
	if (related.empty()) related.insert(toalt); // add self if first
	// if we're mapping a tbl/arg, and it already has an entry, merge them...
	if (from.alt == -1) {
		auto it = minvtyps.find(multi_arg{ from });
		if (it != minvtyps.end()) {
			DBG(assert(multi_arg{ from } != to););
			const set<alt_arg>& old = it->second;
			// just copy, can't easily move a set and it's cheap (alt_arg)
			related.insert(old.begin(), old.end());
			minvtyps.erase(multi_arg{ from });
		}
	}
	related.insert(from);

	//multi_arg root{-1, arg::none, arg::none, {}};
	multi_arg root = multi_arg::get_empty();
	if (get_root_type(from, root) && root != to) { // if(root!=from && root!=to)
		if (root < to) swap(root, to);
		map_type(root, to);
	}

	if (auto ret = mtyps.emplace(from, to); ret.second == false) {
		mtyps.find(from)->second = to;
	}
}

void infer_types::propagate_types(const alt_arg& atype, bitsmeta& bm,
								  const multi_arg& type, bitsmeta& rootbm,
								  bool& lchg, bool& rchg, bool force) {
	if (atype.special == multi_arg::Size) {
		const arg_type& subtype = rootbm.types[type.arg][type];
		subtype.ensureCompound("propagate_types.::Size"); 
		// if (!subtype.isCompound()) throw 0;
		size_t size = subtype.compound.get_primitives().size();
		bitsmeta::sync_types(
			bm.types, (multi_arg)atype, 
			{base_type::INT, bitsmeta::BitScanR(int_t(size-1)), int_t(size-1)});
		lchg = true;
	} else if(atype.special == multi_arg::Element) {
		const arg_type& subtype = rootbm.types[type.arg][type];
		subtype.ensureCompound("propagate_types.::Element");
		// if (!subtype.isCompound()) throw 0;
		const primitive_type& element = subtype.compound.get_primitives()[0];
		bitsmeta::sync_types(
			bm.types, (multi_arg)atype, 
			element);
		lchg = true;
	} else {
		//if(force && bm.types)
		bitsmeta::sync_types(
			bm.types, (multi_arg)atype,
			rootbm.types, type, lchg, rchg, force);
	}
}
/*
 This actually syncs all types, once type inference is done (get_types)
*/
void infer_types::propagate_types() {
	//for (auto& it : minvtyps) {
	for (const auto& [type, related] : minvtyps) {
		//const multi_arg& type = it.first;
		auto& bm = tbls[type.tab].bm;

		// there's a 'hint' of recursion here if it fails
		//DBG(assert(type == get_root_type(type)););
		//if (type != get_root_type(type)) {
		//	wcout << L"type!=root_type:" << 
		//		type << L"," << get_root_type(type) << L"," << endl;
		//}
		//DBG(assert(related.empty() || type == get_root_type(type)););

		DBG(assert(type.arg < bm.get_args()););
		//propagate_types(type);
		bool rootchanged; // = false;
		size_t ntries = 0;
		do {
			rootchanged = false;
			for (const alt_arg& atype : related) { // it.second
				bool lchg = false, rchg = false;
				if (atype.alt == -1) {
					auto& tblbm = tbls[atype.tab].bm;
					DBG(assert(atype.arg < tblbm.get_args()););
					propagate_types(atype, tblbm, type, bm, lchg, rchg);
					//bitsmeta::sync_types(
					//	tblbm.types, (multi_arg)atype,
					//	bm.types, type, lchg, rchg);
					if (rchg)
						rootchanged = true;
				} else {
					// alt should be set up and present in the map
					tbl_alt altkey{ atype.tab, size_t(atype.alt) };
					DBG(assert(has(altstyped, altkey)););
					alt& a = altstyped[altkey];
					DBG(assert(atype.arg < a.bm.get_args()););
					// it happens (rarely) that alt is not synced w tbl if !none
					// so if mapping alt to an 'own' table - force alt args sync
					bool force= atype.tab == type.tab && atype.arg < a.hvarslen;
					// && atype.arg == type.arg // ?
					propagate_types(atype, a.bm, type, bm, lchg, rchg, force);
					//bitsmeta::sync_types(
					//	a.bm.types, (multi_arg)atype, bm.types, type, lchg, rchg);
					if (rchg)
						rootchanged = true;
				}
			}
			if (rootchanged) {
				//o::dump() << L"root changed, repeat..." << endl;
			}
			ntries++;
			if (ntries > 3) {
				o::dump() << L"root changed, repeating, ntries > 3..." << endl;
				break;
			}
		} while (rootchanged);
	}
}

/*
 Temporary types sync while doing get_types, likely to be deprecated
*/
void infer_types::propagate_types(const multi_arg& intype) {
	// TODO: if we remove this method, save/move this 1st part as that's needed
	multi_arg type = get_root_type(intype);
	auto& bm = tbls[type.tab].bm;
	if (type != intype) {
		// in a nutshell, input tbl/arg should be in sync, so sync w/ it
		auto& inbm = tbls[intype.tab].bm;
		DBG(assert(type.arg < bm.get_args()););
		DBG(assert(intype.arg < inbm.get_args()););
		bitsmeta::sync_types(inbm.types, intype, bm.types, type);
	}
}

bool infer_types::get_root_type(const alt_arg& type, multi_arg& root) const {
	map<alt_arg, multi_arg>::const_iterator it;
	if ((it = mtyps.find(type)) != mtyps.end()) {
		DBG(assert(type.alt != -1 || it->second < multi_arg(type)););
		DBG(assert(it->second.arg < tbls[it->second.tab].bm.get_args()););
		root = get_root_type(it->second);
		return true;
	}
	return false; // type;
}
multi_arg infer_types::get_root_type(const multi_arg& type) const {
	//multi_arg root{-1, arg::none, arg::none, {}};
	multi_arg root = multi_arg::get_empty();

	if (get_root_type(alt_arg{type, -1}, root))
		return root;
	return type;
}

multi_arg infer_types::get_fix_root_type(const multi_arg& type) {
	auto it = mtyps.find(alt_arg{type, -1});
	if (it != mtyps.end()) {
		DBG(assert(it->second < type););
		multi_arg root = get_root_type(it->second);
		if (root != it->second)
			mtyps.emplace(alt_arg{type, -1}, root);
		return root;
	}
	return type;
}

void infer_types::get_header_types(
	multi_arg targ, int_t val, const arg_type& type, alt_info& info)
{
	if (val >= 0) return; // optimize, outside
	vm_arg arg = vm_arg::get_empty();
	if (!has(info.m, val)) {
		arg = vm_arg{ targ, info.varslen++ };
		info.m.emplace(val, arg);
		info.mh.emplace(val, arg);
		info.types.push_back(type);
		DBG(assert(info.varslen == info.m.size()););
	}
	else {
		arg = info.m.at(val);
		map_type(multi_arg{ arg }, targ);
	}
	// for facts, no need to map alt
	if (!info.headerOnly)
		// fix for alts, no subargs basically, use .id
		// we need it for both new and 'repeated' var, targ to map to is different.
		map_type(alt_arg{ targ.tab, info.altid, arg.id }, targ);
}

void infer_types::get_term_types(
	const term& t, multi_arg targ, int_t val, const arg_type& type,
	bitsmeta& bm, size_t tnums, alt_info& info)
{
	if (val >= 0) return;
	
	vm_arg arg = vm_arg::get_empty();
	vm_arg harg = vm_arg::get_empty(); 
	if (!has(info.m, val)) {
		// arg.id (info.varslen++) is the id/index into info.types
		arg = vm_arg{ targ, info.varslen++ };
		info.m.emplace(val, arg);
		info.types.push_back(type);
		DBG(assert(info.varslen == info.m.size()););
	}
	else {
		arg = info.m.at(val);
		// check if header maps that var, to map tbl->tbl
		varmap::const_iterator it;
		if ((it = info.mh.find(val)) != info.mh.end())
			harg = it->second;
	}

	// sync alt w/ term, this is 1-way, nothing to map w/ (no bitsmeta)
	// - do we need even EQ types to be updated?
	// - we don't need to map_type to smth like EQ (non-body)?
	//term& rt = (term&)t; // hack to sync_types for nonbodies
	// sig: (arg_type&, const arg_type&)
	bitsmeta::sync_types(info.types[arg.id], type);

	// we do need to sync both ways (even map) for e.g. ARITH ?
	switch (t.extype) {
	case term::ARITH:
	case term::EQ:
	case term::LEQ:
	{
		// a quick fix to give arith/eq/leq some type to work w/
		size_t bits = bitsmeta::BitScanR(tnums, 1);
		bitsmeta::sync_types(
			info.types[arg.id], { base_type::INT, bits, (1 << bits) - 1 });
		break;
	}
	default: break;
	}

	if (t.tab == -1) {
		// if we're 'exiting' we need to sync types changes to root
		// comp arg will also always have root, just could be {tbl, arg, subarg}
		//multi_arg root{-1, arg::none, arg::none, {}};
		multi_arg root = multi_arg::get_empty();

		// h.tab, alt + alt-var# (arg.id) (for alt arg/sub rarely play)
		if (get_root_type({ info.tab, info.altid, arg.id }, root)) {
			bitsmeta::sync_types(
				tbls[root.tab].bm.types, root, info.types[arg.id]);
		}
		if (!harg.is_empty() && 
			root != multi_arg{ info.tab, harg.arg, harg.subarg, harg.path }) {
			bitsmeta::sync_types(
				tbls[info.tab].bm.types, (multi_arg)harg, info.types[arg.id]);
		}
		return;
	}

	bitsmeta::sync_types(bm.types, targ, info.types[arg.id]);

	// alt mapping id is {h.tab, alt, id/order#}
	map_type(alt_arg{ info.tab, info.altid, arg.id }, targ);
	if (!harg.is_empty()) {
		map_type(
			alt_arg{ info.tab, info.altid, arg.id },
			multi_arg{ info.tab, harg.arg, harg.subarg, harg.path });
		// rule/tbl => body/tbl
		//bool ret = 
		map_type(multi_arg{ info.tab, harg.arg, harg.subarg, harg.path }, targ);
		if (true) { //!ret) {
			// false==flipped, root is rule/tbl, uptodate it
			// we only need to keep the root up-to-date w/ latest
			bitsmeta::sync_types(
				tbls[info.tab].bm.types, (multi_arg)harg, bm.types, targ);
		}
	}

	// propagate to all related now - this is likely superfluous...
	propagate_types(targ);
}

// this doesn't seem to be need, alt vm gathers only 'pure' vars 
//static bool include_consts = false;
//#define INCLUDE_CONSTS

/*
 for headers only (w/ vars), simplified / optimized version 
 - this basically allows us to map e.g. A(?x ?x) and get a 1st 2nd 'connection' 
*/
void infer_types::get_alt_types(const term& h, size_t altid) {
	bitsmeta& bm = tbls[h.tab].bm;
	alt_info info{ h.tab, h.types, int_t(altid), true };
	for (size_t n = 0; n != h.size(); ++n) {
		#ifdef INCLUDE_CONSTS
		if (include_consts && h.is_const(n)) {
			// this is if we at all want to include consts in types/varslen.
			// it's a const, don't add to maps, just add type, ++varslen, map.
			info.types.push_back(bm.types[n]);
			size_t arg = info.varslen++;
			if (!info.headerOnly)
				map_type(alt_arg{h.tab, int_t(altid), arg}, {h.tab , n});
			continue;
		}
		#endif
		// to include compound vars (that represent the whole compound)
		// TODO: use .iterate now that we have it
		// rec comp: it.i should be a path and multi_arg too
		// it.i is prim id, but...we also could have vars that are per comp?
		// (now, not just on start, i.e. var elsewhere doesn't mean it's a prim)
		// we'll probably need a 'flag', like is-prim or is-comp?
		// or the same rule as for ?x at start, if at start of comp (0-arg of 
		// any comp within a comp), it means it's for the full thing. i.e. now
		// it makes sense to have that rule of vars only in leafs, if leaf, it's
		// either a prim, or is a 0-arg of a comp. we can't have in the middle.
		// and path should help w/ that, if last arg in the path is 0, it's prim
		// or full comp, nothing else to think about here.
		for (auto& it : type_vals{ bm.types[n], h.multivals()[n] }) {
			// it.i can be none, so leave it for now
			//const arg_type& subtype = it.container; // it.type()
			get_header_types(
				{h.tab, n, it.arg, it.path}, it.val, it.container, info);
		}
	}
	DBG(assert(info.m.size() == info.varslen););
}

void infer_types::sync_map_alt_var(
	const term& h, int_t val1, int_t val2, alt_info& info) {
	//map_type(toarg, fromarg);
	bitsmeta::sync_types(
		info.types, {info.m.at(val1).id, arg::none, {}}, 
		info.types, {info.m.at(val2).id, arg::none, {}});
	if (auto it = info.mh.find(val1); it != info.mh.end())
		bitsmeta::sync_types(
			info.types, {info.m.at(val1).id, arg::none, {}}, 
			tbls[h.tab].bm.types, (multi_arg)it->second);
}

multi_arg infer_types::sync_map_alt_var(
	const term& h, int_t val, const primitive_type& type, alt_info& info) {
	// TODO: this may not be right, multi_arg loses the alt 'id'
	//multi_arg arg = (multi_arg)info.m.at(val);
	//alt_arg arg{info.tab, info.altid, info.m.at(val).id, arg::none, {}};
	multi_arg arg{ info.m.at(val).id, arg::none, {} };
	bitsmeta::sync_types(info.types, arg, type);
	if (auto it = info.mh.find(val); it != info.mh.end()) {
		//map_type(arg, (multi_arg)it->second);
		bitsmeta::sync_types(
			info.types, arg, tbls[h.tab].bm.types, (multi_arg)it->second);
	}
	return arg;
}
/*
 Go through alt/terms and do 2 things a) sync or b) map types
 - sync is important to keep the 'root table' in sync (and build up/merge types)
 - map_type creates a hierarchy of types, matches and does the 'type inference'
*/
void infer_types::get_alt_types(const term& h, const term_set& al, size_t altid) {
	alt& a = altstyped[{ h.tab, size_t(altid) }]; // create, get ref, fill it in
	// header types are already in sync w/ rule tbl's, just copy it to alt t-s
	alt_info info{ h.tab, argtypes{}, int_t(altid), al.empty() };
	bitsmeta& hbm = tbls[h.tab].bm;
	for (size_t n = 0; n != h.size(); ++n) {
		//DBG(assert(hbm.types[n].isPrimitive() == h.types[n].isPrimitive()););
		#ifdef INCLUDE_CONSTS
		if (include_consts && h.is_const(n)) {
			// this is if we at all want to include consts in types/varslen
			// it's a const, don't add to maps, just add type, ++varslen, map.
			info.types.push_back(hbm.types[n]);
			size_t arg = info.varslen++;
			if (!info.headerOnly)
				map_type(alt_arg{h.tab, int_t(altid), arg}, {h.tab , n});
			continue;
		}
		#endif
		// to include compound vars (that represent the whole compound)
		// TODO: use .iterate now that we have it
		// rec comp: it.i should be a path and multi_arg too
		for (auto& it : type_vals{ hbm.types[n], h.multivals()[n] }) {
			// it.i can be none, so leave it for now
			//const arg_type& subtype = it.container; // it.type()
			get_header_types(
				{h.tab, n, it.arg, it.path}, it.val, it.container, info);
		}
	}

	DBG(assert(info.varslen == info.m.size()););
	a.hvarslen = info.varslen;

	for (const term& t : al) {
		bitsmeta& bm = t.tab != -1 ? tbls[t.tab].bm : tbls[h.tab].bm;
		size_t tnums = 0;
		if (!t.empty())
			tnums = std::accumulate(t.types.begin(), t.types.end(), 0,
				[](int_t acc, const arg_type& type) {
					// not sure if this makes sense though
					for (const primitive_type& prim : type.get_primitives())
						acc = max(acc, prim.num);
					return acc;
				});
		for (size_t n = 0; n != t.size(); ++n) {
			for (auto& it : type_vals{ t.types[n], t.multivals()[n] }) {
				// it.i can be none, so leave it for now
				// TODO: produces strange effect, it's primitive to start (here)
				// gets subarg 1 and path {1}, but later in inference becomes a 
				// compound, subarg is no longer valid, path still is
				// no easy way, we should just sync subarg/path after inference.
				const arg_type& subtype = it.container; // it.type()
					//it.container.isPrimitive() ? it.type() : it.container;
				get_term_types(t, {t.tab, n, it.arg, it.path}, it.val, subtype,
							   bm, tnums, info);
			}
		}
		// process builtins, eq-s etc. that have special type mapping rules
		// do it 'outside the loop' as builtins often need to calc as a whole
		if (t.extype == term::REL) {}
		else if (t.extype == term::BLTIN) {
			lexeme bltintype = rtables.dict.get_bltin(t.idbltin);
			int_t bltinout = t.back(); // for those that have ?out
			if (bltintype == L"count") {
				vm_arg arg = info.m.at(bltinout);
				// there's no table behind so nothing to map
				// sig: // (arg_type&, const arg_type&)
				bitsmeta::sync_types(
					info.types, (multi_arg)arg, { base_type::INT, 10, 1023 });
				// just update the main table if this arg is in the header...
				auto it = info.mh.find(bltinout);
				if (it != info.mh.end()) {
					vm_arg harg = it->second;
					bitsmeta::sync_types(
						info.types, (multi_arg)arg,
						tbls[h.tab].bm.types, (multi_arg)harg);
				}
			} else if (bltintype == L"iterate") {
				multi_arg arg{ info.m.at(t[0]) };
				alt_arg itarg{ 
					info.tab, info.altid, info.m.at(t[1]).id, arg::none, {} };
				alt_arg outarg{
					info.tab, info.altid, info.m.at(bltinout).id, arg::none,{}};
				multi_arg argsize{ arg };
				itarg.special = multi_arg::Size; // put this on dependent type
				outarg.special = multi_arg::Element;
				map_type(outarg, arg); // , true);
				map_type(itarg, argsize); // , true);
			} else if(bltintype == L"cast") {
			} else if (bltintype == L"decompose") {
				multi_arg from{ info.m.at(t[2]) };
				alt_arg to{h.tab, info.altid, info.m.at(t[1]).id, arg::none,{}};
				map_type(to, from);
				sync_map_alt_var(h, t[1], t[2], info);

			} else if (bltintype == L"rnd") {
			}
			// TODO: add other builtins type support
		}
		else if (t.extype == term::ARITH) {
			switch (t.arith_op) {
			case ADD:
			{
				multi_arg arg0{ multi_arg::get_empty() };
				multi_arg arg1{ multi_arg::get_empty() };
				if (t[0] < 0) arg0 = 
					sync_map_alt_var(h, t[0], { base_type::INT, 0 }, info);
				if (t[1] < 0) arg1 = 
					sync_map_alt_var(h, t[1], { base_type::INT, 0 }, info);
				if (t[2] < 0) {
					multi_arg argsum = 
						sync_map_alt_var(h, t[2], {base_type::INT, 0},info);
					if (t[0] < 0)
						map_type(
							{h.tab, int_t(altid),
							 info.m.at(t[2]).id, multi_arg::Sum},
							arg0);
					if (t[1] < 0)
						map_type(
							{h.tab, int_t(altid),
							 info.m.at(t[2]).id, multi_arg::Sum},
							arg1);
				}

				break;
			}
			default: break;
			}
		}
		// TODO: we can optimize this based on eq/neg/leq and consts if any
		// simple rule atm: var has the min bits of the largest const 
		else if (t.extype == term::EQ || t.extype == term::LEQ) {}
	}

	a.varslen = info.varslen;
	a.vm = info.m;
	a.inv = varmap_inv(a.vm);
	a.bm = bitsmeta(info.types.size());
	a.bm.set_args(info.types); // values, 
	a.bm.init(rtables.dict); 
}

/*
 Type inference
*/
void infer_types::get_types(const flat_prog& p) {
	// TODO: we're not processing prog_add_rule etc. (does nothing), keep an eye
	// (as get_types needs to be in sync w/ the get_rules (same order of t-s...)
#ifndef TRANSFORM_BIN_DRIVER
	// we need to keep get_types in sync w/ get_rules (same terms, ordering)
	//if (bin_transform) transform_bin(p);
	if (rtables.bin_transform) {
		flat_prog q(rtables.transform_bin(p)); // 
		map<ntable, ntable> mt;
		// pBin: save all post-processing prog/terms, reuse in get_rules
		for (const auto& x : q) rtables.prog_add_rule(rtables.pBin, mt, x);
		replace_rel(move(mt), rtables.pBin);
		rtables.set_priorities(rtables.pBin);
		get_prog_types(rtables.pBin);
		//get_prog_types(move(transform_bin(p)));
		return;
	}
#endif
	get_prog_types(p);
}

void infer_types::get_prog_types(const flat_prog& p) {
	// TODO: optimize later, for now make a map like we're doing it in get_rules
	// (it's too late in get_rules, and we need to sort/termset, also alts etc.)
	map<term, set<term_set>> m;
	for (const auto& x : p)
		if (x.size() == 1) m[x[0]] = {};
		else m[x[0]].insert(term_set(x.begin() + 1, x.end()));

	set<rule> rs;
	//map<ntable, size_t> altids4types;
	for (pair<term, set<term_set>> x : m) {
		// (don't) let facts take part in inferring the types
		//if (x.second.empty()) continue;
		term& t = x.first; // const ?
		DBG(assert(t.tab != -1););
		table& tbl = tbls[t.tab];
		// no need to update here, just update bm
		// nothing to map_type here, only tbl->tbl or alt->tbl, terms dont count
		bitsmeta::sync_types(tbl.bm, t.types); // , t.nums); //t);
		// - altids moved to member, to support multiple passes, e.g. ~r() :-
		// - negated headers will have different sig and be new entry in the map
		size_t& n = altids4types[t.tab];
		if (x.second.empty() && rtables.doemptyalts && t.nvars != 0)
			get_alt_types(t, n++);
		else
			for (const term_set& al : x.second)
				get_alt_types(t, al, n++); // get_alt(al, t, as);
	}
}
void infer_types::rewire_tables(flat_prog& p) {

}
