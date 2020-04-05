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
#include "types.h"
#include "bitsmeta.h"
#include "err.h"
//#include "term.h"
//#include "tables.h"

using namespace std;

tbl_arg::tbl_arg(const alt_arg& aa) : tab(aa.tab), arg(aa.arg) {
	DBG(assert(aa.alt == -1););
}

wostream& operator<<(wostream& os, const alt_arg& arg) {
	if (arg.alt == -1)
		return os << L"(" << arg.tab << L"," << arg.arg << L")"; // << endl;
	return os << L"(" << arg.tab << L"," << arg.alt << L"," << arg.arg << L")"; 
}
wostream& operator<<(wostream& os, const tbl_arg& arg) {
	return os << L"(" << arg.tab << L"," << arg.arg << L")"; // << endl;
}

wostream& operator<<(std::wostream& os, const arg_type& type) {
	switch (type.type) {
		case base_type::CHR: os << L":chr"; break;
		case base_type::STR: os << L":str"; break;
		case base_type::INT: os << L":int"; break;
		case base_type::NONE: os << L":none"; break;
	}
	return os << L"[" << type.bitness << L"]";
}

wostream& operator<<(wostream& os, const argtypes& types) {
	//for (const arg_type& type : types) {
	for (size_t i = 0; i != types.size(); ++i) {
		if (i > 0) os << L" ";
		os << types[i];
	}
	return os;
}

wostream& operator<<(wostream& os, const bitsmeta& bm) {
	//for (const arg_type& type : types) {
	for (size_t i = 0; i != bm.types.size(); ++i) {
		if (i > 0) os << L" ";
		os << bm.types[i];
		os << L"[" << bm.nums[i] << L"]";
	}
	return os;
}

///*
//maps tbl to tbl, it should always be from > to, if not swap.
//(we always call map_type w/ rvalues, we don't care if they change)
//{ table/rule, alt|-1, arg } // nothing for body|term?
//*/
//bool infer_types::map_type(tbl_arg from, tbl_arg to) {
//	if (from == to) return true; // do nothing
//	bool ret = true;
//	if (from < to) {
//		swap(from, to);
//		ret = false; // it's flipped
//	}
//	map_type({ from.tab, -1, from.arg }, { to.tab, to.arg });
//	return ret;
//}
//
///*
//maps alt to tbl.
//(we always call map_type w/ rvalues, we don't care if they change)
//*/
//void infer_types::map_type(alt_arg from, tbl_arg to) {
//	DBG(assert(from.alt != -1 || tbl_arg{ from } > to););
//	DBG(assert(to.arg < tbls[to.tab].bm.get_args()););
//	//wcout << L"map(a->t):" << from << L"," << to << L"," << endl;
//#ifdef DEBUG
//	if (from.alt != -1) {
//		alt& a = altstyped[{from.tab, size_t(from.alt)}];
//		if (!a.bm.types.empty())
//			assert(from.arg < a.bm.get_args());
//	}
//	else assert(from.arg < tbls[from.tab].bm.get_args());
//#endif
//	to = get_root_type(to);
//	alt_arg toalt(to);
//	set<alt_arg>& related = minvtyps[to]; // totbl
//	if (related.empty()) related.insert(toalt); // add self if first
//	// if we're mapping a tbl/arg, and it already has an entry, merge them...
//	if (from.alt == -1) {
//		auto it = minvtyps.find(tbl_arg{ from });
//		if (it != minvtyps.end()) {
//			DBG(assert(tbl_arg{ from } != to););
//			const set<alt_arg>& old = it->second;
//			// just copy, can't easily move a set and it's cheap (alt_arg)
//			related.insert(old.begin(), old.end());
//			minvtyps.erase(tbl_arg{ from });
//		}
//	}
//	related.insert(from);
//
//	tbl_arg root{ -1, 0 };
//	if (get_root_type(from, root) && root != to) { // if(root!=from && root!=to)
//		if (root < to) swap(root, to);
//		map_type(root, to);
//	}
//
//	mtyps.emplace(from, to);
//}
//
///*
// This actually syncs all types, once type inference is done (get_types)
//*/
//void infer_types::propagate_types() {
//	for (auto& it : minvtyps) {
//		const tbl_arg& type = it.first;
//		auto& bm = tbls[type.tab].bm;
//		DBG(assert(type == get_root_type(type)););
//		//if (type != get_root_type(type)) {
//		//	wcout << L"type!=root_type:" << 
//		//		type << L"," << get_root_type(type) << L"," << endl;
//		//}
//		DBG(assert(it.second.empty() || type == get_root_type(type)););
//		DBG(assert(type.arg < bm.get_args()););
//		//propagate_types(type);
//		for (const alt_arg& atype : it.second) {
//			if (atype.alt == -1) {
//				auto& tblbm = tbls[atype.tab].bm;
//				DBG(assert(atype.arg < tblbm.get_args()););
//				bitsmeta::sync_types(
//					tblbm.types[atype.arg], bm.types[type.arg],
//					tblbm.nums[atype.arg], bm.nums[type.arg]);
//			}
//			else {
//				// alt should be set up and present in the map
//				tbl_arg altkey{ atype.tab, size_t(atype.alt) };
//				DBG(assert(has(altstyped, altkey)););
//				alt& a = altstyped[altkey];
//				DBG(assert(atype.arg < a.bm.get_args()););
//				bitsmeta::sync_types(
//					a.bm.types[atype.arg], bm.types[type.arg],
//					a.bm.nums[atype.arg], bm.nums[type.arg]);
//			}
//		}
//	}
//}
//
///*
// Temporary types sync while doing get_types, likely to be deprecated
//*/
//void infer_types::propagate_types(const tbl_arg& intype) {
//	// TODO: if we remove this method, save/move this 1st part as that's needed
//	tbl_arg type = get_root_type(intype);
//	auto& bm = tbls[type.tab].bm;
//	if (type != intype) {
//		// in a nutshell, input tbl/arg should be in sync, so sync w/ it
//		auto& inbm = tbls[intype.tab].bm;
//		DBG(assert(type.arg < bm.get_args()););
//		DBG(assert(intype.arg < inbm.get_args()););
//		bitsmeta::sync_types(
//			inbm.types[intype.arg], bm.types[type.arg],
//			inbm.nums[intype.arg], bm.nums[type.arg]);
//	}
//	// we can cut this part off I think?
//	//return;
//	//map<tbl_arg, set<alt_arg>>::const_iterator it;
//	//if ((it = minvtyps.find(type)) == minvtyps.end()) return;
//	////set<alt_arg>& related = it->second;
//	//for (const alt_arg& atype : it->second) {
//	//	if (atype.alt == -1) {
//	//		auto& tblbm = tbls[atype.tab].bm;
//	//		DBG(assert(atype.arg < tblbm.get_args()););
//	//		bitsmeta::sync_types(
//	//			tblbm.types[atype.arg], bm.types[type.arg],
//	//			tblbm.nums[atype.arg], bm.nums[type.arg]);
//	//	} else {
//	//		map<tbl_arg, alt>::iterator ait; //const_iterator 
//	//		// it's possible that altstyped isn't yet uptodate, alt's not in yet
//	//		if ((ait = altstyped.find({ atype.tab, size_t(atype.alt) }))
//	//			== altstyped.end())
//	//			continue; // return;
//	//		bitsmeta& altbm = ait->second.bm; // *ait->second->bm;
//	//		if (altbm.types.empty()) continue; // not init yet, could happen
//	//		DBG(assert(atype.arg < altbm.get_args()););
//	//		bitsmeta::sync_types(
//	//			altbm.types[atype.arg], bm.types[type.arg],
//	//			altbm.nums[atype.arg], bm.nums[type.arg]);
//	//	}
//	//}
//}
//
//bool infer_types::get_root_type(const alt_arg& type, tbl_arg& root) const {
//	map<alt_arg, tbl_arg>::const_iterator it;
//	if ((it = mtyps.find(type)) != mtyps.end()) {
//		DBG(assert(type.alt != -1 || it->second < tbl_arg{ type }););
//		DBG(assert(it->second.arg < tbls[it->second.tab].bm.get_args()););
//		root = get_root_type(it->second);
//		return true;
//	}
//	return false; // type;
//}
//tbl_arg infer_types::get_root_type(const tbl_arg& type) const {
//	tbl_arg root{ -1, 0 };
//	if (get_root_type(alt_arg{ type }, root))
//		return root;
//	return type;
//}
//
//tbl_arg infer_types::get_fix_root_type(const tbl_arg& type) {
//	auto it = mtyps.find(alt_arg{ type });
//	if (it != mtyps.end()) {
//		DBG(assert(it->second < type););
//		tbl_arg root = get_root_type(it->second);
//		if (root != it->second)
//			mtyps.emplace(alt_arg{ type }, root);
//		return root;
//	}
//	return type;
//}
//
///* for headers only (w/ vars), simplified / optimized version */
//void infer_types::get_alt_types(const term& h, size_t /*altid*/) {
//	varmap m;
//	for (size_t n = 0; n != h.size(); ++n) {
//		if (h[n] < 0) {
//			if (!has(m, h[n]))
//				m.emplace(h[n], n);
//			else
//				map_type({ h.tab, m[h[n]] }, { h.tab, n });
//		}
//		// for facts, no need to map alt, just header
//	}
//}
///*
// Go through alt/terms and do 2 things a) sync or b) map types
// - sync is important to keep the 'root table' in sync (and build up/merge types)
// - map_type creates a hierarchy of types, matches and does the 'type inference'
//*/
//void infer_types::get_alt_types(const term& h, const term_set& al, size_t altid) {
//	alt& a = altstyped[{ h.tab, size_t(altid) }]; // create, get ref, fill it in
//	varmap m, mh;
//	ints ats = (ints)h, nums = h.nums;
//	argtypes types = h.types;
//	// header types are already in sync w/ rule tbl's, just copy it to alt t-s
//	a.varslen = h.size();
//	for (size_t n = 0; n != h.size(); ++n) {
//		if (h[n] < 0) {
//			if (!has(m, h[n]))
//				m.emplace(h[n], n),
//				mh.emplace(h[n], n);
//			else
//				map_type({ h.tab, m[h[n]] }, { h.tab, n });
//		}
//		if (al.empty()) continue; // for facts, no need to map alt, just header
//		map_type({ h.tab, int_t(altid), n }, { h.tab, n });
//	}
//	for (const term& t : al) {
//		bool isbody = t.extype == term::REL;
//		if (isbody) {}
//		bitsmeta& bm = t.tab != -1 ? tbls[t.tab].bm : tbls[h.tab].bm; // tbl.bm;
//		size_t tnums = 0;
//		if (!t.empty() && !t.nums.empty())
//			tnums = size_t(*max_element(t.nums.begin(), t.nums.end()));
//		for (size_t n = 0; n != t.size(); ++n)
//			if (t[n] < 0) {
//				size_t arg;
//				int_t harg = -1;
//				if (!has(m, t[n])) {
//					arg = a.varslen++;
//					m.emplace(t[n], arg);
//					ats.push_back(t[n]);
//					types.push_back(t.types[n]);
//					nums.push_back(t.nums[n]);
//				}
//				else {
//					arg = m[t[n]];
//					// check if header maps that var, to map tbl->tbl
//					varmap::const_iterator it;
//					if ((it = mh.find(t[n])) != mh.end())
//						harg = it->second;
//				}
//				// sync alt w/ term, this is 1-way, nothing to map w/ (no bm)
//				// - do we need even EQ types to be updated?
//				// - we don't need to map_type to smth like EQ (non-body)?
//				//term& rt = (term&)t; // hack to sync_types for nonbodies
//				bitsmeta::sync_types( // const arg_type&
//					types[arg], t.types[n], nums[arg], t.nums[n]);
//				// we do need to sync both ways (even map) for e.g. ARITH ?
//				switch (t.extype) {
//				case term::ARITH:
//				case term::EQ:
//				case term::LEQ:
//				{
//					// a quick fix to give arith/eq/leq some type to work w/
//					size_t bits = bitsmeta::BitScanR(tnums, 5) + 2;
//					bitsmeta::sync_types(
//						types[arg], { base_type::INT, bits }, nums[arg], 1 << bits);
//					break;
//				}
//				default: break;
//				}
//
//				if (t.tab == -1) {
//					// if we're 'exiting' we need to sync types changes to root
//					tbl_arg root{ -1, 0 };
//					if (get_root_type({ h.tab, int_t(altid), arg }, root)) {
//						bitsmeta& rbm = tbls[root.tab].bm;
//						bitsmeta::sync_types(
//							rbm.types[root.arg], types[arg],
//							rbm.nums[root.arg], nums[arg]);
//					}
//					if (harg != -1 && root != tbl_arg{ h.tab, size_t(harg) }) {
//						bitsmeta& hbm = tbls[h.tab].bm;
//						bitsmeta::sync_types(
//							hbm.types[harg], types[arg],
//							hbm.nums[harg], nums[arg]);
//					}
//					continue;
//				}
//
//				bitsmeta::sync_types(
//					types[arg], bm.types[n], nums[arg], bm.nums[n]);
//				map_type({ h.tab, int_t(altid), arg }, { t.tab, n });
//				if (harg != -1) {
//					// we don't really need this map do we? already done above
//					map_type({ h.tab, int_t(altid), arg }, { h.tab, size_t(harg) });
//					// rule/tbl => body/tbl
//					if (!map_type({ h.tab, size_t(harg) }, { t.tab, n })) {
//						// false==flipped, root is rule/tbl, uptodate it
//						// we only need to keep the root up-to-date w/ latest
//						bitsmeta& hbm = tbls[h.tab].bm;
//						bitsmeta::sync_types(
//							hbm.types[harg], bm.types[n],
//							hbm.nums[harg], bm.nums[n]);
//					}
//				}
//				// propagate to all related now - this is likely superfluous...
//				propagate_types({ t.tab, n });
//			}
//		// process builtins, eq-s etc. that have special type mapping rules
//		// do it 'outside the loop' as builtins often need to calc as a whole
//		if (t.extype == term::REL) {}
//		else if (t.extype == term::BLTIN) {
//			lexeme bltintype = dict.get_bltin(t.idbltin);
//			int_t bltinout = t.back(); // for those that have ?out
//			if (bltintype == L"count") {
//				size_t arg = m[bltinout];
//				// sync types to set some meaningful value for the arg, if any
//				// there's no table behind so nothing to sync or map
//				bitsmeta::sync_types( // const arg_type&
//					types[arg], { base_type::INT, 10 }, nums[arg], 1024); //?
//				// and should we map? not for now, ?out is likely 'on its own'
//				// but if any other rels use it we'd need to propagate this?
//				// would that be done automatically?
//				// just update the main table if this arg is in the header...
//				auto it = mh.find(bltinout);
//				if (it != mh.end()) {
//					size_t harg = it->second;
//					bitsmeta& hbm = tbls[h.tab].bm;
//					bitsmeta::sync_types(
//						types[arg], hbm.types[harg], nums[arg], hbm.nums[harg]);
//				}
//			}
//			// TODO: add other builtins type support
//		}
//		else if (t.extype == term::ARITH) {
//			//size_t tnums = size_t(max(t.nums.begin(), t.nums.end()));
//			//size_t bits = bitsmeta::BitScanR(tnums, 5) + 2; // min is 7 bits ?
//			//for (size_t n = 0; n != t.size(); ++n)
//			//	if (t[n] < 0) {
//			//		size_t arg = m[t[0]];
//			//		// what to set for bitness here? we have no consts, hmm
//			//		//if (types[arg].type == base_type::NONE) // only if nothing
//			//		bitsmeta::sync_types( // const arg_type&
//			//			types[arg], {base_type::INT, bits}, nums[arg], 1<<bits);
//			//	}
//		}
//		// TODO: we can optimize this based on eq/neg/leq and consts if any
//		// simple rule atm: var has the min bits of the largest const 
//		else if (t.extype == term::EQ || t.extype == term::LEQ) {
//			//DBG(assert(t.size() == 2););
//			////size_t bits = 5; // ?
//			//size_t tnums = size_t(max(t.nums.begin(), t.nums.end()));
//			//// if(tnums > 0)
//			//size_t bits = bitsmeta::BitScanR(tnums, 5) + 1; // min is 6 bits ?
//			//if (t[0] < 0) {
//			//	size_t arg = m[t[0]];
//			//	// what to set for bitness here? we have no consts, hmm
//			//	//if (types[arg].type == base_type::NONE) // only if nothing
//			//	bitsmeta::sync_types( // const arg_type&
//			//		types[arg], {base_type::INT, bits}, nums[arg], 1 << bits);
//			//}
//			//if (t[1] < 0) {
//			//	size_t arg = m[t[1]];
//			//	//if (types[arg].type == base_type::NONE) // only if nothing
//			//	bitsmeta::sync_types( // const arg_type&
//			//		types[arg], {base_type::INT, bits}, nums[arg], 1 << bits);
//			//}
//		}
//	}
//
//	DBG(assert(a.varslen == ats.size() && a.varslen == types.size()););
//	a.vm = m;
//	a.inv = varmap_inv(a.vm);
//	a.bm = bitsmeta(types.size());
//	a.bm.set_args(ats, types, nums);
//	a.bm.init(dict); // D: Q: for tbl we also 0 each bit into .t bdd, & alts?
//
//	// not needed, we're now updating as needed or at the end
//	// note: still needed, or init all tables before get_types
//	//tbls[h.tab].bm.update_types(a.bm.types, a.bm.nums);
//}
//
///*
// Type inference
//*/
////void infer_types::get_types(flat_prog& p) {
//void infer_types::get_types(const flat_prog& p) {
//	// TODO: we're not processing prog_add_rule etc. (does nothing), keep an eye
//	// (as get_types needs to be in sync w/ the get_rules (same order of t-s...)
//#ifndef TRANSFORM_BIN_DRIVER
//	// we need to keep get_types in sync w/ get_rules (same terms, ordering)
//	//if (bin_transform) transform_bin(p);
//	if (bin_transform) {
//		flat_prog q(move(transform_bin(p)));
//		map<ntable, ntable> mt;
//		// pBin: save all post-processing prog/terms, reuse in get_rules
//		for (const auto& x : q) prog_add_rule(pBin, mt, x);
//		replace_rel(move(mt), pBin);
//		set_priorities(pBin);
//		get_prog_types(pBin);
//		//get_prog_types(move(transform_bin(p)));
//		return;
//	}
//#endif
//	get_prog_types(p);
//}
//
//void infer_types::get_prog_types(const flat_prog& p) {
//	// TODO: optimize later, for now make a map like we're doing it in get_rules
//	// (it's too late in get_rules, and we need to sort/termset, also alts etc.)
//	map<term, set<term_set>> m;
//	for (const auto& x : p)
//		if (x.size() == 1) m[x[0]] = {};
//		else m[x[0]].insert(term_set(x.begin() + 1, x.end()));
//
//	set<rule> rs;
//	//map<ntable, size_t> altids4types;
//	for (pair<term, set<term_set>> x : m) {
//		// (don't) let facts take part in inferring the types
//		//if (x.second.empty()) continue;
//		term& t = x.first; // const ?
//		DBG(assert(t.tab != -1););
//		table& tbl = tbls[t.tab];
//		// no need to update here, just update bm
//		// nothing to map_type here, only tbl->tbl or alt->tbl, terms dont count
//		bitsmeta::sync_types(tbl.bm, t.types, t.nums); //t);
//		// - altids moved to member, to support multiple passes, e.g. ~r() :-
//		// - negated headers will have different sig and be new entry in the map
//		size_t& n = altids4types[t.tab];
//		if (x.second.empty() && doemptyalts && t.nvars != 0)
//			get_alt_types(t, n++);
//		else
//			for (const term_set& al : x.second)
//				get_alt_types(t, al, n++); // get_alt(al, t, as);
//	}
//}
