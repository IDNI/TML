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

#include <vector>
#include <regex>

#include "ir_builder.h"
#include "tables.h"
using namespace std;

ir_builder::ir_builder(dict_t& dict_, rt_options& opts_) :
		dict(dict_), opts(opts_) { }

ir_builder::~ir_builder() { }

void align_vars(vector<term>& v) {
	map<int_t, int_t> m;
	for (size_t k = 0; k != v.size(); ++k)
		for (size_t n = 0; n != v[k].size(); ++n)
			if (v[k][n] < 0 && !has(m, v[k][n]))
				m.emplace(v[k][n], -m.size() - 1);
	if (!m.empty()) for (term& t : v) t.replace(m);
}

#ifdef TYPE_RESOLUTION

void ir_builder::set_vartypes(int_t i, ints &mp, rr_varmap &v, raw_rule &auxr) {
	ints tix;
	tml_natives var_types;
	int_t d = i;
	for (size_t k = 0; k != v.size(); k++) {
		tix.push_back(d % mp[k]);
		d = d / mp[k];
	}

	//decompress, select ith, and fill var_types
	int_t a = 0;
	for (auto &var: v) {
		int_t len = 1;
		int_t bits = 2;
		int_t var_idx = tix[a];
		vector<term> *r = &var.second[0].c;
		if (r->size() == 0) { //decompress only once
			allsat_cb(var.second[0].types, len * bits,
					[r, bits, len, this](const bools& p, bdd_ref ) {
				term t(false, term::REL, NOP, 0, ints(len, 0), 0);
				for (int_t n = 0; n != len; ++n)
					for (int_t k = 0; k != bits; ++k)
						if (p[dynenv->pos(k, n, len)])
							t[n] |= 1 << k;
				r->insert(r->begin(),t);
			})();
		}

		tml_native_t t; //term2tml_native(r[var_id]);
		switch (var.second[0].c[var_idx][0]) {
			case 0: t.type = SYMB; break;
			case 1: t.type = UINT; break;
			case 2: t.type = UCHAR; break;
			case 3: return; //only required for goals
			default : assert(false);
		}
		a++;

		for (auto &vi : var.second) {
			for (auto &vii : vi.inst.positions) {
				if (vi.inst.rt_idx == 0)
					auxr.h[0].s.second[vii] = t;
				else
					auxr.b[0][vi.inst.rt_idx-1].s.second[vii] = t;
			}
		}
	}
	//free_vars ?
}

void ir_builder::get_vars_eq(const raw_term&t, int_t idx, rr_varmap& vars) {
	assert(t.e.size()==3);

	sig s = get_sig_eq(t);
	if (s.second[0].type != POLY || s.second[1].type != POLY) {
		int_t k = s.second[0].type != POLY ? 0 : 1;
		int_t h = k == 0 ? 2 : 0;
		rt_var_inst aux0 = {idx,{}};
		rt_vartypes aux(aux0,hfalse);
		term f;
		switch (s.second[k].type) {
			case SYMB: f.push_back(0);	break;
			case UINT: f.push_back(1); break;
			case UCHAR: f.push_back(2); break;
			case POLY: assert(false); break;
			default : assert(false);
		}
		aux.types = dynenv->from_fact(f);
		int_t id = dict.get_var(t.e[h].e);
		vars[id].push_back(aux);
	}

	else {
		rt_var_inst aux0 = {idx,{}};
		rt_vartypes aux(aux0,hfalse);
		term f;
		for (auto &i : {0,1,2}) {
			f.clear();
			f.push_back(i);
			aux.types = aux.types || dynenv->from_fact(f);
		}

		vars[dict.get_var(t.e[0].e)].push_back(aux);
		//v[dict.get_var(rt.e[0].e)][0].positions
		vars[dict.get_var(t.e[2].e)].push_back(aux);
		//TODO: when ?x = ?y possible optimization is to just replace var
		// over whole rule and just remove equality as a constraint
	}
}

void ir_builder::get_vars_leq(const raw_term&t, int_t idx, rr_varmap& vars) {
	assert(t.e.size()==3);
	ints tl = {0,2};
	for (auto &i : tl) {
		//int_t pos = i == 0 ? i : i-1;
		if (t.e[i].type == elem::VAR) {
			int_t id = dict.get_var(t.e[i].e);
			auto it = find(vars[id].begin(), vars[id].end(), idx);
			if (it != vars[id].end())
				//assert types is UINT
				//it->inst.positions.push_back(pos); //no required
				;
			else {
				rt_var_inst aux0 = {idx,{}};
				rt_vartypes aux(aux0,hfalse);
				term f; f.push_back(1);
				aux.types = dynenv->from_fact(f);
				vars[id].push_back(aux);
			}
		}
		//TODO: assert that non var elem is indeed a NUM
	}
}

void ir_builder::get_vars_arith(const raw_term&t, int_t idx, rr_varmap& vars) {
	assert(t.e.size()==5 || t.e.size()==6);
	ints tl = {0,2,4};
	if (t.e.size()==6) tl.push_back(5);
	for (auto &i : tl) {
		if (t.e[i].type == elem::VAR) {
			int_t id = dict.get_var(t.e[i].e);
			auto it = find(vars[id].begin(), vars[id].end(), idx);
			if (it != vars[id].end())
				//assert types is UINT
				;
			else {
				rt_var_inst aux0 = {idx,{}};
				rt_vartypes aux(aux0,hfalse);
				term f; f.push_back(1);
				aux.types = dynenv->from_fact(f);
				vars[id].push_back(aux);
			}
		}
		//TODO: assert that non var elem is indeed a NUM
	}
}

void ir_builder::get_vars_bltin(const raw_term&t, int_t idx, rr_varmap& vars) {
	int_t i = 0;
	for (auto &ei : t.e) {
		if (ei.type == elem::VAR) {
			int_t id = dict.get_var(t.e[i].e);
			auto it = find(vars[id].begin(), vars[id].end(), idx);
			if (it != vars[id].end())
				it->inst.positions.push_back(i);
			else {
				if (t.e[0].e == "pw_add" || t.e[0].e == "pw_mult" || t.e[0].e == "bw_xor" ||
						(t.e[0].e == "count" && i == (int_t) t.e.size()-2) ) {
					rt_var_inst aux0 = {idx,{i-2}};
					rt_vartypes aux(aux0,hfalse);
					term f; f.push_back(1);
					aux.types = dynenv->from_fact(f);
					vars[id].push_back(aux);
				}
				else {
					rt_var_inst aux0 = {idx,{i-2}};
					rt_vartypes aux(aux0,hfalse);
					term f;
					for (auto &i : {0,1,2}) {
						f.clear();
						f.push_back(i-2);
						aux.types = aux.types || dynenv->from_fact(f);
					}
					vars[id].push_back(aux);
				}
			}
		}
		++i;
	}
}

void ir_builder::get_vars_rel(const raw_term&t, int_t idx, rr_varmap& vars) {
	int_t tl = (t.e.size() == 1) ? 0 : t.e.size()-2;
	for (int_t i = 2; i <= tl; i++)
		if (t.e[i].type == elem::VAR) { //could be based on t.s[i] == POLY
			int_t id = dict.get_var(t.e[i].e);
			auto it = find(vars[id].begin(), vars[id].end(), idx);
			if (it != vars[id].end()) it->inst.positions.push_back(i-2);
			else {
				rt_var_inst aux0 = {idx,{i-2}};
				rt_vartypes aux(aux0,hfalse);
				vars[id].push_back(aux);
			}
		}
}

rr_varmap ir_builder::get_vars(raw_rule &r) {
	rr_varmap v;
	auto h = *r.h.begin();
	get_vars_rel(h, 0, v);
	int_t rt_idx = 1;
	for (auto &rtv : r.b) for (auto &rt : rtv) {
		switch (rt.extype) {
			case raw_term::REL: get_vars_rel(rt, rt_idx, v); break;
			case raw_term::EQ: get_vars_eq(rt, rt_idx, v); break;
			case raw_term::LEQ: get_vars_leq(rt, rt_idx, v); break;
			case raw_term::ARITH: get_vars_arith(rt, rt_idx, v); break;
			case raw_term::BLTIN: get_vars_bltin(rt, rt_idx, v); break;
			default: break;
		}
		rt_idx++;
	}
	return v;
}

void ir_builder::type_resolve_facts(vector<raw_rule> &rp) {
	for (auto itr = rp.begin(); itr != rp.end();) {
		if (!itr->b.empty()) {++itr; continue; }
		if (itr->type == raw_rule::GOAL) {++itr; continue; }

		//head bltins handled here as well
		sig s = get_sig(*itr->h.begin());
		//assert(it = relid_argtypes_map.find(s.first) != relid_argtypes_map.end());
		//assert(find(it->second.begin(), it->second.end(), s.second) != it->second.end());
		++itr;
	}
}

void ir_builder::type_resolve_bodies(raw_rule &r, rr_varmap &v) {
	int_t i = 1;
	for (auto &rtv : r.b) for (auto &rt : rtv) {
		sig s;
		if (rt.extype == raw_term::BLTIN) {
			s = get_sig_bltin(rt);
			++i; continue;
		}
		else if (rt.extype != raw_term::REL) {
			++i; continue;
		}
		else {
			s = get_sig(rt);
			auto it = relid_argtypes_map.find(s.first);
			//assert(it != relid_argtypes_map.end());
			for (auto &rel_sig : it->second)
				if (rel_sig == s.second) {
					//COUT << "body matched" << endl;
					//TODO: simplify / improve this matching
					for (auto &var : v) for (auto &vt : var.second)
						if (vt.inst.rt_idx == i) {
							native_type ts = UNDEF;
							bool vld = true;
							for (auto j: vt.inst.positions) {
								assert(rel_sig[j].type == UINT || rel_sig[j].type == SYMB || rel_sig[j].type == UCHAR);
								if (ts == UNDEF) ts = rel_sig[j].type;
								if (!(ts == rel_sig[j].type)) {vld = false; break;}
							}
							if (vld) {
								term f;
								switch (ts) {
									case SYMB: f.push_back(0); break;
									case UINT: f.push_back(1); break;
									case UCHAR: f.push_back(2); break;
									default : assert(false);
								}
								vt.types = vt.types || dynenv->from_fact(f);
							}
						}
				}
			++i;
		}
	}
}

void ir_builder::type_resolve_rules(vector<raw_rule> &rp) {

	for (auto it = rp.begin(); it != rp.end();) {
		rr_varmap v;
		if (it->b.empty()) {
			if (it->type == raw_rule::GOAL) {
				sig s = get_sig(*it->h.begin());
				DBG(for (auto &si : s.second) assert(si.type == POLY););
				get_vars_rel(*it->h.begin(), 0, v);
				//TODO: handle goals to create typed rules only for the corresponding target
				// avoid creating all pairs of types
			}
			else { it++; continue;}
		}
		else {
			sig sh = get_sig(*it->h.begin());
			v = get_vars(*it);
			if ((*it->h.begin()).extype == raw_term::BLTIN) assert(false);
			//free_vars: detected only at bodies, for cons/bltinsTBD
		}

		type_resolve_bodies(*it, v);

		//reorder negated terms to end of bodies vector as required by *TR001*
		//for (auto &var : v) {
		for (auto itv = v.begin(); itv != v.end(); itv++) {
			int_t bound = itv->second.size();
			for (int_t k = 0; k < bound; k++) {
				if ((itv->second[k].inst.rt_idx != 0) &&
					(it->b[0][itv->second[k].inst.rt_idx-1].neg)) {
					while (it->b[0][itv->second[bound-1].inst.rt_idx-1].neg && k < bound)
						bound--;
					if (k < bound)
						swap(itv->second[k], itv->second[bound-1]);
				}
			}
		}

		//rule context: set head and free var vts
		DBG(COUT << "match types ..." << endl;);
		spbdd_handle *ptr = 0;
		for (auto &var : v) {
			for (auto &vt : var.second) {
				if (vt.inst.rt_idx == 0) {//is_head
					vt.types = htrue;
					ptr = &vt.types;
				}
				else if (ptr != 0) {
					spbdd_handle aux = *ptr && vt.types;
					//::out(COUT, aux) << endl;;
					//*TR001*: avoid type mismatch due to negated body
					if (!(it->b[0][vt.inst.rt_idx-1].neg && aux == hfalse)) {
						*ptr = aux;
					}
				}
				else { //is_free
					//TODO: test polyms of free var between multiple bodies
					;
				}
			}
			//::out(COUT, *ptr);
		}

		DBG(COUT << "starting rule replacement ... " << endl;);
		int_t mpn = 0;
		ints mp;
		for (auto &var : v) {
			int_t vl = satcount(var.second[0].types,2); //types.size()
			vl = vl > 3 ? 3 : vl;
			mpn = mpn == 0 ? vl : mpn * vl;
			mp.push_back(vl);
		}

		if (v.size() == 0) {it++;continue;}
		if (mpn == 0) {
			COUT << "WARNING: removing rule due to invalid types" << endl; //add lineno
			const raw_rule aux = *it;
			it = rp.erase(it);
			continue;
		}

		const raw_rule aux = *it;
		it = rp.erase(it);

		for (int_t i = 0; i < mpn; ++i) {
			raw_rule auxr = aux;
			set_vartypes(i, mp, v, auxr);
			it = rp.insert(it, auxr);
			it++;
			sig s = auxr.h[0].s;

			auto it = relid_argtypes_map.find(s.first);
			if (it != relid_argtypes_map.end()) {
				//TODO: add some monitor here for POLY?
				if (find(it->second.begin(), it->second.end(), s.second) == it->second.end())
					it->second.push_back(s.second);
			}
			else relid_argtypes_map.insert({s.first, {s.second}});
		}
		if (mpn == 0) it++;
	}
}

void ir_builder::type_resolve(raw_prog &rp) {
	//setting universe size due usage of bdd data structure to operate with sets of types
	dynenv->bits = 2;
	type_resolve_facts(rp.r);
	type_resolve_rules(rp.r);
	dynenv->bits = 0;
}

sig ir_builder::to_native_sig(const term& e) {

	tml_natives tn(e.size(), {native_type::UNDEF,-1});

	for (size_t i = 0; i != e.size(); ++i) {
		if (e[i] == 0) tn[i].type = SYMB;
		else if (e[i] == 1) tn[i].type = UINT;
		else if (e[i] == 2) tn[i].type = UCHAR;
		else if (e[i] == 3) ;
		else assert(false);
	}
	int_t tab_id = dynenv->tbls[e.tab].s.first;
	sig s = {tab_id, tn};
	//sig s = {0, tn};
	//smap[s] = e.tab
	return s;
}

void reencode_rel(raw_term *rt, tml_natives &t) {
	size_t tl = (rt->e.size() == 1) ? 0 : rt->e.size()-2;
	for (size_t i = 2; i <= tl; ++i)
		switch (t[i-2].type) {
			case SYMB:	rt->e[i] = elem((int_t) 0); break;
			case UINT:	rt->e[i] = elem((int_t) 1); break;
			case UCHAR: rt->e[i] = elem((int_t) 2); break;
			case POLY: break;
			default : assert(false);
		}
}

//TODO: review effect of 1 == 2 on the input prog
// this will lead to 1 == 1 in tr prog with possible
// wrong inference
void reencode_eqleq(raw_term *rt, tml_natives &t) {

	switch (t[0].type) {
		case SYMB:	rt->e[0] = elem((int_t) 0); break;
		case UINT:	rt->e[0] = elem((int_t) 1); break;
		case UCHAR: rt->e[0] = elem((int_t) 2); break;
		case POLY: break;
		default : assert(false);
	}
	switch (t[1].type) {
		case SYMB:	rt->e[2] = elem((int_t) 0); break;
		case UINT:	rt->e[2] = elem((int_t) 1); break;
		case UCHAR: rt->e[2] = elem((int_t) 2); break;
		case POLY: break;
		default : assert(false);
	}
}

raw_prog ir_builder::generate_type_resolutor(raw_prog &rp) {

	raw_prog tr(dict);
	for (auto itr = rp.r.begin(); itr != rp.r.end();) {
		raw_rule rr = *itr;
		//head
		raw_term *rth = &rr.h.front();
		if (rth->extype == raw_term::BLTIN)  {++itr; continue; }
		sig sh = get_sig(*rth);
		if (rr.b.empty()) {
			if (itr->type == raw_rule::GOAL) {++itr; continue; }
			//TODO if builtin
			if (rr.prft) {
				rr.prft.reset();
				int_t j = 2;
				for (auto &i : sh.second) {
					if (i.type == POLY) i.type = UINT;
					rth->e[j] = elem((int_t)1);
					j++;
				}
			}
			reencode_rel(rth, sh.second); //many to one mappings
			if (append(relid_argtypes_map, sh)) {
				vector<native_type> tys((int_t) sig_len(sh), UINT);
				sig st = get_sig_typed(sh.first, tys);
				rth->s = st;
				tr.r.push_back(rr);
			}
		}
		else {
			if (rth->neg) {itr++; continue;}

			reencode_rel(rth, sh.second);
			vector<native_type> tys((int_t) sig_len(sh), UINT);
			sig st = get_sig_typed(sh.first, tys);
			rth->s = st;

			for (size_t k = 0 ; k != rr.b.front().size(); ++k) {
				raw_term *rt =  &rr.b.front().at(k);
				sig s;
				switch (rt->extype) {
					case raw_term::REL: {
						if (!rt->neg) {
							s = get_sig(*rt);
							reencode_rel(rt, s.second);
							vector<native_type> tys((int_t) sig_len(s), UINT);
							sig st = get_sig_typed(s.first, tys);
							rt->s = st;
						}
						else {
							//auto it = rr.b.front().begin();
							auto it = begin(rr.b.front());
							it += k;
							//auto it = next(begin(rr.b.front()), k);
							it = rr.b.front().erase(it);
							k--;
						}
						break;
					}
					case raw_term::EQ:
						s = get_sig_eq(*rt);
						reencode_eqleq(rt, s.second);
						break;
					case raw_term::LEQ:
						s = get_sig_eq(*rt); //leq same as eq
						reencode_eqleq(rt, s.second);
						rt->neg = false;
						rt->extype = raw_term::EQ;
						break;

					case raw_term::ARITH: {
						s = get_sig_arith(*rt);
						vector<raw_term> vrt;
						int_t i = 0;
						ints ev;
						for (auto &t : s.second) {
							if (t.type == POLY) {
								int_t id = i <= 2 ? dict.get_var(rt->e[i*2].e) : dict.get_var(rt->e[i*2-1].e);
								if (find(ev.begin(), ev.end(), id) == ev.end()) {
									elem v = i <= 2 ? rt->e[i*2] : rt->e[i*2-1];
									ev.push_back(id);
									raw_term r;
									r.e.push_back(v);
									r.e.push_back(elem(elem::etype::EQ));
									r.e.push_back(elem(1));
									r.extype = raw_term::EQ;
									vrt.push_back(r);
								}
							}
							i++;
						}
						auto it = begin(rr.b.front());
						it += k;
						it = rr.b.front().erase(it);
						k--;
						it = rr.b.front().insert(it, vrt.begin(),vrt.end());
						k += vrt.size();
						break;
					}
					case raw_term::BLTIN: {
						auto it = begin(rr.b.front());
						it += k;
						it = rr.b.front().erase(it);
						k--;
						break;
					}
					default: ;
				}
			}
			tr.r.push_back(rr);
		}
		itr++;
	}
	return tr;
}

sig ir_builder::get_sig_bltin(raw_term&t) {
	if (t.s.second.size()) return t.s;
	int_t id = dict.get_bltin(t.e[0].e);
	size_t tl = (t.e.size() == 1) ? 0 : t.e.size()-2;
	tml_natives tn(t.arity[0], {native_type::UNDEF,-1});
	for (size_t i = 2; i <= tl; ++i)
		switch (t.e[i].type) {
			case elem::STR:
			case elem::SYM:	tn[i-2].type = native_type::SYMB; break;
			case elem::NUM:	tn[i-2].type = native_type::UINT ; break;
			case elem::CHR: tn[i-2].type = native_type::UCHAR; break;
			case elem::VAR: tn[i-2].type = native_type::POLY; break;
			default : assert(false);
		}
	t.s = {id, tn};
	return t.s;

	/*if (is_head) {
		assert(dynenv->bltins[id].has_head);
		return dynenv->bltins[id].head.sig;
	} else {
		assert(dynenv->bltins[id].has_body);
		return dynenv->bltins[id].body.sig;
	}*/
}

sig ir_builder::get_sig_arith(const raw_term&t) {

	int_t table_name_id = dict.get_rel(dict.get_lexeme("ARITH"));
	assert(t.e.size()==5 || t.e.size()==6);
	ints tl = {0,2,4};
	if (t.e.size()==6) tl.push_back(5);
	tml_natives tn;
	for (auto &i : tl) {
		switch (t.e[i].type) {
			case elem::STR:
			case elem::SYM:	tn.push_back({native_type::SYMB,-1}); break;
			case elem::NUM:	tn.push_back({native_type::UINT,-1}); break;
			case elem::CHR: tn.push_back({native_type::UCHAR,-1}); break;
			case elem::VAR: tn.push_back({native_type::POLY,-1}); break;
			default : assert(false);
		}
	}
	return {table_name_id , tn};
}

sig ir_builder::get_sig_eq(const raw_term&t) {
	//if (t.s.second.size()) return t.s;
	int_t table_name_id = dict.get_rel(dict.get_lexeme("EQ"));
	ints tl = {0,2};
	tml_natives tn;
	for (auto &i : tl) {
		switch (t.e[i].type) {
			case elem::STR:
			case elem::SYM:	tn.push_back({native_type::SYMB,-1}); break;
			case elem::NUM:	tn.push_back({native_type::UINT,-1}); break;
			case elem::CHR: tn.push_back({native_type::UCHAR,-1}); break;
			case elem::VAR: tn.push_back({native_type::POLY,-1}); break;
			default : assert(false);
		}
	}
	//t.s = {table_name_id , tn};
	return {table_name_id , tn};
}

sig ir_builder::get_sig_typed(const lexeme& rel, vector<native_type> tys) {
	int_t table_name_id = dict.get_rel(rel);
	tml_natives tn;
	for (auto &t : tys)
		tn.push_back({t,-1});
	return {table_name_id, tn};
}

sig ir_builder::get_sig_typed(const int_t& rel_id, vector<native_type> tys) {
	tml_natives tn;
	for (auto &t : tys)
		tn.push_back({t,-1});
	return {rel_id, tn};
}
#endif //TYPE_RESOLUTION

sig ir_builder::get_sig(raw_term&t) {
	int_t table_name_id = dict.get_rel(t.e[0].e);
#ifdef TML_NATIVES
	assert(t.arity.size() == 1);
	if (t.s.second.size()) return t.s;
	tml_natives tn(t.arity[0], {native_type::UNDEF,-1});
#ifdef TYPE_RESOLUTION
	size_t tl = (t.e.size() == 1) ? 0 : t.e.size()-2;
	//TODO: fill bitwidth
	for (size_t i = 2; i <= tl; ++i)
		switch (t.e[i].type) {
			case elem::STR:
			case elem::SYM:	tn[i-2].type = native_type::SYMB; break;
			case elem::NUM:	tn[i-2].type = native_type::UINT ; break;
			case elem::CHR: tn[i-2].type = native_type::UCHAR; break;
			case elem::VAR: tn[i-2].type = native_type::POLY; break;
			default : assert(false);
		}
#endif
	t.s = {table_name_id , tn};
	return t.s;
#else
	return {table_name_id , t.arity};
#endif
}

sig ir_builder::get_sig(const lexeme& rel, const ints& arity) {
	int_t table_name_id = dict.get_rel(rel);
#ifdef TML_NATIVES
	assert(arity.size() == 1);
	tml_natives tn(arity[0], {native_type::UNDEF,-1});
	return {table_name_id, tn};
#else
	return {table_name_id, arity};
#endif
}

sig ir_builder::get_sig(const int_t& rel_id, const ints& arity) {
#ifdef TML_NATIVES
	assert(arity.size() == 1);
	tml_natives tn(arity[0], {native_type::UNDEF,-1});
	return {rel_id, tn};
#else
	return {rel_id, arity};
#endif
}

size_t ir_builder::sig_len(const sig& s) const {
#ifdef TML_NATIVES
	return s.second.size();
#else
	assert(s.second.size()==1);
	return s.second[0];
#endif
}

// ----------------------------------------------------------------------------

flat_prog ir_builder::to_terms(const raw_prog& pin) {
	flat_prog m;
	vector<term> v;
	term t;
	raw_prog p = pin;
	for (raw_rule& r : p.r)

		//XXX:  each rule is a context.
		if (r.type == raw_rule::NONE && !r.b.empty()) {
			for (const raw_term& x : r.h) {
				get_nums(x);
				t = from_raw_term(x, true);
				v.push_back(t);
				for (const vector<raw_term>& y : r.b) {
					int i = 0;
					for (const raw_term& z : y) // term_set(
						v.push_back(from_raw_term(z, false, i++)),
						get_nums(z);
					//FIXME:
					//only having effect on regression/builtins/count1.tml:
					//rules NAB_prod_A , NAB_prod_B
					//and sudoku backtracking (probalby due to use of count as well)
					align_vars(v);
					if (!m.insert(move(v)).second) v.clear();
				}
			}
		}
		else if(r.prft) {
			bool is_sol = false;
			form* froot = 0;
			//TODO: review
			sprawformtree root = r.prft->neg // neg transform
				? make_shared<raw_form_tree>(elem::NOT,
						make_shared<raw_form_tree>(*r.prft))
				: make_shared<raw_form_tree>(*r.prft);
			if (r.prft->guard_lx != lexeme{ 0, 0 }) { // guard transform
				raw_term gt;
				gt.arity = { 0 };
				gt.e.emplace_back(elem::SYM, r.prft->guard_lx);
				root = make_shared<raw_form_tree>(elem::AND, root,
					make_shared<raw_form_tree>(gt));
			}
			from_raw_form(root, froot, is_sol);
			/*
			DBG(COUT << "\n ........... \n";)
			DBG(r.prft->printTree();)
			DBG(COUT << "\n ........... \n";)
			DBG(froot->printnode(0, this);)
			*/
			term::textype extype;
			if(is_sol) {
				//DBG(COUT << "\n SOL parsed \n";)
				//to_pnf(froot);
				extype = term::FORM2;
			} else {
				//froot->implic_rmoval();
				extype = term::FORM1;
			}
			spform_handle qbf(froot);

			for (raw_term& x : r.h) {
				#ifdef TYPE_RESOLUTION
				sig s = get_sig(x);
				for (auto &e : s.second) {
					e.type = UINT;
				}
				x.s = s;
				#endif

				get_nums(x), t = from_raw_term(x, true),
				v.push_back(t);
				t = term(extype, qbf);
				v.push_back(t);
				//align_vars_form(v);
				m.insert(move(v));
			}
			//TODO: review multiple heads and varmaps
		} else  {
			for (const raw_term& x : r.h)
				t = from_raw_term(x, true),
				t.goal = r.type == raw_rule::GOAL,
				m.insert({t}), get_nums(x);
		}

	// Note the relations that are marked as tmprel in the raw_prog
	#ifdef HIDDEN_RELS
	for(const auto &[functor, arity] : p.hidden_rels)
		dynenv->tbls[get_table(get_sig(functor, arity))].hidden = true;
	#endif
	
	return m;
}

// ----------------------------------------------------------------------------

term ir_builder::from_raw_term(const raw_term& r, bool isheader, size_t orderid) {
	ints t;
	lexeme l;
	size_t nvars = 0;

	//FIXME: this is too error prone.
	term::textype extype = (term::textype)r.extype;
	bool realrel = extype == term::REL || (extype == term::BLTIN && isheader);
	// skip the first symbol unless it's EQ/LEQ/ARITH (which has VAR/CONST as 1st)
	//bool isrel = realrel || extype == term::BLTIN;
	for (size_t n = !realrel ? 0 : 1; n < r.e.size(); ++n)
		switch (r.e[n].type) {
			case elem::NUM:	t.push_back(mknum(r.e[n].num)); break;
			case elem::CHR: t.push_back(mkchr(r.e[n].ch)); break;
			case elem::VAR:	++nvars; t.push_back(dict.get_var(r.e[n].e)); break;
			case elem::STR: {
				l = r.e[n].e;
				++l[0], --l[1];
				int_t s = dict.get_sym(dict.get_lexeme(unquote(lexeme2str(l))));
				t.push_back(mksym(s));	break;
			}
			case elem::SYM:	t.push_back(mksym(dict.get_sym(r.e[n].e))); break;
			default: break;
		}
	raw_term auxr = r;
	int_t tab = realrel ? get_table(get_sig(auxr)) : -1;

	if (extype == term::BLTIN) {
		#ifdef TYPE_RESOLUTION
		sig s = get_sig_bltin(auxr);
		int_t idbltin = s.first;
		int_t idbltin_tr = get_bltin(s);
		return term(r.neg, idbltin_tr, t, orderid, idbltin,
			(bool) (r.e[0].num & 1), (bool) (r.e[0].num & 2));

		#else
		int_t idbltin =  dict.get_bltin(r.e[0].e);
		if (tab > -1) {
			// header BLTIN rel w table, save alongside table (for decomp. etc.)
			dynenv->tbls[tab].idbltin = idbltin;
			dynenv->tbls[tab].bltinargs = t; // if needed, for rule/header (all in tbl)
			dynenv->tbls[tab].bltinsize = nvars; // number of vars (<0)
		}
		return term(r.neg, tab, t, orderid, idbltin,
			(bool) (r.e[0].num & 1), (bool) (r.e[0].num & 2));
		#endif
	}
	return term(r.neg, extype, r.arith_op, tab, t, orderid);
}

elem ir_builder::get_elem(int_t arg) const {
	if (arg < 0) return elem(elem::VAR, dict.get_var_lexeme(arg));

	if(!opts.bitunv) {
		if (arg & 1) return elem((char32_t) (arg >> 2));
		if (arg & 2) return elem((int_t) (arg >> 2));
		return elem(elem::SYM, dict.get_sym_lexeme(arg >>2));
	}
	else {
		if(arg == 1 || arg == 0) return elem((bool) (arg));
		return elem(elem::SYM, dict.get_sym_lexeme(arg));
	}
}

void ir_builder::get_nums(const raw_term& t) {
	for (const elem& e : t.e)
		if (e.type == elem::NUM) nums = max(nums, e.num);
		else if (e.type == elem::CHR) chars = max(chars, (int_t)e.ch);
		else if (e.type == elem::SYM) syms = max(syms, (int_t) dict.nsyms()); //e.num
}

#ifdef TYPE_RESOLUTION
int_t ir_builder::get_bltin(const sig& s) {
	auto it = bsmap.find(s);
	if (it != bsmap.end())
		return it->second;
	int_t nb = dynenv->bltins.sigs.size(); // == bsmap.size()
	bsmap.emplace(s,nb);
	dynenv->bltins.sigs.push_back(s);
	return nb;
}
#endif

int_t ir_builder::get_table(const sig& s) {

#ifdef TYPE_RESOLUTION
	DBG(for (auto &se : s.second) {
		assert (se.type != UNDEF && "error: unresolved type");
	};);
#endif

	auto it = tsmap.find(s);
	if (it != tsmap.end())
		return it->second;
	int_t nt = dynenv->tbls.size();
	table tb;
	tb.s = s, tb.len = sig_len(s);
	dynenv->tbls.push_back(tb);
	tsmap.emplace(s,nt);
	return nt;
}

//---------------------------------------------------------

/* Populates froot argument by creating a binary tree from raw formula in rfm.
It is caller's responsibility to manage the memory of froot. If the function,
returns false or the froot is not needed any more, the caller should delete the froot pointer.
For a null input argument rfm, it returns true and makes froot null as well.
	*/
bool ir_builder::from_raw_form(const sprawformtree rfm, form *&froot, bool &is_sol) {

	form::ftype ft = form::NONE;
	bool ret =false;
	form *root = 0;
	int_t arg = 0;

	if(!rfm) return froot=root, true;

	if(rfm->rt) {
		ft = form::ATOM;
		#ifdef TYPE_RESOLUTION
		if (rfm->rt->extype == raw_term::REL) {
			sig s = get_sig(*rfm->rt);
			for (auto &e : s.second) {
				e.type = UINT;
			}
			rfm->rt->s = s;
		}
		#endif

		term t = from_raw_term(*rfm->rt);
		arg = dict.get_temp_sym(rfm->rt->e[0].e); //fixme, 2nd order var will conflic with consts
		root = new form(ft, arg, &t);
		froot = root;
		if(!root) return false;
		return true;
	}
	else {
		switch(rfm->type) {
			case elem::NOT:
				root = new form(form::NOT);
				if(root ) {
					ret =  from_raw_form(rfm->l, root->l, is_sol);
					froot = root;
					return ret;
				}
				else return false;

			case elem::VAR:
			case elem::SYM:
				ft = form::ATOM;
				if( rfm->type == elem::VAR)
					arg = dict.get_var(rfm->el->e);
				else
					arg = dict.get_temp_sym(rfm->el->e); //VAR2
				root = new form(ft, arg);
				froot = root;
				if(!root) return false;
				return true;

			//identifying sol formula
			case elem::FORALL:
				if(rfm->l->type == elem::VAR) ft = form::FORALL1;
				else ft = form::FORALL2, is_sol = true;
				break;
			case elem::UNIQUE:
				if(rfm->l->type == elem::VAR) ft = form::UNIQUE1;
				else ft = form::UNIQUE2, is_sol = true;
				break;
			case elem::EXISTS:
				if(rfm->l->type == elem::VAR) ft = form::EXISTS1;
				else ft = form::EXISTS2, is_sol = true;
				break;
			case elem::OR:
			case elem::ALT: ft = form::OR; break;
			case elem::AND: ft = form::AND; break;
			case elem::IMPLIES: ft= form::IMPLIES; break;
			case elem::COIMPLIES: ft= form::COIMPLIES; break;
			default: return froot= root, false;
		}
		root =  new form(ft);
		ret = from_raw_form(rfm->l, root->l, is_sol);
		if(ret) ret = from_raw_form(rfm->r, root->r, is_sol);
		froot = root;
		return ret;
	}
}

raw_term ir_builder::to_raw_term(const term& r) {
		raw_term rt;
		size_t args;
		rt.neg = r.neg;
		//understand raw_term::parse before touching this
		if (r.extype == term::EQ) {
			args = 2, rt.e.resize(args + 1), rt.arity = {2};
			rt.extype = raw_term::EQ;
			rt.e[0] = get_elem(r[0]), rt.e[1] = elem::EQ, rt.e[2] = get_elem(r[1]);
			return rt;
		} else if (r.extype == term::LEQ) {
			rt.extype = raw_term::LEQ;
			args = 2, rt.e.resize(args + 1), rt.arity = {2};
			rt.e[0] = get_elem(r[0]), rt.e[1] = elem::LEQ; rt.e[2] = get_elem(r[1]);
			return rt;
		} else if( r.tab == -1 && r.extype == term::ARITH ) {
				rt.e.resize(5);
				elem elp;
				elp.arith_op = r.arith_op;
				elp.type = elem::ARITH;
				switch ( r.arith_op ) {
					case t_arith_op::ADD: elp.e = dict.get_lexeme("+");break;
					case t_arith_op::MULT: elp.e = dict.get_lexeme("*");break;
					case t_arith_op::SUB: elp.e = dict.get_lexeme("-");break;
					default: __throw_runtime_error( "to_raw_term to support other operator ");
				}
				elem elq;
				elq.type = elem::EQ;
				elq.e = dict.get_lexeme("=");

				rt.e[0] = get_elem(r[0]);
				rt.e[1] = elp;
				rt.e[2] = get_elem(r[1]);
				rt.e[3] = elq;
				rt.e[4] = get_elem(r[2]);
				rt.extype = raw_term::ARITH;
				return rt;
		} else if (r.extype == term::BLTIN) {
			args = r.size();
			rt.e.resize(args + 1);
			rt.e[0] = elem(elem::SYM,
				dict.get_bltin_lexeme(r.idbltin));
			rt.e[0].num = r.renew << 1 | r.forget;
			rt.arity = { (int_t) args };

			#ifdef TYPE_RESOLUTION
			sig s = dynenv->bltins.sigs[r.tab];
			for (size_t n = 1; n != args + 1; ++n) {
				switch (s.second[n-1].type) {
					case native_type::UINT :
						rt.e[n] =  elem((int_t) r[n - 1]); break;
					case native_type::UCHAR :
						rt.e[n] =  elem((char32_t) r[n - 1]); break;
					case native_type::SYMB :
						rt.e[n] =  elem(elem::SYM,dict.get_sym_lexeme(r[n - 1])); break;
					case native_type::POLY :
						COUT << "warning: unhandled sig path for BLTIN" << endl; break;
					default : assert(false);
				}
			}
			#else
			for (size_t n = 1; n != args + 1; ++n)
				rt.e[n] = get_elem(r[n - 1]);
			#endif

			rt.add_parenthesis();
		}
		else {
			if (r.tab != -1) {
				args = dynenv->tbls.at(r.tab).len, rt.e.resize(args + 1);
				rt.e[0] = elem(elem::SYM,
						dict.get_rel_lexeme(get<0>(dynenv->tbls.at(r.tab).s)));
				rt.arity = {(int_t) sig_len(dynenv->tbls.at(r.tab).s)};
				#ifdef TML_NATIVES
				assert(rt.arity.size() == 1);
				#endif

				#ifdef TYPE_RESOLUTION
				sig s = dynenv->tbls[r.tab].s;
				for (size_t n = 1; n != args + 1; ++n) {
					elem e;
					switch (s.second[n-1].type) {
						case native_type::UINT :
							rt.e[n] =  elem((int_t) r[n - 1]); break;
						case native_type::UCHAR :
							rt.e[n] =  elem((char32_t) r[n - 1]); break;
						case native_type::SYMB :
							rt.e[n] =  elem(elem::SYM,dict.get_sym_lexeme(r[n - 1])); break;
						case native_type::POLY :
							COUT << "warning: unhandled sig path" << endl; break;
						default : assert(false);
					}
				}
				#else
				for (size_t n = 1; n != args + 1; ++n)
					rt.e[n] = get_elem(r[n - 1]);
				#endif

				rt.add_parenthesis();
			} else {
				args = 1;
				rt.e.resize(args);
				rt.e[0] = get_elem(r[0]);
			}
		}
		DBG(assert(args == r.size());)
#ifdef BIT_TRASNFORM
		if( opts.bitunv ) {
			if(bitunv_to_raw_term(rt))
				rt.calc_arity(nullptr);
		}
#endif
		return rt;
}

//---------------------------------------------------------
// unary string
//---------------------------------------------------------

unary_string::unary_string(size_t _pbsz): pbsz(_pbsz) {
	DBG(assert(sizeof(char32_t)*8 >= pbsz);)
	DBG(assert(pbsz  && !(pbsz & (pbsz-1)));) // power of 2 only, 1 2 4 8 16...
	vmask = ((uint64_t(1)<<(pbsz)) -1);
}

bool unary_string::buildfrom(u32string s) {
	if(!s.size()) return false;
	size_t n = (sizeof(s[0])<<3)/pbsz;
	sort_rel.resize(s.size()*n);
	for (size_t i=0; i < s.size(); i++)
		for (size_t a=0; a < n; a++) {
			rel[ char32_t(vmask & s[i]) ].insert(i*n+a),
			sort_rel[i*n+a] = char32_t(vmask & s[i]),
			s[i] = uint64_t(s[i]) >> pbsz;
		}
	return true;
}

string_t unary_string::getrelin_str(char32_t r) {
	return (r == '\0') ? to_string_t("00"): to_string_t(r);
}

ostream_t& unary_string::toprint(ostream_t& o) {
	for(size_t i = 0; i < sort_rel.size(); i++)
		if(isalnum(sort_rel[i]))
			o << to_string(to_string_t(sort_rel[i]))
				<< " " << i << endl;
		else o <<uint_t(sort_rel[i])<<"  "<< i <<endl;
	return o;
}

//---------------------------------------------------------
// FORMULA
//---------------------------------------------------------

bool ir_builder::to_pnf(form *&froot) {

	implic_removal impltrans;
	demorgan demtrans(true);
	pull_quantifier pullquant(this->dict);

	bool changed = false;
	changed = impltrans.traverse(froot);
	changed |= demtrans.traverse(froot);
	COUT << "\n ........... \n";
	froot->printnode(0, this);
	changed |= pullquant.traverse(froot);
	COUT << "\n ........... \n";
	froot->printnode(0, this);

	return changed;

}

form::ftype transformer::getdual( form::ftype type) {
	switch (type) {
		case form::ftype::OR : return form::ftype::AND;
		case form::ftype::AND : return form::ftype::OR;
		case form::ftype::FORALL1 : return form::ftype::EXISTS1 ;
		case form::ftype::FORALL2 : return form::ftype::EXISTS2 ;
		case form::ftype::EXISTS1 : return form::ftype::FORALL1 ;
		case form::ftype::EXISTS2 : return form::ftype::FORALL2 ;
		default: { DBGFAIL; return {}; }
	}
}

bool form::is_sol() {
	if (type == FORALL2 || type == EXISTS2 || type == UNIQUE2) return true;
	bool is_sol = false;
	if(l) is_sol |= l->is_sol();
	if(r && !is_sol) is_sol |= r->is_sol();
	return is_sol;
}

bool form::implic_rmoval() {
	implic_removal impltrans;
	auto ref = &(*this);
	return(impltrans.traverse(ref));
}

bool demorgan::push_negation( form *&root) {

	if(!root) return false;
	if( root->type == form::ftype::AND ||
		root->type == form::ftype::OR ) {

			root->type = getdual(root->type);
			if( ! push_negation(root->l) ||
				! push_negation(root->r))
					{ DBGFAIL; }
			return true;
	}
	else if ( allow_neg_move_quant && root->isquantifier()) {
			root->type = getdual(root->type);
			if( ! push_negation(root->r) ) { DBGFAIL; }

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

bool demorgan::apply(form *&root) {

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

			fresh_int = dt.get_new_var();
		else
			fresh_int = dt.get_new_sym();

		subst.add( temp->l->arg, fresh_int );

		COUT << "\nNew fresh: "<<temp->l->arg<<" --> "<<fresh_int;
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
				{ DBGFAIL; }
		curr->l = lprefend->r;
		curr->r = rprefend->r;
		lprefend->r = rprefbeg;
		rprefend->r = curr;
		root = lprefbeg;
		changed = true;
		COUT<<"\nPulled both: "<<lprefbeg->type<<" "<<lprefbeg->arg<<
			" , "<< rprefbeg->type << " " << rprefbeg->arg<< "\n";
	}
	else if(lprefbeg) {
		if(!dosubstitution(lprefbeg, lprefend))
			{ DBGFAIL; }
		curr->l = lprefend->r;
		lprefend->r = curr;
		root = lprefbeg;
		changed = true;
		COUT<<"\nPulled left: "<<lprefbeg->type<<" "<<lprefbeg->arg<<
			"\n";
	}
	else if (rprefbeg) {
		if(!dosubstitution(rprefbeg, rprefend))
			{ DBGFAIL; }
		curr->r = rprefend->r;
		rprefend->r = curr;
		root = rprefbeg;
		changed = true;
		COUT <<"\nPulled right: "<<rprefbeg->type<<" "<<rprefbeg->arg<<
			"\n";
	}
	return changed;
}

bool pull_quantifier::traverse(form *&root) {
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

void form::printnode(int lv, ir_builder* tb) {
	if (r) r->printnode(lv+1, tb);
	for (int i = 0; i < lv; i++) COUT << '\t';
	if( tb && this->tm != NULL)
		COUT << " " << type << " " << tb->to_raw_term(*tm) << "\n";
	else
		COUT << " " << type << " " << arg << "\n";
	if (l) l->printnode(lv+1, tb);
}

// ----------------------------------------------------
// GRAMMARS
// ----------------------------------------------------

bool ir_builder::get_substr_equality(const raw_term &rt, size_t &n,
	std::map<size_t,term> &refs, std::vector<term> &v, std::set<term> &/*done*/)
{
	//format : substr(1) = substr(2)
	term svalt;
	svalt.resize(4);
	#ifdef TYPE_RESOLUTION
	vector<native_type> tys((int_t) svalt.size(), UINT);
	svalt.tab = get_table(get_sig_typed(dict.get_lexeme("equals"), tys));
	#else
	svalt.tab = get_table(get_sig(dict.get_lexeme("equals"), {(int_t) svalt.size()}));
	#endif

	svalt.extype = term::textype::REL;

	for( int i=0; i<2 ; i++) {
		if( n >= rt.e.size() || rt.e[n].type != elem::SYM )
			return false;
		string_t attrib = lexeme2str(rt.e[n].e);
		if( !(!strcmp(attrib.c_str(), "substr")
			&& 	(n+3) < rt.e.size()
			&& 	rt.e[n+1].type == elem::OPENP
			&&	rt.e[n+2].type == elem::NUM
			&&	rt.e[n+3].type == elem::CLOSEP ) )
			return false;

		int_t pos =  rt.e[n+2].num;
		if( pos < 1 || pos >= (int_t)refs.size())
			parse_error("Wrong symbol index in substr", rt.e[n+2].e );


		if( refs[pos].size()) svalt[i*2] = refs[pos][0];
		// normal S( ?i ?j ) term, but for binary str(?i a) relation,
		// get the var by decrementing that at pos0
		//IMPROVE: Following code needs to aware of bitsz of unary string.
		//Currently, it assume whole char (32 bits) as a relation.
		if( refs[pos].size()==2)
			svalt[i*2+1] = refs[pos][1] >= 0 ? refs[pos][0]-1 : refs[pos][1];
		else if ( refs[pos].size()==1) // for unary str
			svalt[i*2+1] = refs[pos][0]-1;
		else
			parse_error("Incorrect term size for substr(index)");

		n += 4;  // parse sval(i)
		if( i == 0 && !( n < rt.e.size() &&
			(rt.e[n].type == elem::EQ || rt.e[n].type == elem::LEQ)))
			parse_error("Missing operator", rt.e[n].e );
		else if( i == 1 && n < rt.e.size())
			parse_error("Incorrect syntax", rt.e[n].e );
		else n++; //parse operator
	}
	v.push_back(move(svalt));
	return true;
}

int_t ir_builder::get_factor(raw_term &rt, size_t &n, std::map<size_t, term> &refs,
							std::vector<term> &v, std::set<term> &/*done*/){

	int_t lopd=0;
	if( n < rt.e.size() && rt.e[n].type == elem::SYM ) {
		string_t attrib = lexeme2str(rt.e[n].e);
		if( ! strcmp(attrib.c_str() , "len")
			&& 	(n+3) < rt.e.size()
			&& 	rt.e[n+1].type == elem::OPENP
			&&	rt.e[n+2].type == elem::NUM
			&&	rt.e[n+3].type == elem::CLOSEP ) {
				int_t pos =  rt.e[n+2].num;
				if( pos <0 || pos >= (int_t)refs.size())
					parse_error("Wrong symbol index in len", rt.e[n+2].e );

				if( refs[pos].size() > 1 ) {

					term lent;
					lent.resize(3), lent.tab = -1 ,
					lent.extype = term::textype::ARITH ,lent.arith_op = t_arith_op::ADD;

					lent[0] = refs[pos][0];
					if( refs[pos][1] < 0 )	lent[2] = refs[pos][1];
					else lent[2] = refs[pos][0] -1; // so len(i) refers to str relation

					lent[1] = dict.get_var(dict.get_lexeme(string("?len")+to_string_(pos)));
					lopd = lent[1];
					n += 4;
					//if(!done.insert(lent).second)
					v.push_back(lent);
				}
				else er("Wrong term for ref.");
			}
	}
	else if( n < rt.e.size() && rt.e[n].type == elem::NUM ) {
			lopd = mknum(rt.e[n].num);
			n += 1;
	}
	else er("Invalid start of constraint.");
	return lopd;
}

bool ir_builder::get_rule_substr_equality(vector<vector<term>> &eqr ){

	if (str_rels.size() > 1) er(err_one_input);
	if (str_rels.empty()) return false;
	eqr.resize(3); // three rules for substr equality
	for(size_t r = 0; r < eqr.size(); r++) {
		int_t var = 0;
		int_t i= --var, j= --var , k=--var, n= --var;

		#ifdef TYPE_RESOLUTION
		ntable nt = get_table(get_sig_typed(dict.get_lexeme("equals"), {UINT,UINT,UINT,UINT}));
		#else
		ntable nt = get_table(get_sig(dict.get_lexeme("equals"), {4}));
		#endif

		// making head   equals( i j k n) :-
		eqr[r].emplace_back(false, term::textype::REL, t_arith_op::NOP, nt,
								std::initializer_list<int>{i, j, k, n}, 0 );
		if( r == 0 ) {
			// making rule equals( i i k k) :- 0<=i, 0<=k. Inequalities are
			// used to force variables to be integers.
			// Turn equals( i j k n) into equals( i i k k)
			eqr[r].back().assign({i,i,k,k});
			// Add body term 0 <= i, forcing i to be an integer
			eqr[r].emplace_back(false, term::textype::LEQ, t_arith_op::NOP, -1,
				std::initializer_list<int>{mknum(0), i}, 0 );
			// Add body term 0 <= k, forcing k to be an integer
			eqr[r].emplace_back(false, term::textype::LEQ, t_arith_op::NOP, -1,
				std::initializer_list<int>{mknum(0), k}, 0 );
		} else if( r == 1 ) { // inductive case
			// equals(i j k n ) ;- str(i cv), str(k cv), i + 1 = j, k +1 = n.
			int_t cv = --var;
			// str(i cv) ,str( k, cv)
			for( int vi=0; vi<2; vi++) {
				//work in progress
				//DBG(COUT << "get_rule_substr_equality" << endl);
				#ifdef TYPE_RESOLUTION
				eqr[r].emplace_back(false, term::textype::REL, t_arith_op::NOP,
									get_table(get_sig_typed(*str_rels.begin(),{UINT,UCHAR})),
									std::initializer_list<int>{eqr[r][0][2*vi], cv} , 0);
				#else
				eqr[r].emplace_back(false, term::textype::REL, t_arith_op::NOP,
									get_table(get_sig(*str_rels.begin(),{2})),
									std::initializer_list<int>{eqr[r][0][2*vi], cv} , 0);

				#endif

			}
			eqr[r].emplace_back( false, term::ARITH, t_arith_op::ADD, -1,
								 std::initializer_list<int>{i, mknum(1), j}, 0);
			eqr[r].emplace_back( eqr[r].back());
			eqr[r].back()[0] = k, eqr[r].back()[2] = n ;
		}
		else if( r == 2) { // inductive case.
			//equals(i j k n ) :- equals( i x k y)	, equals( x j y n)
			int_t x = --var, y = --var;
			term eqs(false, term::textype::REL, t_arith_op::NOP, nt, { i, x, k, y }, 0);
			eqr[r].emplace_back(eqs);
			eqs.assign({x, j, y, n});
			eqr[r].emplace_back(eqs);
		}
	}
	return true;
}

bool ptransformer::parse_alt( vector<elem> &next, size_t& cur){
	bool ret = false;
	//size_t cur1 = cur;
	while( cur < next.size() && is_firstoffactor(next[cur])){
		ret = parse_factor(next, cur);
		if(!ret) break;
	}
		return ret;
}

bool ptransformer::is_firstoffactor(elem &c) {
	if(c.type == elem::SYM ||
		c.type == elem::STR ||
		c.type == elem::CHR ||
		c.type == elem::OPENB ||
		c.type == elem::OPENP ||
		c.type == elem::OPENSB )
		return true;
	else return false;
}

bool ptransformer::parse_alts( vector<elem> &next, size_t& cur){
	bool ret = false;
	while(cur < next.size()) {
		ret = parse_alt(next, cur);
		if(!ret) return false;
		if(cur < next.size() && next[cur].type == elem::ALT ) cur++;
		else break;
	}
	return ret;
}

lexeme ptransformer::get_fresh_nonterminal(){
	static size_t count=0;
	string fnt = "_R"+ to_string(lexeme2str(this->p.p[0].e))+ to_string(count++);
	return d.get_lexeme(fnt);
}

bool ptransformer::synth_recur(vector<elem>::const_iterator from,
		vector<elem>::const_iterator till, bool bnull = true, bool brecur = true,
		bool balt = true) {

	if (brecur) {
		bool binsidealt =false; // for | to be present inside
		for( vector<elem>::const_iterator f = from; f!=till; f++)
			if(f->type == elem::ALT) {binsidealt = true; break;}
		if (binsidealt) {
			synth_recur( from, till, false, false, false);
			from = lp.back().p.begin();
			till = lp.back().p.begin()+1;
		}
	}
	lp.emplace_back();
	production &np = lp.back();
	elem sym = elem(elem::SYM, get_fresh_nonterminal());
	np.p.push_back(sym);
	np.p.insert(np.p.end(), from , till);
	if(brecur) np.p.push_back(sym);
	elem alte = elem(elem::ALT, d.get_lexeme("|"));
	if (balt) np.p.emplace_back(alte);
	if (balt && bnull) {
		#ifdef NNULL_KLEENE
			np.p.insert(np.p.end(), from , till);
			np.p.emplace_back(elem::SYM, d.get_lexeme("_null_tg_"));
		#else
			np.p.emplace_back( elem::SYM, d.get_lexeme("null"));
		#endif
	}
	else if (balt) np.p.insert(np.p.end(), from, till);
	return true;
}

bool ptransformer::parse_factor( vector<elem> &next, size_t& cur){
	size_t cur1 = cur;
	if (cur >= next.size()) return false;
	if (next[cur].type == elem::SYM ||
		next[cur].type == elem::STR ||
		next[cur].type == elem::CHR) {
		size_t start = cur;
		++cur;
		if ((next.size() > cur) &&
			(next[cur].type == elem::ARITH) &&
			(next[cur].arith_op == MULT || next[cur].arith_op == ADD)) {
			//lp.emplace_back(),
			synth_recur( next.begin()+start, next.begin()+cur,
			next[cur].arith_op == MULT),
			++cur;
			next.erase(next.begin()+start, next.begin()+cur);
			next.insert(next.begin()+start, lp.back().p[0]);
			return cur = start+1, true;
		}
		return true;
	}
	if (next[cur].type == elem::OPENSB) {
		size_t start = cur;
		++cur;
		if( !parse_alts(next, cur)) return cur = cur1, false;
		if(next[cur].type != elem::CLOSESB) return false;
		++cur;
		//lp.emplace_back();
		synth_recur( next.begin()+start+1, next.begin()+cur-1, true, false);
		next.erase( next.begin()+start, next.begin()+cur);
		next.insert( next.begin()+start, lp.back().p[0]);
		return cur = start+1, true;
	}
	else if( next[cur].type == elem::OPENP ) {
		size_t start = cur;
		++cur;
		if( !parse_alts(next, cur)) return cur = cur1, false;
		if(next[cur].type != elem::CLOSEP) return false;
		++cur;
		//lp.emplace_back();
		if(next[cur].type == elem::ARITH &&
			(next[cur].arith_op == MULT 	||
			next[cur].arith_op == ADD		))
			// include brackets for correctness since it may contain alt
			synth_recur( next.begin()+start+1, next.begin()+cur-1,
			next[cur].arith_op == MULT),
			++cur;
		else //making R => ...
			synth_recur( begin(next)+start+1, begin(next)+cur -1,
			false, false, false);
		next.erase( next.begin()+start, next.begin()+cur);
		next.insert( next.begin()+start, this->lp.back().p[0]);
		return cur = start+1, true;
	}
	else if( next[cur].type == elem::OPENB ) {
		size_t start = cur;
		++cur;
		if( !parse_alts(next, cur)) return cur = cur1, false;
		if(next[cur].type != elem::CLOSEB) return false;
		++cur;
		//lp.emplace_back();
		// making R => ... R | null
		synth_recur( next.begin()+start+1, next.begin()+cur -1);
		next.erase( next.begin()+start, next.begin()+cur);
		next.insert( next.begin()+start, lp.back().p[0]);
		return cur = start+1, true;
	}
	else return cur = cur1, false;
}

bool ptransformer::visit() {
	size_t cur = 1;
	bool ret = this->parse_alts(this->p.p, cur);
	if (this->p.p.size() > cur) ret = false;
	//DBG(COUT << "transform_ebnf:visit" << endl << lp <<endl);
	if(!ret) parse_error("Error Production",
		cur < this->p.p.size() ? p.p[cur].e : p.p[0].e);
	return ret;
}

bool ir_builder::transform_ebnf(vector<production> &g, dict_t &d, bool &changed){
	bool ret= true;
	changed = false;
	for (size_t k = 0; k != g.size();k++) {
		ptransformer pt(g[k], d);
		if(!pt.visit()) return ret = false;
		g.insert( g.end(), pt.lp.begin(), pt.lp.end() ),
		changed |= pt.lp.size()>0;
	}
	return ret;
}

graphgrammar::graphgrammar(vector<production> &t, dict_t &_d): dict(_d) {
	for(production &p: t)
		if (p.p.size() < 2) parse_error(err_empty_prod, p.p[0].e);
		else _g.insert({p.p[0],std::make_pair(p, NONE)});
}

bool graphgrammar::dfs( const elem &s) {

	// get all occurrences of s and markin progress
	auto rang = _g.equal_range(s);
	for( auto sgit = rang.first; sgit != rang.second; sgit++)
		sgit->second.second = PROGRESS;

	for( auto git = rang.first; git != rang.second; git++)
		for( auto nxt= git->second.first.p.begin()+ 1; nxt != git->second.first.p.end(); nxt++ ) {
			if( nxt->type == elem::SYM ) {
				auto nang = _g.equal_range(*nxt);
				for( auto nit = nang.first; nit != nang.second; nit++)
					if( nit->second.second == PROGRESS ) return true;
					else if( nit->second.second != VISITED)
						if(  dfs(*nxt)) return true;
			//	for( auto nit = nang.first; nit != nang.second; nit++)
			//		nit->second.second = VISITED;
			//	sort.push_back(*nxt);
			}
		}
	for( auto sgit = rang.first; sgit != rang.second; sgit++)
		sgit->second.second = VISITED;
	sort.push_back(s);
	return false;
}

bool graphgrammar::detectcycle() {
	bool ret =false;
	for( auto it = _g.begin(); it != _g.end(); it++)
		if( it->second.second == NONE ) {
			if( dfs(it->first ) ) ret = true;
		}
	return ret;
}

bool graphgrammar::iscyclic( const elem &s) {
	auto rang = _g.equal_range(s);
	for( auto sgit = rang.first; sgit != rang.second; sgit++)
		if(sgit->second.second != VISITED) return true;
	return false;
}

const std::map<lexeme,string,lexcmp>& graphgrammar::get_builtin_reg() {
	static const map<lexeme,string,lexcmp> b =
		  { {dict.get_lexeme("alpha"), "[a-zA-Z]"},
		  {dict.get_lexeme("alnum"), "[a-zA-Z0-9]"},
		  {dict.get_lexeme("digit"), "[0-9]" },
		  {dict.get_lexeme("space"),  "[\\s]" },
		  {dict.get_lexeme("printable") , "[\\x20-\\x7F]"}
		};
		return b;
}

std::string graphgrammar::get_regularexpstr(const elem &p, bool &bhasnull, bool dolazy = false) {
	vector<elem> comb;
	static const set<char32_t> esc{ U'.', U'+', U'*', U'?', U'^', U'$', U'(', U',',
						U')',U'[', U']', U'{', U'}', U'|', U'\\'};
	static const string quantrep = "+*?}";

	static const map<lexeme,string,lexcmp> &b = get_builtin_reg();
	combine_rhs(p, comb);
	std::string ret;
	for(const elem &e: comb ) {
		if( e.type == elem::SYM && (e.e == "null") )
			bhasnull = true, ret.append("^$");
		else if( b.find(e.e) != b.end())
			ret.append(b.at(e.e));
		else if (e.type == elem::CHR) {
				if(esc.find(e.ch) != esc.end())
						ret.append("\\");
			ret.append(e.to_str());
		}
		else {
			ret.append(e.to_str());
			if( dolazy && quantrep.find(ret.back()) != string::npos)
				ret.append("?");
				/*
				| *  -->  *?
				| +  -->  +?
				| {n} --> {n}?
				*/

		}
	}
	return ret;
}

bool graphgrammar::combine_rhs( const elem &s, vector<elem> &comb) {
	lexeme alt = dict.get_lexeme("|");
	if( s.type != elem::SYM ) return false;
	auto rang2 = _g.equal_range(s);
	for( auto rit = rang2.first; rit != rang2.second; rit++) {
		production &prodr = rit->second.first;
		if(comb.size())	comb.push_back(elem(elem::ALT, alt));
		comb.insert(comb.end(), prodr.p.begin()+1, prodr.p.end());
		DBG(assert(rit->second.second == VISITED));
	}
	return true;
}

bool graphgrammar::collapsewith(){
	for( _itg_t it = _g.begin(); it != _g.end(); it++){
		DBG(COUT<< it->second.second << ":" << it->second.first.to_str(0)<<endl);
	}
	if(sort.empty()) return false;

	static const map<lexeme,string,lexcmp> &b = get_builtin_reg();
	for (elem &e: sort) {
		DBG(COUT<<e<<endl;)
		auto rang = _g.equal_range(e);
		for( auto sit = rang.first; sit != rang.second; sit++){

			production &prodc = sit->second.first;
			for( size_t i = 1 ; i < prodc.p.size(); i++) {
				elem &r = prodc.p[i];
				if( r.type == elem::SYM && !(r.e == "null") &&
					b.find(r.e) == b.end() ) {
					vector<elem> comb;
					combine_rhs(r, comb);
					comb.push_back(elem(elem::CLOSEP, dict.get_lexeme(")")));
					comb.insert(comb.begin(),elem(elem::OPENP, dict.get_lexeme("(")));
					prodc.p.erase(prodc.p.begin()+i);
					prodc.p.insert(prodc.p.begin()+i,
						comb.begin(), comb.end());
					i += comb.size() -2;
				}
			}

		}
	}
	return true;
}

bool ir_builder::transform_grammar_constraints(const production &x, vector<term> &v,
	flat_prog &p, std::map<size_t, term> &refs)
{
	std::set<term> done;
	bool beqrule = false;
	for( raw_term rt : x.c ) {

		size_t n = 0;
		if( get_substr_equality(rt, n, refs, v, done)) {
			// lets add equality rule since substr(i) is being used
			if(!beqrule) {
				vector<vector<term>> eqr;
				beqrule = get_rule_substr_equality(eqr);
				for( auto vt: eqr) p.insert(vt);
			}
			continue;
		}
		//every len constraint raw_term should be :
		//	(len(i)| num) [ bop (len(i)| num) ] (=) (len(i)| num)  ;
		// e.g. len(1) + 2 = 5  | len(1) = len(2
		n = 0;
		int_t lopd = get_factor(rt, n, refs, v, done);
		int_t ropd, oside;
		if( n < rt.e.size() && rt.e[n].type == elem::ARITH ) {
			// format : lopd + ropd = oside
			term aritht;
			aritht.resize(3);
			aritht.tab = -1;
			aritht.extype = term::textype::ARITH;
			aritht.arith_op = rt.e[n].arith_op;
			n++; // operator

			int_t ropd = get_factor(rt, n, refs, v, done);

			if( rt.e[n].type != elem::EQ)
				parse_error("Only EQ supported in len constraints. ", rt.e[n].e);
			n++; // assignment

			aritht[0] = lopd;
			aritht[1] = ropd;
			oside = get_factor(rt, n, refs, v, done);
			aritht[2] = oside;
			//if(!done.insert(aritht).second)
			if(n == rt.e.size())	v.push_back(aritht);
			else return er("Only simple binary operation allowed.");
		}
		else if( n < rt.e.size() &&
				(rt.e[n].type == elem::EQ || rt.e[n].type == elem::LEQ)) {
			//format: lopd = ropd
			term equalt;
			equalt.resize(2);
			equalt.extype = rt.e[n].type == elem::EQ ?
							term::textype::EQ : term::textype::LEQ;

			equalt[0]= lopd; //TODO: switched order due to bug <=
			n++; //equal
			ropd =  get_factor(rt, n, refs, v, done);
			equalt[1] = ropd;

			//if(!done.insert(equalt).second )
			if(n == rt.e.size())	v.push_back(equalt);
			else if( n < rt.e.size()
					&& rt.e[n].type == elem::ARITH
					&& equalt.extype == term::textype::EQ ) {
				//format: lopd = ropd + oside

					term aritht;
					aritht.resize(3);
					aritht.tab = -1;
					aritht.extype = term::textype::ARITH;
					aritht.arith_op = rt.e[n].arith_op;
					n++; // operator

					oside = get_factor(rt, n, refs, v, done);
					aritht[0] = ropd;
					aritht[1] = oside;
					aritht[2] = lopd;

					//if(!done.insert(aritht).second)
					if(n == rt.e.size())	v.push_back(aritht);
					else return er("Only simple binary operation allowed.");

			} else parse_error(err_constraint_syntax);
		}
		else parse_error(err_constraint_syntax, rt.e[n].e);
	}
	return true;
}

bool ir_builder::transform_grammar(vector<production> g, flat_prog& p) {
	if (g.empty()) return true;

	for (production& p : g)
		for (size_t n = 0; n < p.p.size(); ++n)
			if (p.p[n].type == elem::STR) {
				ccs s = p.p[n].e[0]+1;
				size_t chl, sl = p.p[n].e[1]-1 - s;
				char32_t ch;
				bool esc = false;
				p.p.erase(p.p.begin() + n);
				while ((chl = peek_codepoint(s, sl, ch)) > 0) {
					sl -= chl; s += chl;
					chars = max(chars, (int_t) ch);
					if (ch == U'\\' && !esc) esc = true;
					else p.p.insert(p.p.begin() + n++,
						elem(ch)), esc = false;
				}
			}
	clock_t start, end;
	int statterm=0;
	set<elem> torem;
	measure_time_start();
	bool enable_regdetect_matching = opts.apply_regexpmatch;
#ifdef LOAD_STRS
	if (strs.size() && enable_regdetect_matching) {
		string inputstr = to_string(strs.begin()->second);
#else
	if (dynenv->strs.size() && enable_regdetect_matching) {
		string inputstr = to_string(dynenv->strs.begin()->second);

#endif
		DBG(COUT<<inputstr<<endl);
		graphgrammar ggraph(g, dict);
		ggraph.detectcycle();
		ggraph.collapsewith();
		for(auto &elem : ggraph.sort) {
			bool bnull =false;
			string regexp = ggraph.get_regularexpstr(elem, bnull);
			DBG(COUT<<"Trying"<<regexp<<"for "<< elem<<endl);
			regex rgx;
#ifdef WITH_EXCEPTIONS
			try {
#else
// TODO: check regexp's validity another way?
#endif
				rgx = regexp;
#ifdef WITH_EXCEPTIONS
			} catch( ... ) {
				DBG(COUT<<"Ignoring Invalid regular expression"<<regexp);
				continue;
			}
#endif
			smatch sm;
			term t;
			bool bmatch=false;
			if(regex_level > 0) {
				for( size_t i = 0; i <= inputstr.size(); i++)
					for( size_t j = i; j <= inputstr.size(); j++)	{
						string ss = (i == inputstr.size()) ? "": inputstr.substr(i,j-i);
						if( regex_match(ss, sm, rgx)) {
							DBG(COUT << regexp << " match "<< sm.str() << endl);
							DBG(COUT << "len: " << sm.length(0) << std::endl);
							DBG(COUT << "size: " << sm.size() << std::endl);
							DBG(COUT << "posa: " << i + sm.position(0) << std::endl);
							t.resize(2);
							#ifdef TYPE_RESOLUTION
							t.tab = get_table(get_sig_typed(elem.e,{UINT,UINT}));
							#else
							t.tab = get_table(get_sig(elem.e,{2}));
							#endif
							t[0] = mknum(i), t[1] = mknum(i+ sm.length(0));
							p.insert({t});
							bmatch = true;
							statterm++;
						}
					}
				if(bmatch) torem.insert(elem);
			}
			else if( regex_level == 0) {
				std::sregex_iterator iter(inputstr.begin(), inputstr.end(), rgx );
				std::sregex_iterator end;
				for(;iter != end; ++iter) {
					DBG(COUT << regexp << " match "<< iter->str()<< endl);
					DBG(COUT << "size: " << iter->size() << std::endl);
					DBG(COUT << "len: " << iter->length(0) << std::endl);
					DBG(COUT << "posa: " << (iter->position(0) % (inputstr.length()+1)) << std::endl);
					t.resize(2);
					#ifdef TYPE_RESOLUTION
					t.tab = get_table(get_sig_typed(elem.e,{UINT,UINT}));
					#else
					t.tab = get_table(get_sig(elem.e,{2}));
					#endif
					t[0] = mknum(iter->position(0)), t[1] = mknum(iter->position(0)+iter->length(0));
					p.insert({t});
					statterm++;
				}
			}
		}
		size_t removed = 0;
		for( auto pit = g.begin(); pit != g.end(); )
			if(regex_level > 1  && torem.count(pit->p[0]) > 0 && removed < (size_t)(regex_level-1)) {
				o::ms()<<*pit<<endl;
				pit = g.erase(pit);
				removed++;
			} else pit++;

		o::ms()<<"REGEX: "<<"terms added:"<<statterm<<" production removed:"
		<<removed<<" for "<< torem.size()<<endl;
	}
	measure_time_end();
	bool changed;
	if(!transform_ebnf(g, dict, changed )) return true;

	for (size_t k = 0; k != g.size();) {
		if (g[k].p.size() < 2) parse_error(err_empty_prod, g[k].p[0].e);
		size_t n = 0;
		while (n < g[k].p.size() && g[k].p[n].type != elem::ALT) ++n;
		if (n == g[k].p.size()) { ++k; continue; }
		g.push_back({ vector<elem>(g[k].p.begin(), g[k].p.begin()+n) });
		g.push_back({ vector<elem>(g[k].p.begin()+n+1, g[k].p.end()) });
		g.back().p.insert(g.back().p.begin(), g[k].p[0]);
		g.erase(g.begin() + k);
	}
	DBG(o::out()<<"grammar after:"<<endl);
	DBG(for (production& p : g) o::out() << p << endl;)

	vector<term> v;

	#define GRAMMAR_BLTINS
	#ifdef GRAMMAR_BLTINS
	static const set<string> b =
		{ "alpha", "alnum", "digit", "space", "printable" };
	set<lexeme, lexcmp> builtins;
	for (const string& s : b) builtins.insert(dict.get_lexeme(s));
	#endif

	for (const production& x : g) {

		if (x.p.size() == 2 && x.p[1].e == "null") {
			term t;
			t.resize(2);
			t[0] = t[1] = -1;
		#ifdef TYPE_RESOLUTION
			t.tab = get_table(get_sig_typed(x.p[0].e, {UINT,UINT}));
		#else
			t.tab = get_table(get_sig(x.p[0].e,{2}));
		#endif
			// Ensure that the index is an integer by asserting that it is >= 0
			term guard;
			guard.resize(2);
			guard.extype = term::LEQ;
			guard[0] = mknum(0);
			guard[1] = -1;
			// Make the rule x(?a ?a) :- 0 <= ?a
			vector<term> v{t, guard};
			p.insert(v);
			vector<term> af{t, t};
			af[0].neg = true;
			align_vars(af);
			dynenv->prog_after_fp.insert(move(af));
			continue;
		}

		std::map<size_t, term> refs; //refs: maps ith prod. symbol to terms

		for (int_t n = 0; n != (int_t)x.p.size(); ++n) {
			term t;
			#ifdef GRAMMAR_BLTINS
			if (builtins.find(x.p[n].e) != builtins.end()) {
				#ifdef TYPE_RESOLUTION
				t.tab = get_table(get_sig_typed(*str_rels.begin(), {SYMB,UINT,UINT}));
				#else
				t.tab = get_table(get_sig(*str_rels.begin(), {3}));
				#endif
				t.resize(3), t[0] = mksym(dict.get_sym(x.p[n].e)),
				t[1] = -n, t[2] = mknum(0);
				term plus1;
				plus1.tab = -1;
				plus1.resize(3);
				plus1.extype = term::textype::ARITH;
				plus1.arith_op = t_arith_op::ADD;
				plus1[0]= -n, plus1[1]=mknum(1), plus1[2]=-n-1;
				v.push_back(move(plus1));
			} else
			#endif
			if (x.p[n].type == elem::SYM) {
				t.resize(2);
				#ifdef TYPE_RESOLUTION
				t.tab = get_table(get_sig_typed(x.p[n].e,{UINT,UINT}));
				#else
				t.tab = get_table(get_sig(x.p[n].e,{2}));
				#endif
				if (n) t[0] = -n, t[1] = -n-1;
				else t[0] = -1, t[1] = -(int_t)(x.p.size());
			} else if (x.p[n].type == elem::CHR) {
				unary_string us(sizeof(char32_t)*8);
				us.buildfrom(u32string(1, x.p[n].ch));
				int_t tv=n;
				//DBG(us.toprint(o::dbg()));
				for( auto rl: us.sort_rel) {
					term t; t.resize(1);
					#ifdef TYPE_RESOLUTION
					t.tab = get_table(get_sig_typed(dict.get_lexeme(us.getrelin_str(rl)), {UINT}));
					#else
					t.tab = get_table(get_sig(dict.get_lexeme(us.getrelin_str(rl)), {1}));
					#endif
					t[0] = -tv;
					term plus1;
					plus1.resize(3);
					plus1.tab = -1;
					plus1.extype = term::textype::ARITH;
					plus1.arith_op = t_arith_op::ADD;
					plus1[0] = -tv, plus1[1] = mknum(1), plus1[2] = -tv-1;

					v.push_back(move(plus1));
					v.push_back(move(t));
					// IMPROVE FIX: the symbol index n e.g. in len(i) should refer
					// to what is the relative position inside the rhs of production. This
					// should change when pbsz of unary_str is NOT sizeof(char32_t)*8.
					refs[n] = v.back();
					tv++;
				}
				continue;

			} else return er("Unexpected grammar element");
			v.push_back(move(t));
			refs[n] = v.back();
		}
		// add vars to dictionary to avoid collision with new vars
		for(int_t i =-1; i >= (int_t)-x.p.size(); i--)
			dict.get_var_lexeme(dict.get_new_var());

		transform_grammar_constraints(x, v, p, refs);

		p.insert(move(v));
	}
	if (opts.print_transformed) printer->print(printer->print(o::to("transformed")
		<< "\n# after transform_grammar:\n", p)
		<< "\n# run after a fixed point:\n", dynenv->prog_after_fp)
		<< endl;
	return true;
}

// ----------------------------------------------------
// STRINGS
// ----------------------------------------------------
#ifdef LOAD_STRS
void ir_builder::load_string(flat_prog &fp, const lexeme &r, const string_t& s) {

	nums = max(nums, (int_t) s.size()+1); //this is to have enough for the str index
	unary_string us(sizeof(char32_t)*8);
	chars = max(chars, (int_t) us.rel.size()); //TODO: review this one
	vector<term> v;
	us.buildfrom(s);
	for (auto it: us.rel) {
		term t; t.resize(1);
#ifdef TYPE_RESOLUTION
		ntable tb = get_table(get_sig_typed(dict.get_lexeme(us.getrelin_str(it.first)), {UINT}));
#else
		ntable tb = get_table(get_sig(dict.get_lexeme(us.getrelin_str(it.first)), {1}));
#endif
		t.tab = tb;
		for (int_t i : it.second)
			t[0] = mknum(i), v.push_back(t), fp.insert(move(v));
	}
	//FIXME: these are always the same for all eventual strs, so could be stored
	const int_t sspace = dict.get_sym(dict.get_lexeme("space")),
		salpha = dict.get_sym(dict.get_lexeme("alpha")),
		salnum = dict.get_sym(dict.get_lexeme("alnum")),
		sdigit = dict.get_sym(dict.get_lexeme("digit")),
		sprint = dict.get_sym(dict.get_lexeme("printable"));
	//updating syms universe size after creating new syms,
	syms = dict.nsyms();

	int_t rel = dict.get_rel(r);
	term t(2),tb(3);
	#ifdef TYPE_RESOLUTION
	t.tab = get_table(get_sig_typed(r, {UINT, UCHAR}));
	tb.tab =  get_table(get_sig_typed(r, {SYMB, UINT, UINT}));
	#else
	t.tab = get_table(get_sig(r, {2}));
	tb.tab =  get_table(get_sig(r, {3}));
	#endif
	for (int_t n = 0; n != (int_t)s.size(); ++n) {
		t[0] = mknum(n), t[1] = mkchr(s[n]); // t[2] = mknum(n + 1),
		chars = max(chars, t[1]);
		v.push_back(t), fp.insert(move(v));
		tb[1] = t[0], tb[2] = mknum(0);
		if (isspace(s[n])) tb[0] = mksym(sspace), v.push_back(tb), fp.insert(move(v));
		if (isdigit(s[n])) tb[0] = mksym(sdigit), v.push_back(tb), fp.insert(move(v));
		if (isalpha(s[n])) tb[0] = mksym(salpha), v.push_back(tb), fp.insert(move(v));
		if (isalnum(s[n])) tb[0] = mksym(salnum), v.push_back(tb), fp.insert(move(v));
		if (isprint(s[n])) tb[0] = mksym(sprint), v.push_back(tb), fp.insert(move(v));
	}
	str_rels.insert(rel);
}

void ir_builder::load_strings_as_fp(flat_prog &fp, const strs_t& s) {
	strs = s;
	for (auto x : strs) {
		load_string(fp, x.first, x.second);
	}
}
#endif
