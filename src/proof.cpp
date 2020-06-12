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
#include "tables.h"
#include "input.h"
#include "output.h"

using namespace std;

vector<env> tables::varbdd_to_subs(
	const alt* a, ntable tab, cr_spbdd_handle v) const
{
	vector<env> r;
	//decompress(v, 0, [a, &r](const term& x) {
	decompress(v, tab, [a, &r](const term& x) {
		env m;
		// D: VM: refactor this (and is questionable)
		// why not use .vm, as we're iterating them all and var<->pos is 1<->1
		for (auto z : a->vm) {
			//inv.emplace(z.second.id, z.first);
			if (!m.emplace(z.first, x[z.second.id]).second)
				throw 0;
		}
		//for (auto z : a->inv)
		//	if (!m.emplace(z.second, x[z.first]).second)
		//		throw 0;
		r.emplace_back(move(m));
	}, a->varslen, a);
	return r;
}

vector<term> subs_to_rule(const rule& r, const alt* a, const map<int, int>& e) {
	static vector<term> hb;
	hb.clear(), hb.reserve(a->size() + 1),
	hb.push_back(r.t), hb.insert(hb.end(), a->t.begin(), a->t.end());
	for (term& t : hb) for (int_t& i : t) if (i < 0) i = e.at(i);
	return hb;
}

vector<term> subs_to_body(const alt* a, const map<int, int>& e) {
	static vector<term> b;
	b = a->t;
	for (term& t : b) for (int_t& i : t) if (i < 0) i = e.at(i);
	return b;
}

void tables::rule_get_grounds(cr_spbdd_handle& h, size_t rl, size_t level,
	cb_ground f) {
	ntable tab = rules[rl].tab;
	table& tbl = tbls[tab];
	DBG(assert(rules[rl].t.size() == tbl.bm.get_args()););
	for (size_t n = 0; n != rules[rl].size(); ++n) {
		const alt* a = rules[rl][n];
		DBG(assert(a->varslen == a->bm.get_args()););
		if (has(a->levels, level)) {
			spbdd_handle htemp = addtail(*a, h, tbl.bm, a->bm);
			for (const env& e : varbdd_to_subs(a, tab, move(htemp))) {
				f(rl, level, n, move(subs_to_body(a, e)));
			}
		}
	}
}

void tables::term_get_grounds(const term& t, size_t level, cb_ground f) {
	spbdd_handle h = from_fact(t), x;
	if (!level) f(-1, 0, -1, {t});
	if (level > 1) {
		spbdd_handle x = levels[level-1][t.tab] && h,
					 y = levels[level][t.tab] && h;
		if (t.neg?(hfalse==x||hfalse!=y):(hfalse!=x||hfalse==y)) return;
	}
	for (size_t r : tbls[t.tab].r)
		if (rules[r].neg == t.neg)
			rule_get_grounds(h, r, level, f);
}

set<tables::witness> tables::get_witnesses(const term& t, size_t l) {
	set<witness> r;
	term_get_grounds(t, l, [&r](size_t rl, size_t, size_t al,
		const vector<term>& b) { 
			r.emplace(rl, al, b); 
		});
	return r;
}

/*void tables::explain(proof_elem& e) const {
	for (size_t n = 0; n != e.b.size(); ++n)
		if (e.b[n].first == -1) {
		}
}

const set<proof_elem>& tables::explain(const term& q, proof& p, size_t level) {
	set<witness> s;
	proof_elem e;
	if (!level) return 0;
	if (auto it = p[level].find(q); it != p.end()) {
		set<proof_elem> x

		for (const proof_elem& e : it->second) {
			for (const auto& b : e.b) if (b.first == -1) x.insert(e);
			if (x.empty()) continue;
			for (const proof_elem& e : x) it->second.erase(e);
		}
		return it->second;
	}
	while ((s = get_witnesses(q, level)).empty()) if (!level--) return 0;
	bool f;
	for (const witness& w : s) {
//		DBG(o::out()<<L"witness: "; print(o::out(), w); o::out()<<endl;)
		e.rl = w.rl, e.al = w.al, e.b.clear(), e.b.reserve(w.b.size());
		for (const term& t : w.b) {
			f = false;
			for (size_t n = level; n--;)
				if (p[n].find(t) != p[n].end()) {
					f = true;
					e.b.emplace_back(n, t);
					break;
				}
			if (f) continue;
			e.b.emplace_back(level?get_proof(t,p,level-1,2):0, t);
		}
		p[level][q].insert(e);
	}
	return p[level][q];
}*/

size_t tables::get_proof(const term& q, proof& p, size_t level, size_t dep) {
	set<witness> s;
	proof_elem e;
	if (!level) return 0;
	if (!--dep) return -1;
//	DBG(o::out()<<L"current p: " << endl; print(o::out(), p);)
//	DBG(o::out()<<L"proving " << to_raw_term(q) << L" level "<<level<<endl;)
	while ((s = get_witnesses(q, level)).empty())
		if (!level--)
			return 0;
	bool f;
	for (const witness& w : s) {
//		DBG(o::out()<<L"witness: "; print(o::out(), w); o::out()<<endl;)
		e.rl = w.rl, e.al = w.al, e.b.clear(), e.b.reserve(w.b.size());
		for (const term& t : w.b) {
			f = false;
			for (size_t n = level; n--;)
				if (p[n].find(t) != p[n].end()) {
					f = true;
					e.b.emplace_back(n, t);
					break;
				}
			if (f) continue;
			e.b.emplace_back(level?get_proof(t,p,level-1,dep):0, t);
		}
		p[level][q].insert(e);
	}
	return level;
}


void tables::print_dot(std::wstringstream &ss, gnode &gh, std::set<gnode*> &visit, int space) {

	std::wstring sp;
	for(int i=0; i< space; i++)	sp += L"\t";
	
	if(!visit.insert(&gh).second) return;
	if( gh.type == gnode::gntype::symbol)
		ss  << endl<< sp << size_t(&gh) << L"[label=\""<<gh.lev<< " "<< to_raw_term(gh.t)<< L"\"];";
	else
		ss  << endl<< sp << size_t(&gh) << L"[shape = \"point\" label=\""<< L"\"];";
	
	for( const auto& x:gh.next) {
		ss << std::endl << size_t(&gh) << L"->" << size_t(x)<< L';';
		print_dot(ss, *x, visit, space+1);
	}
}

bool tables::build( std::map<std::pair<int,term>, gnode*> &tg, proof &p, gnode &g){
	
	for( int i = p.size()-1 ; i >= 0 ; i--) {
		if( p[i].find(g.t) != p[i].end() && i == g.lev ) {
			
			for( const auto &pfe : p[i][g.t]) {
				g.next.emplace_back(new gnode(i, g.t, gnode::gntype::pack));

				for( const auto &nt : pfe.b) {
					auto it = tg.find(nt);
					if( it == tg.end()) {
						gnode *cur = new gnode(nt.first,nt.second);
						tg[nt] = cur; 
	
						g.next.back()->next.emplace_back(cur);
						build(tg, p, *cur);
					}
					else g.next.back()->next.emplace_back( it->second);
					
				}
			}
		}		
	}	
	return true;
}
bool tables::isvalid( const raw_term &rt) {
	
	if( rt.e.size() == 5  &&         // Symbol(pos1, pos2 )
		rt.e[0].type == elem::SYM &&
		rt.e[2].type == elem::NUM &&
		rt.e[3].type == elem::NUM &&
		rt.e[3].num < rt.e[2].num  ) {
		
			return false;
	} 
	else if( rt.e.size() == 16  &&         // str(((2))('+')((5)))
		rt.e[0].type == elem::SYM &&
		rt.e[4].type == elem::NUM &&
		rt.e[12].type == elem::NUM &&
		((rt.e[12].num - rt.e[4].num) != 1)  ) {	
			return false;				
		}
	return true;
}
bool tables::prune_proof( proof &p) {

	bool done=false;
	int cheadrem=0, cbodyrem=0;
	for( int i = 0 ; i < p.size() ; i++) {
		for( auto mit = p[i].begin(); mit!= p[i].end();) {		
			raw_term rt = to_raw_term(mit->first);
			if(!isvalid(rt)) {
				DBG(o::dbg()<<endl<<L"Pruning " <<rt<<endl;)
				mit = p[i].erase(mit);
				cheadrem++;
			} 
			else {
				for( auto pfeit = mit->second.begin(); pfeit!= mit->second.end();) {
					bool btvalid = true;
					for( const auto &nt : pfeit->b) {
						raw_term brt = to_raw_term(nt.second);
						bool ispresent = (bdd_handle::F != (tbls[nt.second.tab].tq && from_fact(nt.second)) );
								 
						btvalid = isvalid(brt);
						
						if(!btvalid) {
							DBG(o::dbg()<<endl<<L"Pruning proof element body of "<<ispresent<<L" " <<rt<<L" due to "<<brt<<endl;)
							pfeit = mit->second.erase(pfeit);
							cbodyrem++;
							break;
						} 
					}
					if(btvalid)  pfeit++;
				}
				if(mit->second.size() == 0 ) 
					mit = p[i].erase(mit), cheadrem++;
				else mit++;
			}
		}
	}
	DBG(o::dbg()<<endl<<L"Pruned proof : headcount, bodycount:"<< cheadrem << "," <<cbodyrem<<endl;)
	if(cheadrem || cbodyrem) return true;
	else return false;
}
gnode* tables::get_forest(std::wostream&os, const term& t, proof& p ) {

	std::map<pair<int,term>, gnode*> tg;
	set<gnode*> v;
	std::wstringstream ss;
	gnode* root =  nullptr;
	for(int i =p.size()-1; i >=0; i-- )
		if( p[i].find(t) != p[i].end() ) {
			root = new gnode(i,t);
			if( tg.find({i,t}) == tg.end() ) {
				tg[{i,t}] = root; 
				build(tg, p, *root);
				print_dot(ss, *root, v);
			}
			else delete root;
		}
	os<< L"digraph {" << endl<< ss.str() << endl<<L"}"<<endl;

	return root;
}

bool tables::get_goals(wostream& os) {
	proof p(levels.size());
	set<term> s;
	
	for (const term& t : goals)
		decompress(tbls[t.tab].tq && from_fact(t), t.tab,
			[&s](const term& t) { s.insert(t); }, t.size());
	for (const term& g : s)
		if (bproof) {
			get_proof(g, p, levels.size() - 1);
			prune_proof( p );
			get_forest(os, g, p);
		}
		else os << to_raw_term(g) << L'.' << endl;
	if (bproof) print(os, p);
	return goals.size() || bproof;
}
