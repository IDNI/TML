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

/* Ensure that the current variable instantiations are legal. Needed for proving
 * negative facts by showing that no variable instantiation would satisfy rules
 * of a relation. */

bool tables::is_term_valid(const term &t) {
	return true;
}


/* For the given table and sign, make a rule that positively or negatively
 * carries all table facts from the previous step to the next step. */

rule tables::new_identity_rule(const ntable tab, const bool neg) {
	// Make the identity term
	term tm;
	tm.tab = tab;
	tm.neg = neg;
	for(size_t i = 0; i < tbls[tab].len; i++) tm.push_back(-i-1);
	// Make a rule alternative based on the term
	set<alt> alts_singleton;
	get_alt({ tm }, tm, alts_singleton);
	assert(alts_singleton.size() == 1);
	alt *dyn_alt = new alt;
	*dyn_alt = *alts_singleton.begin();
	// Populate the alternative's history in order to allow recognition of carrys
	// in proof tree generation
	for(size_t lev = 0; lev < levels.size(); lev++)
		dyn_alt->levels[lev+1] = neg ? (htrue % levels[lev][tab]) : levels[lev][tab];
	// To ensure that this alternative is eventually freed by tables destructor
	alts.insert(dyn_alt);
	// Make an identity rule based on the alternative
	rule rul;
	rul.eq = htrue;
	rul.t = tm;
	rul.neg = neg;
	rul.tab = tab;
	rul.len = tbls[tab].len;
	rul.push_back(dyn_alt);
	return rul;
}


std::set<const gnode*> gnode::visited;
std::map<std::set<term>, gnode*> gnode::interm2g;

bool gnode::_binarise() {

	if (visited.insert(this).second == false) return false;

	bool done = false;
	if( this->type == gntype::pack &&
		this->next.size() > 2 ) { // the first node is not changed
			gnode* gninter = nullptr;
			std::vector<gnode*> temp(next.begin()+1, next.end());
			std::set<term> key;
			for( auto &gn: temp )
				key.insert( gn->t );
			if( interm2g.find( key ) != interm2g.end() )
				gninter = interm2g[key];
			else
				gninter = new gnode( lev, t, temp ),
				interm2g[key]= gninter;

			this->next.erase(next.begin()+1, next.end());
			this->next.push_back(gninter);
			done = true;
		}

	for( gnode *gn : next)	done |= gn->_binarise();

	return done;
}


void tables::print_dot(std::wstringstream &ss, gnode &gh, std::set<gnode*> &visit, int space) {

	std::wstring sp;
	for(int i=0; i< space; i++)	sp += L"\t";

	if(!visit.insert(&gh).second) return;
	if( gh.type == gnode::gntype::symbol)
		;
	else if (gh.type == gnode::gntype::pack)
		ss  << endl<< sp << size_t(&gh) << L"[shape = \"point\" label=\""<< L"\"];";
	else if (gh.type == gnode::gntype::interm)
		ss  << endl<< sp << size_t(&gh) << L"[shape = \"rectangle\" label=\""<< L"\"];";
	for( const auto& x:gh.next) {
		ss << std::endl << sp << size_t(&gh) << L"->" << size_t(x)<< L';';
		print_dot(ss, *x, visit, space+1);
	}
}

bool tables::build_graph( std::map<term , gnode*> &tg, proof &p, gnode &g){

	for( int i = p.size()-1 ; i >= 0 ; i--) {
		if( p[i].find(g.t) != p[i].end() && i == g.lev ) {

			for( const auto &pfe : p[i][g.t]) {
				g.next.emplace_back(new gnode(i, g.t, gnode::gntype::pack));

				for( const auto &nt : pfe.b) {
					auto it = tg.find(nt.second);
					if( it == tg.end()) {
						gnode *cur = new gnode(nt.first, nt.second);
						tg[nt.second] = cur;
						g.next.back()->next.emplace_back(cur);
						build_graph(tg, p, *cur);
					}
					else g.next.back()->next.emplace_back( it->second);
				}
			}
		}
	}
	return true;
}

