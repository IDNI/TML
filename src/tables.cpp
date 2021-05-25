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
#include <regex>
#include "tables.h"
#include "dict.h"
#include "input.h"
#include "output.h"
using namespace std;

#define mkchr(x) (opts.bitunv? ((int_t)(x)):(((((int_t)(x))<<2)|1)))
#define mknum(x) (opts.bitunv? ((int_t)(x)):(((((int_t)(x))<<2)|2)))

//#define mkchr(x) ((((int_t)x)))
//#define mknum(x) ((((int_t)x)))

size_t sig_len(const sig& s) {
	size_t r = 0;
	for (int_t x : get<ints>(s)) if (x > 0) r += x;
	return r;
}

void unquote(string_t& str) {
	for (size_t i = 0; i != str.size(); ++i)
		if (str[i] == (unsigned char) '\\') str.erase(str.begin() + i);
}

string_t _unquote(string_t str) { unquote(str); return str; }

#ifdef DEBUG
vbools tables::allsat(spbdd_handle x, size_t args) const {
//	const size_t args = siglens[tab];
	vbools v = ::allsat(x, bits * args), s;
	for (bools b : v) {
		s.emplace_back(bits * args);
		for (size_t n = 0; n != bits; ++n)
			for (size_t k = 0; k != args; ++k)
				s.back()[(k+1)*bits-n-1] = b[pos(n, k, args)];
	}
	return s;
}
#endif

spbdd_handle tables::leq_const(int_t c, size_t arg, size_t args, size_t bit)
	const
{
	if (!--bit)
		return	(c & 1) ? htrue :
			::from_bit(pos(0, arg, args), false);
	return (c & (1 << bit)) ?
		bdd_ite_var(pos(bit, arg, args), leq_const(c, arg, args, bit),
			htrue) :
		bdd_ite_var(pos(bit, arg, args), hfalse,
			leq_const(c, arg, args, bit));
}

typedef tuple<size_t, size_t, size_t, int_t> skmemo;
typedef tuple<size_t, size_t, size_t, int_t> ekmemo;
map<skmemo, spbdd_handle> smemo;
map<ekmemo, spbdd_handle> ememo;
map<ekmemo, spbdd_handle> leqmemo;

spbdd_handle tables::leq_var(size_t arg1, size_t arg2, size_t args) const {
	static ekmemo x;
	static map<ekmemo, spbdd_handle>::const_iterator it;
	if ((it = leqmemo.find(x = { arg1, arg2, args, bits })) != leqmemo.end())
		return it->second;
	spbdd_handle r = leq_var(arg1, arg2, args, bits);
	return leqmemo.emplace(x, r), r;
}

spbdd_handle tables::leq_var(size_t arg1, size_t arg2, size_t args, size_t bit)
	const
{
	if (!--bit)
		return	bdd_ite(::from_bit(pos(0, arg2, args), true),
				htrue,
				::from_bit(pos(0, arg1, args), false));
	return	bdd_ite(::from_bit(pos(bit, arg2, args), true),
			bdd_ite_var(pos(bit, arg1, args),
				leq_var(arg1, arg2, args, bit), htrue),
			bdd_ite_var(pos(bit, arg1, args), hfalse,
				leq_var(arg1, arg2, args, bit)));
}

void tables::range(size_t arg, size_t args, bdd_handles& v) {
	spbdd_handle	ischar= ::from_bit(pos(0, arg, args), true) &&
			::from_bit(pos(1, arg, args), false);
	spbdd_handle	isnum = ::from_bit(pos(0, arg, args), false) &&
			::from_bit(pos(1, arg, args), true);
	spbdd_handle	issym = ::from_bit(pos(0, arg, args), false) &&
			::from_bit(pos(1, arg, args), false);
	// nums is set to max NUM, not universe size. While for syms it's the size.
	// It worked before because for arity==1 fact(nums) is always negated.
	bdd_handles r = {ischar || isnum || issym,
		(!chars	? htrue%ischar : bdd_impl(ischar,
			leq_const(mkchr(chars-1), arg, args, bits))),
		(!nums 	? htrue%isnum : bdd_impl(isnum,
			leq_const(mknum(nums), arg, args, bits))),
		(!syms 	? htrue%issym : bdd_impl(issym,
			leq_const(((syms-1)<<2), arg, args, bits)))};
	v.insert(v.end(), r.begin(), r.end());
}

spbdd_handle tables::range(size_t arg, ntable tab) {
	array<int_t, 6> k = { syms, nums, chars, (int_t)tbls[tab].len,
		(int_t)arg, (int_t)bits };
	auto it = range_memo.find(k);
	if (it != range_memo.end()) return it->second;
	bdd_handles v;
	return	range(arg, tbls[tab].len, v),
		range_memo[k] = bdd_and_many(move(v));
}

uints perm_init(size_t n) {
	uints p(n);
	while (n--) p[n] = n;
	return p;
}

spbdd_handle tables::add_bit(spbdd_handle x, size_t args) {
	uints perm = perm_init(args * bits);
	for (size_t n = 0; n != args; ++n)
		for (size_t k = 0; k != bits; ++k)
			perm[pos(k, n, args)] = pos(k+1, bits+1, n, args);
	bdd_handles v = { x ^ perm };
	for (size_t n = 0; n != args; ++n)
		v.push_back(::from_bit(pos(0, bits + 1, n, args), false));
	return bdd_and_many(move(v));
}

void tables::add_bit() {
	range_clear_memo();
	spbdd_handle x = hfalse;
	bdd_handles v;
	for (auto& x : tbls)
//	for (size_t n = 0; n != ts.size(); ++n)
//		x.second.t = add_bit(x.second.t, x.second.len);
		x.t = add_bit(x.t, x.len);
	++bits;
}

//typedef tuple<size_t, size_t, size_t, int_t> skmemo;
//typedef tuple<size_t, size_t, size_t, int_t> ekmemo;
//map<skmemo, spbdd_handle> smemo;
//map<ekmemo, spbdd_handle> ememo;
//map<ekmemo, spbdd_handle> leqmemo;

spbdd_handle tables::from_sym(size_t pos, size_t args, int_t i) const {
	static skmemo x;
	static map<skmemo, spbdd_handle>::const_iterator it;
	if ((it = smemo.find(x = { i, pos, args, bits })) != smemo.end())
		return it->second;
	spbdd_handle r = htrue;
	for (size_t b = 0; b != bits; ++b) r = r && from_bit(b, pos, args, i);
	return smemo.emplace(x, r), r;
}

spbdd_handle tables::from_sym_eq(size_t p1, size_t p2, size_t args) const {
	static ekmemo x;
	// a typo should be ekmemo, all the same at the moment
	//static map<skmemo, spbdd_handle>::const_iterator it;
	static map<ekmemo, spbdd_handle>::const_iterator it;
	if ((it = ememo.find(x = { p1, p2, args, bits })) != ememo.end())
		return it->second;
	spbdd_handle r = htrue;
	for (size_t b = 0; b != bits; ++b)
		r = r && ::from_eq(pos(b, p1, args), pos(b, p2, args));
	return ememo.emplace(x, r), r;
}

spbdd_handle tables::from_fact(const term& t) {
	// TODO: memoize
	spbdd_handle r = htrue;
	static varmap vs;
	vs.clear();
	auto it = vs.end();
	for (size_t n = 0, args = t.size(); n != args; ++n)
		if (t[n] >= 0) r = r && from_sym(n, args, t[n]);
		else if (vs.end() != (it = vs.find(t[n])))
			r = r && from_sym_eq(n, it->second, args);
		else if (vs.emplace(t[n], n), !t.neg)
			r = r && range(n, t.tab);
	return r;
}

sig tables::get_sig(const raw_term&t) {return{dict.get_rel(t.e[0].e),t.arity};}
sig tables::get_sig(const lexeme& rel, const ints& arity) {
	return { dict.get_rel(rel), arity };
}

term tables::from_raw_term(const raw_term& r, bool isheader, size_t orderid) {
	ints t;
	lexeme l;
	size_t nvars = 0;

	//FIXME: this is too error prone.
	// D: make sure enums match (should be the same), cast is just to warn.
	term::textype extype = (term::textype)r.extype;

	// D: header builtin is treated as rel, but differentiated later (decomp.)
	bool realrel = extype == term::REL || (extype == term::BLTIN && isheader);
	// skip the first symbol unless it's EQ/LEQ/ARITH (which has VAR/CONST as 1st)
	bool isrel = realrel || extype == term::BLTIN;
	for (size_t n = !isrel ? 0 : 1; n < r.e.size(); ++n)
		switch (r.e[n].type) {
			case elem::NUM: t.push_back(mknum(r.e[n].num)); break;
			case elem::CHR: t.push_back(mkchr(r.e[n].ch)); break;
			case elem::VAR:
				++nvars;
				t.push_back(dict.get_var(r.e[n].e));
				break;
			case elem::STR:
				l = r.e[n].e;
				++l[0], --l[1];
				t.push_back(dict.get_sym(dict.get_lexeme(
					_unquote(lexeme2str(l)))));
				break;
			//case elem::BLTIN: // no longer used, check and remove...
			//	DBG(assert(false););
			//	t.push_back(dict.get_bltin(r.e[n].e)); break;
			case elem::SYM: t.push_back(dict.get_sym(r.e[n].e));
			default: ;
		}
	// stronger 'realrel' condition for tables, only REL and header BLTIN
	ntable tab = realrel ? get_table(get_sig(r)) : -1;
	// D: idbltin name isn't handled above (only args, much like rel-s & tab-s).
	if (extype == term::BLTIN) {
		int_t idbltin = dict.get_bltin(r.e[0].e);
		if (tab > -1) {
			// header BLTIN rel w table, save alongside table (for decomp. etc.)
			tbls[tab].idbltin = idbltin;
			tbls[tab].bltinargs = t; // if needed, for rule/header (all in tbl)
			tbls[tab].bltinsize = nvars; // number of vars (<0)
			//count_if(t.begin(), t.end(), [](int i) { return i < 0; });
		}
		return term(r.neg, tab, t, orderid, idbltin,
			(bool) (r.e[0].num & 1), (bool) (r.e[0].num & 2));
	}
	return term(r.neg, extype, r.arith_op, tab, t, orderid);
	// ints t is elems (VAR, consts) mapped to unique ints/ids for perms.
}


//---------------------------------------------------------

//TODO: we need to put all formula manipulation code in separated
// sources. Dragan already did this in varbits, but in the meantime
// in next commit we should refactor this

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

//---------------------------------------------------------

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

//---------------------------------------------------------

/* Populates froot argument by creating a binary tree from raw formula in rfm.
It is caller's responsibility to manage the memory of froot. If the function,
returns false or the froot is not needed any more, the caller should delete the froot pointer.
For a null input argument rfm, it returns true and makes froot null as well.
	*/
bool tables::from_raw_form(const sprawformtree rfm, form *&froot, bool &is_sol) {

	form::ftype ft = form::NONE;
	bool ret =false;
	form *root = 0;
	int_t arg = 0;

	if(!rfm) return froot=root, true;

	if(rfm->rt) {
		ft = form::ATOM;
		term t = from_raw_term(*rfm->rt);
		arg = dict.get_temp_sym(rfm->rt->e[0].e);
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

void form::printnode(int lv, const tables* tb) {
	if (r) r->printnode(lv+1, tb);
	for (int i = 0; i < lv; i++) COUT << '\t';
	if( tb && this->tm != NULL)
		COUT << " " << type << " " << tb->to_raw_term(*tm) << "\n";
	else
		COUT << " " << type << " " << arg << "\n";
	if (l) l->printnode(lv+1, tb);
}

//---------------------------------------------------------

template <typename T>
void tables::out(basic_ostream<T>& os) const {
	//strs_t::const_iterator it;
	for (ntable tab = 0; (size_t)tab != tbls.size(); ++tab) {
//		if ((it = strs.find(dict.get_rel(tab))) == strs.end())
		if (!tbls[tab].internal) out(os, tbls[tab].t, tab);
//		else os << it->first << " = \"" << it->second << '"' << endl;
	}
}

template void tables::out<char>(ostream& os) const;
template void tables::out<wchar_t>(wostream& os) const;

/* Print out the fixpoint associated with this sequence of databases and
 * return true. Return false if this sequence of databases contains no
 * repeats. */

template <typename T>
bool tables::out_fixpoint(basic_ostream<T>& os) {
	const int_t fronts_size = fronts.size(), tbls_size = tbls.size();
	if(fronts_size < 2 ||
			std::find(fronts.begin(), fronts.end()-1, fronts.back()) ==
			fronts.end()-1) {
		// There cannot be a fixpoint if there are less than two fronts or
		// if there do not exist two equal fronts
		return false;
	} else if (opts.pfp3) {
		// If FO(3-PFP) semantics are in effect
		// Determine which facts are true, false, and undefined
		level trues(tbls_size), falses(tbls_size), undefineds(tbls_size);
		// Loop back to the first repetition of the last front. It is clear
		// that the set of intervening fronts are periodic
		int_t cycle_start;
		for(cycle_start = fronts_size - 2;
			fronts[cycle_start] != fronts.back(); cycle_start--);
		// Make a buffer to hold the sequence of states a single table
		// eventually cycles through
		bdd_handles cycle(fronts_size - 1 - cycle_start);
		// For each table, compute which facts are true, false, and
		// undefined respectively
		for(ntable n = 0; n < (ntable)tbls_size; n++) {
			// Compute the eventual cycle of the current table
			for(int_t i = cycle_start + 1; i < fronts_size; i++) {
				cycle[i - cycle_start - 1] = fronts[i][n];
			}
			// True facts are those for which there exists an I such that
			// for all i>=I, the fact is a member of front i
			trues[n] = bdd_and_many(cycle);
			// False facts are those for which there exists an I such that
			// for all i>=I, the fact is not a member of front i
			falses[n] = htrue % bdd_or_many(cycle);
			// Undefined facts are those which are neither true nor false
			undefineds[n] = htrue % (trues[n] || falses[n]);
		}
		// Print out the true points separately
		os << "true points:" << endl;
		bool exists_trues = false;
		for(ntable n = 0; n < (ntable)tbls_size; n++) {
			decompress(trues[n], n, [&os, &exists_trues, this](const term& r) {
				os << to_raw_term(r) << '.' << endl;
				exists_trues = true; });
		}
		if(!exists_trues) os << "(none)" << std::endl;

		// Finally print out the undefined points separately
		os << endl << "undefined points:" << endl;
		bool exists_undefineds = false;
		for(ntable n = 0; n < (ntable)tbls_size; n++) {
			decompress(undefineds[n], n, [&os, &exists_undefineds, this](const term& r) {
				os << to_raw_term(r) << '.' << endl;
				exists_undefineds = true; });
		}
		if(!exists_undefineds) os << "(none)" << std::endl;
		return true;
	} else if(fronts.back() == fronts[fronts_size - 2]) {
		// If FO(PFP) semantics are in effect and the last two fronts are
		// equal then print them; this is the fixpoint.
		level &l = fronts.back();
		for(ntable n = 0; n < (ntable)tbls_size; n++) {
			if (!tbls[n].internal)
				decompress(l[n], n, [&os, this](const term& r) {
					os << to_raw_term(r) << '.' << endl; });
		}
		return true;
	} else {
		// If FO(PFP) semantics are in effect and two equal fronts are
		// separated by an unequal front; then the fixpoint is empty.
		return true;
	}
}

template bool tables::out_fixpoint<char>(ostream& os);
template bool tables::out_fixpoint<wchar_t>(wostream& os);

void tables::out(const rt_printer& f) const {
	for (ntable tab = 0; (size_t)tab != tbls.size(); ++tab)
		if (!tbls[tab].internal) out(tbls[tab].t, tab, f);
}

template <typename T>
void tables::out(basic_ostream<T>& os, spbdd_handle x, ntable tab) const {
	if (!tbls[tab].internal) // don't print internal tables.
		out(x, tab, [&os](const raw_term& rt) { os<<rt<<'.'<<endl; });
}

#ifdef __EMSCRIPTEN__
// o is `tabular_collector` - JS object with methods:
// - length(relation_name) - returns number of rows (or index of next new row)
// - set(relation_name, row, col, value) - sets value of the cell of a table
void tables::out(emscripten::val o) const {
	out([&o](const raw_term& t) {
		string relation = to_string(lexeme2str(t.e[0].e));
		int row = o.call<int>("length", relation);
		int col = 0;
		for (size_t ar = 0, n = 1; ar != t.arity.size();) {
			ostringstream es;
			while (t.arity[ar] == -1) ++ar, es << '(';
			if (n >= t.e.size()) break;
			while (t.e[n].type == elem::OPENP) ++n;
			for (int_t k = 0; k != t.arity[ar];)
				if ((es<<t.e[n++]),++k!=t.arity[ar]) {
					o.call<void>("set", relation, row,col++,
						es.str());
					es.str("");
				}
			while (n<t.e.size() && t.e[n].type == elem::CLOSEP) ++n;
			++ar;
			while (ar < t.arity.size()
				&& t.arity[ar] == -2) ++ar, es<<')';
			if (es.str() != "")
				o.call<void>("set", relation, row, col++,
					es.str());
		}
	});
}
#endif

void tables::decompress(spbdd_handle x, ntable tab, const cb_decompress& f,
	size_t len, bool allowbltins) const {
	table tbl = tbls.at(tab);
	// D: bltins are special type of REL-s, mostly as any but no decompress.
	if (!allowbltins && tbl.is_builtin()) return;
	if (!len) len = tbl.len;
	allsat_cb(x/*&&ts[tab].t*/, len * bits,
		[tab, &f, len, this](const bools& p, int_t DBG(y)) {
		DBG(assert(abs(y) == 1);)
		term r(false, term::REL, NOP, tab, ints(len, 0), 0);
		for (size_t n = 0; n != len; ++n)
			for (size_t k = 0; k != bits; ++k)
				if (p[pos(k, n, len)])
					r[n] |= 1 << k;
		f(r);
	})();
}

set<term> tables::decompress() {
	set<term> r;
	for (ntable tab = 0; (size_t)tab != tbls.size(); ++tab)
		decompress(tbls[tab].t, tab, [&r](const term& t){r.insert(t);});
	return r;
}

// D: TODO: just a quick & dirty fix, get_elem, to_raw_term (out etc.) is const
#define rdict() ((dict_t&)dict)
//#define get_var_lexeme(v) rdict().get_var_lexeme_from(v)
//#define get_var_lexeme(v) dict.get_lexeme(string("?v") + to_string_(-v))
#define get_var_lexeme(v) rdict().get_lexeme(to_string_t("?v")+to_string_t(-v))

elem tables::get_elem(int_t arg) const {
	if (arg < 0) return elem(elem::VAR, get_var_lexeme(arg));
	if( opts.bitunv == false) {
		if (arg & 1) return elem((char32_t) (arg >> 2));
		if (arg & 2) return elem((int_t) (arg >> 2));
	}
	else if(arg == 1 || arg == 0) return elem((bool)(arg));
	return elem(elem::SYM, rdict().get_sym(arg));
}

raw_term tables::to_raw_term(const term& r) const {
	raw_term rt;
	rt.neg = r.neg;
	size_t args;
	if (r.extype == term::EQ) {//r.iseq)
		args = 2, rt.e.resize(args + 1), rt.e[0] = get_elem(r[0]),
		rt.e[1] = elem(elem::SYM, rdict().get_lexeme(r.neg ? "!=" : "=")),
		rt.e[2] = get_elem(r[1]), rt.arity = {2}, rt.extype = raw_term::EQ;
		return rt;
	} else if (r.extype == term::LEQ) {//r.isleq)
		args = 2, rt.e.resize(args + 1), rt.e[0] = get_elem(r[0]),
		// D: TODO: is this a bug (never used)? for neg it should be > not <= ?
		rt.e[1] = elem(elem::SYM, rdict().get_lexeme(r.neg ? "<=" : ">")),
		rt.e[2] = get_elem(r[1]), rt.arity = {2}, rt.extype = raw_term::LEQ;
		return rt;
	} else if( r.tab == -1 && r.extype == term::ARITH ) {
			rt.e.resize(5);
			elem elp;
			elp.arith_op = r.arith_op;
			elp.type = elem::ARITH;
			switch ( r.arith_op ) {
				case t_arith_op::ADD: elp.e = rdict().get_lexeme("+");break;
				case t_arith_op::MULT: elp.e = rdict().get_lexeme("*");break;
				case t_arith_op::SUB: elp.e = rdict().get_lexeme("-");break;
				default: __throw_runtime_error( "to_raw_term to support other operator ");
			}
			elem elq;
			elq.type = elem::EQ;
			elq.e = rdict().get_lexeme("=");

			rt.e[0] = get_elem(r[0]);
			rt.e[1] = elp;
			rt.e[2] = get_elem(r[1]);
			rt.e[3] = elq;
			rt.e[4] = get_elem(r[2]);
			rt.extype = raw_term::ARITH;
			return rt;
		}
	else if (r.extype == term::BLTIN) {
		args = r.size();
		rt.e.resize(args + 1);
		rt.e[0] = elem(elem::SYM,
			dict.get_bltin(r.idbltin));
		rt.e[0].num = r.renew << 1 | r.forget;
		rt.arity = { (int_t) args };
		for (size_t n = 1; n != args + 1; ++n)
			rt.e[n] = get_elem(r[n - 1]);
		rt.insert_parens(dict.op, dict.cl);
	}
	else {
		args = tbls.at(r.tab).len, rt.e.resize(args + 1);
		rt.e[0] = elem(elem::SYM,
			dict.get_rel(get<0>(tbls.at(r.tab).s)));
		rt.arity = get<ints>(tbls.at(r.tab).s);
		for (size_t n = 1; n != args + 1; ++n)
			rt.e[n] = get_elem(r[n - 1]);
		rt.insert_parens(dict.op, dict.cl);
	}
	DBG(assert(args == r.size());)
	if( opts.bitunv && typenv.contains_pred(lexeme2str(rt.e[0].e) )) {
		const std::vector<typedecl> &vt = typenv.lookup_pred(lexeme2str(rt.e[0].e)) ;
		int_t bitsz = -1; 
		int_t val;
		int_t argc = 0;
		for(typedecl td: vt ) {
			if( td.is_primitive() ) {
				bitsz =  td.pty.get_bitsz();
				val = 0;
				DBG(assert(rt.e.size() > (size_t)bitsz ));
				for( int_t n = 0; n < bitsz; n++)
						val |= rt.e[argc + n + 2].num << (bitsz-1 -n);
				
				rt.e.erase(rt.e.begin()+ 2 + argc, rt.e.begin() + 2 + argc + bitsz);
				elem el;
				if( td.pty.ty == primtype::UINT )
					el = elem(val);
				else if ( td.pty.ty == primtype::UCHAR ) 
					el = elem((char_t) val);
				else if ( td.pty.ty == primtype::SYMB )
					el = elem(elem::SYM, this->dict.get_sym(val) );
					
				rt.e.insert(rt.e.begin() + 2 + argc, el);
				argc++;
			}
			else { } //structtypes userdef
		}
		rt.calc_arity(nullptr);
	}
	else if( opts.bitunv) {
	}
	
	return rt;
}

void tables::out(spbdd_handle x, ntable tab, const rt_printer& f) const {
	decompress(x&&tbls.at(tab).t, tab, [f, this](const term& r) {
		f(to_raw_term(r)); });
}

void term::replace(const map<int_t, int_t>& m) {
	auto it = m.end();
	for (int_t& i : *this) if (m.end() != (it = m.find(i))) i = it->second;
}

void align_vars(vector<term>& v) {
	// D: 'vs'? remove it
	//set<int_t> vs;
	//vs.clear();
	map<int_t, int_t> m;
	for (size_t k = 0; k != v.size(); ++k)
		for (size_t n = 0; n != v[k].size(); ++n)
			if (v[k][n] < 0 && !has(m, v[k][n]))
				m.emplace(v[k][n], -m.size() - 1);
	if (!m.empty()) for (term& t : v) t.replace(m);
}

uints tables::get_perm(const term& t, const varmap& m, size_t len) const {
	uints perm = perm_init(t.size() * bits);
	for (size_t n = 0, b; n != t.size(); ++n)
		if (t[n] < 0)
			for (b = 0; b != bits; ++b)
				perm[pos(b,n,t.size())] = pos(b,m.at(t[n]),len);
	return perm;
}

template<typename T>
varmap tables::get_varmap(const term& h, const T& b, size_t &varslen, bool blt) {
	varmap m;
	varslen = h.size();
	for (size_t n = 0; n != h.size(); ++n)
		if (h[n] < 0 && !has(m, h[n])) m.emplace(h[n], n);
	if (blt) return m;
	for (const term& t : b)
		for (size_t n = 0; n != t.size(); ++n)
			if (t[n] < 0 && !has(m, t[n]))
				m.emplace(t[n], varslen++);
	return m;
}

spbdd_handle tables::get_alt_range(const term& h, const term_set& a,
	const varmap& vm, size_t len) {
	set<int_t> pvars, nvars, eqvars, leqvars, arithvars;
	vector<const term*> eqterms, leqterms, arithterms;
	// first pass, just enlist eq terms (that have at least one var)
	for (const term& t : a) {
		bool haseq = false, hasleq = false;
		for (size_t n = 0; n != t.size(); ++n)
			if (t[n] >= 0) continue;
			else if (t.extype == term::EQ) haseq = true; // .iseq
			else if (t.extype == term::LEQ) hasleq = true; // .isleq
			else (t.neg ? nvars : pvars).insert(t[n]);
		// TODO: BLTINS: add term::BLTIN handling
		// only if iseq and has at least one var
		if (haseq) eqterms.push_back(&t);
		else if (hasleq) leqterms.push_back(&t);
	}
	for (const term* pt : eqterms) {
		const term& t = *pt;
		bool noeqvars = true;
		vector<int_t> tvars;
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

	for (int_t i : pvars) nvars.erase(i);
	if (h.neg) for (int_t i : h) if (i < 0)
		nvars.erase(i), eqvars.erase(i), leqvars.erase(i); // arithvars.erase(i);
	bdd_handles v;
	for (int_t i : nvars) range(vm.at(i), len, v);
	for (int_t i : eqvars) range(vm.at(i), len, v);
	for (int_t i : leqvars) range(vm.at(i), len, v);
	if (!h.neg) {
		set<int_t> hvars;
		for (int_t i : h) if (i < 0) hvars.insert(i);
		for (const term& t : a) for (int_t i : t) hvars.erase(i);
		for (int_t i : hvars) range(vm.at(i), len, v);
	}
	return bdd_and_many(v);
}

map<size_t, int_t> varmap_inv(const varmap& vm) {
	map<size_t, int_t> inv;
	for (auto x : vm) {
		assert(!has(inv, x.second));
		inv.emplace(x.second, x.first);
	}
	return inv;
}

body tables::get_body(const term& t, const varmap& vm, size_t len) const {
	body b;
	b.neg = t.neg, b.tab = t.tab, b.perm = get_perm(t, vm, len),
	b.q = htrue, b.ex = bools(t.size() * bits, false);
	varmap m;
	auto it = m.end();
	for (size_t n = 0; n != t.size(); ++n)
		if (t[n] >= 0)
			b.q = b.q && from_sym(n, t.size(), t[n]),
			get_var_ex(n, t.size(), b.ex);
		else if (m.end() == (it = m.find(t[n]))) m.emplace(t[n], n);
		else	b.q = b.q && from_sym_eq(n, it->second, t.size()),
			get_var_ex(n, t.size(), b.ex);
	return b;
}

bool tables::get_facts(const flat_prog& m) {
	map<ntable, set<spbdd_handle>> add, del;
	for (const auto& r : m)
		if (r.size() != 1) continue;
		else if (r[0].goal) goals.insert(r[0]);
		else if (r[0].is_builtin()) fact_builtin(r[0]);
		else (r[0].neg ? del : add)[r[0].tab].insert(from_fact(r[0]));
	if (unsat || halt) return false;
	clock_t start{}, end;
	if (opts.optimize) measure_time_start();
	bdd_handles v;
	for (auto x : add) for (auto y : x.second)
		tbls[x.first].t = tbls[x.first].t || y;
	for (auto x : del) {
		for (auto y : x.second) tbls[x.first].t = tbls[x.first].t % y;
	}
	if (opts.optimize)
		(o::ms() << "# get_facts: "),
		measure_time_end();
	return true;
}

void tables::get_nums(const raw_term& t) {
	for (const elem& e : t.e)
		if (e.type == elem::NUM) nums = max(nums, e.num);
		else if (e.type == elem::CHR) chars = max(chars, (int_t)e.ch);
}

bool tables::to_pnf(form *&froot) {

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

flat_prog tables::to_terms(const raw_prog& p) {
	flat_prog m;
	vector<term> v;
	term t;

	for (const raw_rule& r : p.r)
		if (r.type == raw_rule::NONE && !r.b.empty()) {
			for (const raw_term& x : r.h) {
				get_nums(x), t = from_raw_term(x, true),
				v.push_back(t);
				for (const vector<raw_term>& y : r.b) {
					int i = 0;
					for (const raw_term& z : y) // term_set(
						v.push_back(from_raw_term(z, false, i++)),
						get_nums(z);
					align_vars(v);
					if (!m.insert(move(v)).second) v.clear();
				}
			}
		}
		else if(r.prft != NULL) {
			bool is_sol = false;
			form* froot = 0;
			sprawformtree root = r.prft->neg // neg transform
				? std::make_shared<raw_form_tree>(elem::NOT, r.prft)
				: r.prft;
			if (r.prft->guard_lx != lexeme{ 0, 0 }) { // guard transform
				raw_term gt;
				gt.arity = { 0 };
				gt.e.emplace_back(elem::SYM, r.prft->guard_lx);
				root = std::make_shared<raw_form_tree>(elem::AND, root,
					std::make_shared<raw_form_tree>(gt));
			}
			from_raw_form(root, froot, is_sol);

			/*
			DBG(COUT << "\n ........... \n";)
			DBG(r.prft.get()->printTree();)
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

			for (const raw_term& x : r.h) {
				get_nums(x), t = from_raw_term(x, true),
				v.push_back(t);
				t = term(extype, qbf);
				v.push_back(t);
				m.insert(move(v));
			}
		} else  {
			for (const raw_term& x : r.h)
				t = from_raw_term(x, true),
				t.goal = r.type == raw_rule::GOAL,
				m.insert({t}), get_nums(x);
		}

	return m;
}

int_t tables::freeze(vector<term>& v, int_t m = 0) {
	map<int_t, int_t> p;
	map<int_t, int_t>::const_iterator it;
	for (const term& t : v) for (int_t i : t) 
		if (opts.bitunv && (i ==0 || i == 1 )) m = max(m, i);
		else if (i & 2) m = max(m, i >> 2);
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

flat_prog& tables::get_canonical_db(vector<term>& x, flat_prog& p) {
	freeze(x);
	for (size_t n = 1; n != x.size(); ++n) p.insert({x[n]});
	return p;
}

flat_prog& tables::get_canonical_db(vector<vector<term>>& x, flat_prog& p) {
	int_t m = 0;
	for (vector<term>& v : x)
		for (const term& t : v)
			for (int_t i : t)
				if (opts.bitunv && (i == 1 || i == 0) ) m = max(m, i);
				else if (i & 2) m = max(m, i >> 2);
	for (vector<term>& t : x) {
		freeze(t, m);
		for (size_t n = 1; n != t.size(); ++n) p.insert({t[n]});
	}
	return p;
}

void tables::run_internal_prog(flat_prog p, set<term>& r, size_t nsteps) {
	dict_t tmpdict(dict); // copy ctor, only here, if this's needed at all?
	tables::options to;
	to.bin_transform = true;
	tables t(move(tmpdict), to);
	//t.dict = dict;
	t.bcqc = false, t.chars = chars, t.nums = nums;
	if (!t.run_nums(move(p), r, nsteps)) { DBGFAIL; }
}

void getvars(const term& t, set<int_t>& v) {
	for (int_t i : t) if (i < 0) v.insert(i);
}

void getvars(const vector<term>& t, set<int_t>& v) {
	for (const term& x : t) getvars(x, v);
}

void create_head(vector<term>&, ntable) {
/*	set<int_t> v;
	getvars(x, v);
	term h;
	h.tab = tab, h.insert(h.begin(), vx.begin(), vx.end());
	x.insert(x.begin(), move(h));*/
}

ntable tables::create_tmp_rel(size_t len) {
	ntable tab = get_new_tab(dict.get_rel(get_new_rel()), {(int_t)len});
	return tmprels.insert(tab), tab;
}

void tables::create_tmp_head(vector<term>& x) {
	set<int_t> v;
	getvars(x, v);
	create_head(x, create_tmp_rel(v.size()));
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
//		return print(print(o::out(),x)<<" is a generalization of ",yy),
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
		print(print(o::err()<<"Rule\t\t", v)<<endl<<"minimized into\t"
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

template <typename T>
basic_ostream<T>& tables::print(basic_ostream<T>& os, const vector<term>& v) const {
	os << to_raw_term(v[0]);
	if (v.size() == 1) return os << '.';
	os << " :- ";
	for (size_t n = 1; n != v.size(); ++n) {
		if (v[n].goal) os << '!';
		os << to_raw_term(v[n]) << (n == v.size() - 1 ? "." : ", ");
	}
	return os;
}

template <typename T>
basic_ostream<T>& tables::print(basic_ostream<T>& os, const flat_prog& p) const{
	for (const auto& x : p)
		print(os << (x[0].tab == -1 ? 0 : tbls[x[0].tab].priority) <<
			'\t', x) << endl;
/*	map<size_t, flat_prog> m;
	for (const auto& x : p) m[tbls[x[0].tab].priority].insert(x);
	size_t n = m.rbegin()->first;
	vector<flat_prog> v(n);
	for (const auto& x : m) v[n--] = move(x.second);
	for (n = 0; n != v.size(); ++n)
		for (const vector<term>& y : v[n])
			print(os << n << '\t', y) << endl;*/
	return os;
}

template <typename T>
basic_ostream<T>& tables::print_dict(basic_ostream<T>& os) const {
	return os << dict;
}
template basic_ostream<char>& tables::print_dict(basic_ostream<char>&) const;
template basic_ostream<wchar_t>& tables::print_dict(basic_ostream<wchar_t>&) const;

bool tables::handler_eq(const term& t, const varmap& vm, const size_t vl,
		spbdd_handle &c) const {
	DBG(assert(t.size() == 2););
	spbdd_handle q = bdd_handle::T;
	if (t[0] == t[1]) return !(t.neg);
	if (t[0] >= 0 && t[1] >= 0) return !(t.neg == (t[0] == t[1]));
	if (t[0] < 0 && t[1] < 0)
		q = from_sym_eq(vm.at(t[0]), vm.at(t[1]), vl);
	else if (t[0] < 0)
		q = from_sym(vm.at(t[0]), vl, t[1]);
	else if (t[1] < 0)
		q = from_sym(vm.at(t[1]), vl, t[0]);
	c = t.neg ? c % q : (c && q);
	return true;
}

bool tables::handler_leq(const term& t, const varmap& vm, const size_t vl,
		spbdd_handle &c) const {
	DBG(assert(t.size() == 2););
	spbdd_handle q = bdd_handle::T;
	if (t[0] == t[1]) return !(t.neg);
	if (t[0] >= 0 && t[1] >= 0) return !(t.neg == (t[0] <= t[1]));
	if (t[0] < 0 && t[1] < 0)
		q = leq_var(vm.at(t[0]), vm.at(t[1]), vl, bits);
	else if (t[0] < 0)
		q = leq_const(t[1], vm.at(t[0]), vl, bits);
	else if (t[1] < 0)
		// 1 <= v1, v1 >= 1, ~(v1 <= 1) || v1==1.
		q = htrue % leq_const(t[0], vm.at(t[1]), vl, bits) ||
			from_sym(vm.at(t[1]), vl ,t[0]);
	c = t.neg ? c % q : (c && q);
	return true;
}

void tables::get_alt(const term_set& al, const term& h, set<alt>& as, bool blt){
	alt a;
	set<pair<body, term>> b;
	spbdd_handle leq = htrue, q;
	a.vm = get_varmap(h, al, a.varslen, blt), a.inv = varmap_inv(a.vm);

	for (const term& t : al) {
		if (t.extype == term::REL) {
			b.insert({ get_body(t, a.vm, a.varslen), t });
		} else if (t.extype == term::EQ) {
			if (!handler_eq(t, a.vm, a.varslen, a.eq)) return;
		} else if (t.extype == term::LEQ) {
			if (!handler_leq(t, a.vm, a.varslen, leq)) return;
		} else if (t.extype == term::ARITH) {
			//arith constraint on leq
			if (!handler_arith(t,a.vm, a.varslen, leq)) return;
		} else if (!blt && t.extype == term::BLTIN) {
			bltins.at(t.idbltin).body.getvars(t,
				a.bltinvars, a.bltngvars, a.bltoutvars);
			a.bltins.push_back(t);
		}
	}
	if (a.bltinvars.size()) { // get grnd
		ints args;
		for (auto v : a.bltinvars) args.push_back(v);
		const term bt(false, -1, args, 0, -1);
		set<alt> as;
		get_alt(al, bt, as, true);
		assert(as.size() == 1);
		for (alt x : as) *(a.grnd = new alt) = x;
		// TODO grnd alt sharing?
		//set<alt*, ptrcmp<alt>>::const_iterator ait;
		//	if ((ait = grnds.find(&x)) != grnds.end())
		//		a.grnd = *ait;
		//	else	*(a.grnd = new alt) = x,
		//		grnds.insert(a.grnd);
	}
	a.rng = bdd_and_many({ get_alt_range(h, al, a.vm, a.varslen), leq });
	static set<body*, ptrcmp<body>>::const_iterator bit;
	body* y;
	for (auto x : b) {
		a.t.push_back(x.second);
		if ((bit=bodies.find(&x.first)) != bodies.end())
			a.push_back(*bit);
		else *(y=new body) = x.first, a.push_back(y), bodies.insert(y);
		// collect bodies for builtins. these arn't grounded
		if (y) for (size_t n = 0; n != x.second.size(); ++n)
			if (x.second[n] < 0 && has(a.bltngvars, x.second[n]))
				a.varbodies.insert({ x.second[n], a.back() });
	}
	auto d = deltail(a.varslen, h.size());
	a.ex = d.first, a.perm = d.second, as.insert(a);
}

lexeme tables::get_new_rel() {
	static size_t last = 1;
	string s = "r";
	size_t sz;
	lexeme l;
retry:	sz = dict.nrels(), l = dict.get_lexeme(s + to_string_(last));
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

vector<term> tables::interpolate(vector<term> x, set<int_t> v) {
	term t;
	for (size_t k = 0; k != x.size(); ++k)
		for (size_t n = 0; n != x[k].size(); ++n)
			if (has(v, x[k][n]))
				t.push_back(x[k][n]), v.erase(x[k][n]);
	return t.tab = create_tmp_rel(t.size()), x.insert(x.begin(), t), x;
}

set<int_t> intersect(const set<int_t>& x, const set<int_t>& y) {
	set<int_t> r;
	set_intersection(x.begin(), x.end(), y.begin(), y.end(),
		inserter(r, r.begin()));
	return r;
}

void tables::transform_bin(flat_prog& p) {
	const flat_prog q = move(p);
	vector<set<int_t>> vars;
	auto getterms = [&vars]
		(const vector<term>& x) -> vector<size_t> {
		if (x.size() <= 3) return {};
		/* XXX: OK to remove?
		vector<size_t> e;
		for (size_t n = 1; n != x.size(); ++n)
			if (has(exts, x[n].tab)) e.push_back(n);
		if (e.size() == x.size() - 1) return { 1, 2 };
		if (e.size() > 1) return { e[0], e[1] }; */
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
	set<int_t> v;
	for (vector<term> x : q) {
		if (x[0].goal) { goals.insert(x[0]); continue; }
			//prog_add_rule(p, x); continue; }
		for (const term& t : x) getvars(t, v), vars.push_back(move(v));
		while (!(m = getterms(x)).empty()) {
			for (size_t i : m) r.push_back(x[i]);
			for (size_t n = m.size(); n--;)
				x.erase(x.begin() + m[n]),
				vars.erase(vars.begin() + m[n]);
			for (const auto& s : vars) v.insert(s.begin(), s.end());
			r = interpolate(r, move(v)),
			x.push_back(r[0]), getvars(r[0], v),
			vars.push_back(move(v)), p.insert(move(r));
		}
		p.insert(move(x)), vars.clear();
	}
	if (opts.print_transformed) print(o::to("transformed")
		<< "# after transform_bin:" << endl, p);
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

void tables::get_form(const term_set& al, const term& h, set<alt>& as) {
	auto t = al.begin();
	DBG(assert(t->extype == term::FORM1 || t->extype == term::FORM2));
	alt a;
	a.f.reset(new(pnft));

	const term_set anull;
	size_t varsh;
	varmap vm = get_varmap(h, al, varsh), vmh;
	varsh = vm.size();
	a.f->vm = vm;
	if (t->extype == term::FORM1)
		handler_form1(a.f, t->qbf.get(), vm, vmh, true);
	else
		handler_formh(a.f, t->qbf.get(), vm, vmh);

	 if (varsh > 0 && a.f->ex_h.size() == 0) {
		 a.f->varslen = vm.size();
		 a.f->varslen_h = varsh;
		 auto d = deltail(a.f->varslen, h.size(), bits-2);
		 a.f->ex_h = d.first, a.f->perm_h = d.second;
		 term t; t.resize(a.f->varslen);
		 for (auto &v : vm) t[v.second] = v.first;
		 a.f->perm = get_perm(t, a.f->vm, a.f->varslen, bits-2);
	}

	as.insert(a);
	return;
}

bool tables::get_rules(flat_prog p) {
	bcqc = false;
	if (!get_facts(p)) return false;
	/*
	//XXX: OK to remove?
	for (const vector<term>& x : p)
		for (size_t n = 1; n != x.size(); ++n)
			exts.insert(x[n].tab);
	for (const vector<term>& x : p) if (x.size() > 1) exts.erase(x[0].tab);*/
	if (bcqc) print(o::out()<<"before cqc, "<<p.size()<<" rules:"<<endl,p);
	flat_prog q(move(p));
	map<ntable, ntable> r;
	for (const auto& x : q) prog_add_rule(p, r, x);
	replace_rel(move(r), p);
	if (bcqc) print(o::out()<<"after cqc before tbin, "
		<<p.size()<<" rules."<<endl, p);
	if (opts.bin_transform) transform_bin(p);
	if (bcqc) print(o::out()<<"before cqc after tbin, "
		<<p.size()<< " rules."<<endl, p);
	q = move(p);
	for (const auto& x : q) prog_add_rule(p, r, x);
	replace_rel(move(r), p), set_priorities(p);
	if (bcqc) print(o::out()<<"after cqc, "
		<<p.size()<< " rules."<<endl, p);
	if (opts.optimize) bdd::gc();

	// BLTINS: set order is important (and wrong) for e.g. REL, BLTIN, EQ
	map<term, set<term_set>> m;
	for (const auto& x : p)
		if (x.size() == 1) m[x[0]] = {};
		else m[x[0]].insert(term_set(x.begin() + 1, x.end()));
	set<rule> rs;
	varmap::const_iterator it;
	set<alt*, ptrcmp<alt>>::const_iterator ait;
	alt* aa;
	for (auto x : m) {
		if (x.second.empty()) continue;
		set<int_t> hvars;
		const term &t = x.first;
		rule r;
		if (t.neg) datalog = false;
		//tbls[t.tab].ext = false;
		varmap v;
		r.neg = t.neg, r.tab = t.tab, r.eq = htrue, r.t = t; //XXX: review why we replicate t variables in r
		for (size_t n = 0; n != t.size(); ++n)
			if (t[n] >= 0) get_sym(t[n], n, t.size(), r.eq);
			else if (v.end()==(it=v.find(t[n]))) v.emplace(t[n], n);
			else r.eq = r.eq&&from_sym_eq(n, it->second, t.size());
		set<alt> as;
		r.len = t.size();

		for (const term_set& al : x.second)
			if (al.begin()->extype == term::FORM1 ||
					al.begin()->extype == term::FORM2)
				get_form(al, t, as);
			else
				get_alt(al, t, as);

		for (alt x : as)
			if ((ait = alts.find(&x)) != alts.end())
				r.push_back(*ait);
			else	*(aa = new alt) = x,
				r.push_back(aa), alts.insert(aa);

		rs.insert(r);
	}
	for (rule r : rs)
		tbls[r.t.tab].r.push_back(rules.size()), rules.push_back(r);
	sort(rules.begin(), rules.end(), [this](const rule& x, const rule& y) {
			return tbls[x.tab].priority > tbls[y.tab].priority; });
	return true;
}

struct unary_string{
	//IMPROVE: use array [ pos] = rel or unorderedmap instead
	unordered_map< char32_t, set<int_t> > rel;
	size_t pbsz;
	uint64_t vmask;
	vector<char32_t> sort_rel;

	unary_string(size_t _pbsz): pbsz(_pbsz) {
		DBG(assert(sizeof(char32_t)*8 >= pbsz);)
		DBG(assert(pbsz  && !(pbsz & (pbsz-1)));) // power of 2 only, 1 2 4 8 16...
		vmask = ((uint64_t(1)<<(pbsz)) -1);
	}
	bool buildfrom(string_t s) { return buildfrom(to_u32string(s)); }
	bool buildfrom(u32string s) {
		if(!s.size()) return false;

		size_t n = (sizeof(s[0])<<3)/pbsz;
		sort_rel.resize(s.size()*n);

		for (size_t i=0; i < s.size(); i++) {
			for (size_t a=0; a < n; a++) {
				rel[ char32_t(vmask & s[i]) ].insert(i*n+a),
				sort_rel[i*n+a] = char32_t(vmask & s[i]),
				s[i] = uint64_t(s[i]) >> pbsz;
			}
		}
		return true;
	}
	string_t getrelin_str(char32_t r) {
		return (r == '\0') ? to_string_t("00"): to_string_t(r);

	}
	ostream_t& toprint(ostream_t& o) {
		for(size_t i = 0; i < sort_rel.size(); i++)
			if(isalnum(sort_rel[i]))
				o << to_string(to_string_t(sort_rel[i]))
					<< " " << i << endl;
			else o <<uint_t(sort_rel[i])<<"  "<< i <<endl;
		return o;
	}
};
void tables::load_string(lexeme r, const string_t& s) {

	unary_string us(sizeof(char32_t)*8);
	us.buildfrom(s);
	//DBG(us.toprint(o::dbg()));
	for( auto it: us.rel ){
		int_t r = dict.get_rel(rdict().get_lexeme(us.getrelin_str(it.first)));
		term t; t.resize(1);
		ntable tb = get_table({r, {1} });
		t.tab =tb;
		bdd_handles b;
		b.reserve(it.second.size());
		for( int_t i :it.second)
			t[0]= mknum(i), b.push_back(from_fact(t));
		tbls[tb].t = bdd_or_many(b);
	}

	int_t rel = dict.get_rel(r);
	str_rels.insert(rel);

//	const ints ar = {0,-1,-1,1,-2,-2,-1,1,-2,-1,-1,1,-2,-2};
	const int_t sspace = dict.get_sym(dict.get_lexeme("space")),
		salpha = dict.get_sym(dict.get_lexeme("alpha")),
		salnum = dict.get_sym(dict.get_lexeme("alnum")),
		sdigit = dict.get_sym(dict.get_lexeme("digit")),
		sprint = dict.get_sym(dict.get_lexeme("printable"));
	term t,tb;
	bdd_handles b1, b2;
	b1.reserve(s.size()), b2.reserve(s.size()), t.resize(2), tb.resize(3);
	for (int_t n = 0; n != (int_t)s.size(); ++n) {
		t[0] = mknum(n), t[1] = mkchr(s[n]), // t[2] = mknum(n + 1),
		chars = max(chars, t[1]),
		b1.push_back(from_fact(t));
		tb[1] = t[0], tb[2] = mknum(0);
		if (isspace(s[n])) tb[0] = sspace, b2.push_back(from_fact(tb));
		if (isdigit(s[n])) tb[0] = sdigit, b2.push_back(from_fact(tb));
		if (isalpha(s[n])) tb[0] = salpha, b2.push_back(from_fact(tb));
		if (isalnum(s[n])) tb[0] = salnum, b2.push_back(from_fact(tb));
		if (isprint(s[n])) tb[0] = sprint, b2.push_back(from_fact(tb));
	}
	clock_t start{}, end;
	if (opts.optimize)
		(o::ms()<<"# load_string or_many: "),
		measure_time_start();
	ntable st = get_table({rel, {2}}); // str(pos char)
	ntable stb = get_table({rel, {3}}); // str(printable pos 0)

	tbls[st].t = bdd_or_many(move(b1));
	tbls[stb].t = bdd_or_many(move(b2));
	if (opts.optimize) measure_time_end();
}

/*template<typename T> bool subset(const set<T>& small, const set<T>& big) {
	for (const T& t : small) if (!has(big, t)) return false;
	return true;
}*/

void tables::get_var_ex(size_t arg, size_t args, bools& b) const {
	for (size_t k = 0; k != bits; ++k) b[pos(k, arg, args)] = true;
}

void tables::get_sym(int_t sym, size_t arg, size_t args, spbdd_handle& r) const{
	for (size_t k = 0; k != bits; ++k) r = r && from_bit(k, arg, args, sym);
}

ntable tables::get_table(const sig& s) {
	auto it = smap.find(s);
	if (it != smap.end()) return it->second;
	ntable nt = tbls.size();
	size_t len = sig_len(s);
	max_args = max(max_args, len);
	table tb;
	return	tb.t = hfalse, tb.s = s, tb.len = len,
		tbls.push_back(tb), smap.emplace(s,nt), nt;
}

term tables::to_nums(term t) {
	for (int_t& i : t)  if (i > 0) i = mknum(i);
	return t;
}

//term from_nums(term t) {
//	for (int_t& i : t)  if (i > 0) i >>= 2;
//	return t;
//}

vector<term> tables::to_nums(const vector<term>& v) {
	vector<term> r;
	for (const term& t : v) r.push_back(to_nums(t));
	return r;
}

//set<term> from_nums(const set<term>& s) {
//	set<term> ss;
//	for (const term& t : s) ss.insert(from_nums(t));
//	return ss;
//}

void tables::to_nums(flat_prog& m) {
	flat_prog mm;
	for (auto x : m) mm.insert(to_nums(x));
	m = move(mm);
}

ntable tables::get_new_tab(int_t x, ints ar) { return get_table({ x, ar }); }

bool tables::get_substr_equality(const raw_term &rt, size_t &n,
	std::map<size_t,term> &refs, std::vector<term> &v, std::set<term> &/*done*/)
{
	//format : substr(1) = substr(2)
	term svalt;
	svalt.resize(4);
	int_t relp = dict.get_rel(dict.get_lexeme("equals"));
	svalt.tab = get_table({relp, {(int_t)svalt.size()}});
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

int_t tables::get_factor(raw_term &rt, size_t &n, std::map<size_t, term> &refs,
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

bool tables::get_rule_substr_equality(vector<vector<term>> &eqr ){

	if (str_rels.size() > 1) er(err_one_input);
	if (str_rels.empty()) return false;
	eqr.resize(3); // three rules for substr equality
	for(size_t r = 0; r < eqr.size(); r++) {
		int_t var = 0;
		int_t i= --var, j= --var , k=--var, n= --var;
		ntable nt = get_table({dict.get_rel(dict.get_lexeme("equals")), {4}});
		// making head   equals( i j k n) :-
		eqr[r].emplace_back(false, term::textype::REL, t_arith_op::NOP, nt,
								std::initializer_list<int>{i, j, k, n}, 0 );
		// making fact equals( i i k k).
		if( r == 0 ) eqr[r].back().assign({i,i,k,k});
		else if( r == 1 ) { // inductive case
			// equals(i j k n ) ;- str(i cv), str(k cv), i + 1 = j, k +1 = n.
			int_t cv = --var;
			// str(i cv) ,str( k, cv)
			for( int vi=0; vi<2; vi++)
				eqr[r].emplace_back(false, term::textype::REL, t_arith_op::NOP,
									get_table({*str_rels.begin(),{2}}),
									std::initializer_list<int>{eqr[r][0][2*vi], cv} , 0);

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

bool ptransformer::synth_recur( vector<elem>::const_iterator from,
		vector<elem>::const_iterator till, bool bnull = true, bool brecur =true,
		bool balt= true ){

	if(brecur ) {
		bool binsidealt =false; // for | to be present inside
		for( vector<elem>::const_iterator f = from; f!=till; f++)
			if(f->type == elem::ALT) {binsidealt =true; break;}
		if(binsidealt) {
			synth_recur( from, till, false, false, false);
			from = lp.back().p.begin();
			till = lp.back().p.begin()+1;
		}
	}
	lp.emplace_back();
	production &np = lp.back();
	elem sym = elem(elem::SYM,  get_fresh_nonterminal());
	np.p.push_back( sym);
	np.p.insert(np.p.end(), from , till);
	if(brecur) np.p.push_back( sym);
	elem alte = elem(elem::ALT, d.get_lexeme( "|" ) );
	if(balt) np.p.emplace_back(alte);
	if( balt && bnull )	np.p.emplace_back( elem::SYM, d.get_lexeme("null"));
	else if(balt) np.p.insert(np.p.end(), from, till);
	return true;
}

bool ptransformer::parse_factor( vector<elem> &next, size_t& cur){
	size_t cur1 = cur;
	if(cur >= next.size()) return false;
	if( next[cur].type ==  elem::SYM ||
		next[cur].type ==  elem::STR ||
		next[cur].type ==  elem::CHR ) {
		size_t start = cur;
		++cur;
		if( next.size() > cur 				&&
			next[cur].type == elem::ARITH 	&&
			(next[cur].arith_op == MULT 	||
				next[cur].arith_op == ADD		)) {

			//lp.emplace_back(),
			synth_recur( next.begin()+start, next.begin()+cur,
			next[cur].arith_op == MULT),
			++cur;
			next.erase( next.begin()+start, next.begin()+cur);
			next.insert( next.begin()+start, lp.back().p[0]);
			return cur = start+1, true;
		}
		return true;
	}
	if( next[cur].type == elem::OPENSB ) {
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
	//DBG(COUT<<endl<<p<<endl);
	bool ret = this->parse_alts( this->p.p, cur);
	if( this->p.p.size() > cur ) ret = false;

	//DBG(COUT<<p<<endl);
	for ( production t : lp )
		DBG(COUT<<t<<endl);
	if(!ret) parse_error("Error Production",
		cur < this->p.p.size() ? p.p[cur].e : p.p[0].e );
	return ret;

}

bool tables::transform_ebnf(vector<production> &g, dict_t &d, bool &changed){
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
bool tables::transform_grammar_constraints(const production &x, vector<term> &v,
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


bool tables::transform_grammar(vector<production> g, flat_prog& p, form*& /*r*/ ) {
	if (g.empty()) return true;
//	o::out()<<"grammar before:"<<endl;
//	for (production& p : g) o::out() << p << endl;
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
	if (strs.size() && enable_regdetect_matching) {
		string inputstr = to_string(strs.begin()->second);
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
							t.tab = get_table({dict.get_rel(elem.e),{2}});
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
					t.tab = get_table({dict.get_rel(elem.e),{2}});
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
	static const set<string> b =
		{ "alpha", "alnum", "digit", "space", "printable" };
	set<lexeme, lexcmp> builtins;
	for (const string& s : b) builtins.insert(dict.get_lexeme(s));

	for (const production& x : g) {

		if (x.p.size() == 2 && x.p[1].e == "null") {
			term t;
			t.resize(2);
			t[0] = t[1] = -1;
			t.tab = get_table({dict.get_rel(x.p[0].e),{2}});
			vector<term> v{t};
			p.insert(v);
			vector<term> af{t, t};
			af[0].neg = true;
			align_vars(af);
			prog_after_fp.insert(move(af));
			continue;
		}

		// ref: maps ith sybmol production to resp. terms
		std::map<size_t, term> refs;
		DBG(o::dbg()<<x;)
		for (int_t n = 0; n != (int_t)x.p.size(); ++n) {
			term t;
			if (builtins.find(x.p[n].e) != builtins.end()) {
				t.tab = get_table({*str_rels.begin(), {3}});
				t.resize(3), t[0] = dict.get_sym(x.p[n].e),
				t[1] = -n, t[2] = mknum(0);

				term plus1;
				plus1.tab = -1;
				plus1.resize(3);
				plus1.extype = term::textype::ARITH;
				plus1.arith_op = t_arith_op::ADD;
				plus1[0]= -n, plus1[1]=mknum(1), plus1[2]=-n-1;
				v.push_back(move(plus1));

			} else if (x.p[n].type == elem::SYM) {
				t.resize(2);
				t.tab = get_table({dict.get_rel(x.p[n].e),{2}});
				if (n) t[0] = -n, t[1] = -n-1;
				else t[0] = -1, t[1] = -(int_t)(x.p.size());
			} else if (x.p[n].type == elem::CHR) {
				unary_string us(sizeof(char32_t)*8);
				us.buildfrom(u32string(1, x.p[n].ch));
				int_t tv=n;
				//DBG(us.toprint(o::dbg()));
				for( auto rl: us.sort_rel) {
					int_t r = dict.get_rel(rdict().get_lexeme(us.getrelin_str(rl)));
					term t; t.resize(1);
					t.tab= get_table({r, {1}});
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
			dict.get_var_lexeme_from(i);

		transform_grammar_constraints(x, v, p, refs);

		//#define GRAMMAR_FOL
		#ifdef GRAMMAR_FOL
		form *root = NULL;
		int_t minc= 0; // to get the minimum var index;
		for(size_t n=1; n < v.size(); n++) {
			form *cur = new form(form::ATOM, 0, &v[n]);
			if(root) root = new form(form::AND, 0 , NULL, root, cur );
			else root = cur;
			for(int var : v[n])
				minc = min(var, minc);
		}

		// adding quantifier since var indexes are added incrementally
		for(int_t j = -1; j >= minc; j--) {
			// ignore adding exist for vars for lhs first symbol of production
			if( v[0][0] == j || v[0][1] == j ) continue;
			root = new form(form::EXISTS1, 0,  0, new form(form::ATOM, j), root);
		}
		v.erase(v.begin()+1, v.end());
		spform_handle qbf(root);
		v.emplace_back(term::FORM1, qbf);
		DBG(COUT<<endl; root->printnode(0, this);)
		#endif
		p.insert(move(v));
	}
	if (opts.print_transformed) print(print(o::to("transformed")
		<< "# after transform_grammar:\n", p)
		<< "\n# run after a fixed point:\n", prog_after_fp)
		<< endl;
	return true;
}

bool tables::add_prog(const raw_prog& p, const strs_t& strs_) {
	strs = strs_;
	if (!strs.empty()) {
		//chars = 255,
		dict.get_sym(dict.get_lexeme("space")),
		dict.get_sym(dict.get_lexeme("alpha")),
		dict.get_sym(dict.get_lexeme("alnum")),
		dict.get_sym(dict.get_lexeme("digit")),
		dict.get_sym(dict.get_lexeme("printable"));
		for (auto x : strs) {
			nums = max(nums, (int_t)x.second.size()+1);
			unary_string us(32);
			us.buildfrom(x.second);
			chars = max(chars, (int_t)us.rel.size());
		}
	}

	return add_prog(to_terms(p), p.g);
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
//	DBG(print(o::out()<<"run_nums for:"<<endl, p)<<endl<<"returned:"<<endl;)
	if (!add_prog(move(p), {})) return false;
	if (!pfp(nsteps)) return false;
	r = g(decompress());
	return true;
}

void tables::add_tml_update(const term& t, bool neg) {
	// TODO: decompose nstep if too big for the current universe
	nums = max(nums, (int_t)nstep);
	ints arity = tbls.at(t.tab).s.second;
	arity[0] += 3;
	ntable tab = get_table({ rel_tml_update, arity });
	ints args = { mknum(nstep), (neg ? sym_del : sym_add),
		dict.get_sym(dict.get_rel(tbls[t.tab].s.first)) };
	args.insert(args.end(), t.begin(), t.end());
	tbls[tab].add.push_back(from_fact(term(false, tab, args, 0, -1)));
}

template <typename T>
basic_ostream<T>& tables::decompress_update(basic_ostream<T>& os,
	spbdd_handle& x, const rule& r)
{
	if (print_updates) print(os << "# ", r) << "\n# \t-> ";
	decompress(x, r.tab, [&os, &r, this](const term& x) {
		if (print_updates)
			os << (r.neg ? "~" : "") << to_raw_term(x) << ". ";
		if (populate_tml_update) add_tml_update(x, r.neg);
	});
	if (print_updates) os << endl;
	return os;
}

void tables::init_tml_update() {
	rel_tml_update = dict.get_rel(dict.get_lexeme("tml_update"));
	sym_add = dict.get_sym(dict.get_lexeme("add"));
	sym_del = dict.get_sym(dict.get_lexeme("delete"));
}

bool tables::add_prog(flat_prog m, const vector<production>& g, bool mknums) {
	error = false;
	smemo.clear(), ememo.clear(), leqmemo.clear();
	if (mknums) to_nums(m);
	if (populate_tml_update) init_tml_update();
	rules.clear(), datalog = true;
	syms = dict.nsyms();
	while (max(max(nums, chars), syms) >= (1 << (bits - 2))) add_bit();
	for (auto x : strs) load_string(x.first, x.second);
	form *froot;
	if (!transform_grammar(g, m, froot)) return false;
	if (!get_rules(move(m))) return false;
	// filter for rels starting and ending with __
	auto filter_internal_tables = [] (const lexeme& l) {
		size_t len = l[1] - l[0];
		return len > 4 && '_' == l[0][0]     && '_' == l[0][1] &&
				  '_' == l[0][len-2] && '_' == l[0][len-1];
	};
	ints internal_rels = dict.get_rels(filter_internal_tables);
	for (auto& tbl : tbls)
		for (int_t rel : internal_rels)
			if (rel == tbl.s.first) { tbl.internal = true; break; }
//	clock_t start, end;
//	o::dbg()<<"load_string: ";
//	measure_time_start();
//	measure_time_end();
	if (opts.optimize) bdd::gc();
	return true;
}

pair<bools, uints> tables::deltail(size_t len1, size_t len2) const {
	bools ex(len1 * bits, false);
	uints perm = perm_init(len1 * bits);
	for (size_t n = 0; n != len1; ++n)
		for (size_t k = 0; k != bits; ++k)
			if (n >= len2) ex[pos(k, n, len1)] = true;
			else perm[pos(k, n, len1)] = pos(k, n, len2);
	return { ex, perm };
}

uints tables::addtail(size_t len1, size_t len2) const {
	uints perm = perm_init(len1 * bits);
	for (size_t n = 0; n != len1; ++n)
		for (size_t k = 0; k != bits; ++k)
			perm[pos(k, n, len1)] = pos(k, n, len2);
	return perm;
}

spbdd_handle tables::addtail(cr_spbdd_handle x, size_t len1, size_t len2) const{
	if (len1 == len2) return x;
	return x ^ addtail(len1, len2);
}

spbdd_handle tables::body_query(body& b, size_t /*DBG(len)*/) {
//	if (b.a) return alt_query(*b.a, 0);
//	if (b.ext) return b.q;
//	DBG(assert(bdd_nvars(b.q) <= b.ex.size());)
//	DBG(assert(bdd_nvars(get_table(b.tab, db)) <= b.ex.size());)
	if (b.tlast && b.tlast->b == tbls[b.tab].t->b) return b.rlast;
	b.tlast = tbls[b.tab].t;
	return b.rlast = (b.neg ? bdd_and_not_ex_perm : bdd_and_ex_perm)
		(b.q, tbls[b.tab].t, b.ex, b.perm);
//	DBG(assert(bdd_nvars(b.rlast) < len*bits);)
//	if (b.neg) b.rlast = bdd_and_not_ex_perm(b.q, ts[b.tab].t, b.ex,b.perm);
//	else b.rlast = bdd_and_ex_perm(b.q, ts[b.tab].t, b.ex, b.perm);
//	return b.rlast;
//	return b.rlast = bdd_permute_ex(b.neg ? b.q % ts[b.tab].t :
//			(b.q && ts[b.tab].t), b.ex, b.perm);
}

auto handle_cmp = [](const spbdd_handle& x, const spbdd_handle& y) {
	return x->b < y->b;
};

spbdd_handle tables::alt_query(alt& a, size_t /*DBG(len)*/) {
	if (a.f) {
		bdd_handles f; //form
		formula_query(a.f, f);
		//TODO: complete for any type, only for ints by now
		if (a.f->ex_h.size() != 0 ) {
			append_num_typebits(f[0], a.f->varslen_h);
			a.rlast = f[0];
		}
		else a.rlast = f[0] == hfalse ? hfalse : htrue;
		return a.rlast;
	}

	bdd_handles v1 = { a.rng, a.eq };
	spbdd_handle x;
	//DBG(assert(!a.empty());)

	for (size_t n = 0; n != a.size(); ++n)
		if (hfalse == (x = body_query(*a[n], a.varslen))) {
			a.insert(a.begin(), a[n]), a.erase(a.begin() + n + 1);
			return hfalse;
		} else v1.push_back(x);

	//NOTE: for over bdd arithmetic (currently handled as a bltin, although may change)
	// In case arguments/ATOMS are the same than last iteration,
	// here is were it should be avoided to recompute.
	spbdd_handle xg = htrue;
	if (a.grnd) xg = alt_query(*(a.grnd), 0); // vars grounding query
	body_builtins(xg, &a, v1);

	sort(v1.begin(), v1.end(), handle_cmp);
	if (v1 == a.last) return a.rlast;// { v.push_back(a.rlast); return; }
	if (!opts.bproof) return a.rlast =
		bdd_and_many_ex_perm(a.last = move(v1), a.ex, a.perm);
	a.levels.emplace(nstep, x = bdd_and_many(v1));
//	if ((x = bdd_and_many_ex(a.last, a.ex)) != hfalse)
//		v.push_back(a.rlast = x ^ a.perm);
//	bdd_handles v;
	return a.rlast = bdd_permute_ex(x, a.ex, a.perm);
//	if ((x = bdd_and_many_ex_perm(a.last, a.ex, a.perm)) != hfalse)
//		v.push_back(a.rlast = x);
//	return x;
//	DBG(assert(bdd_nvars(a.rlast) < len*bits);)
}

bool table::commit(DBG(size_t /*bits*/)) {
	if (add.empty() && del.empty()) return false;
	spbdd_handle x;
	if (add.empty()) x = t % bdd_or_many(move(del));
	else if (del.empty()) add.push_back(t), x = bdd_or_many(move(add));
	else {
		spbdd_handle a = bdd_or_many(move(add)),
				 d = bdd_or_many(move(del)), s = a % d;
//		DBG(assert(bdd_nvars(a) < len*bits);)
//		DBG(assert(bdd_nvars(d) < len*bits);)
		if (s == hfalse) return unsat = true;
		x = (t || a) % d;
	}
//	DBG(assert(bdd_nvars(x) < len*bits);)
	return x != t && (t = x, true);
}

char tables::fwd() noexcept {
	for (rule& r : rules) {
		bdd_handles v(r.size() == 0 ? 1 : r.size());
		spbdd_handle x;
		for (size_t n = 0; n != r.size(); ++n)
			//print(COUT << "rule: ", r) << endl,
			v[n] = alt_query(*r[n], r.len);
		if (v == r.last) { if (datalog) continue; x = r.rlast; }
		else r.last = v, x = r.rlast = bdd_or_many(move(v)) && r.eq;
		//DBG(assert(bdd_nvars(x) < r.len*bits);)
		if (x == hfalse) continue;
		(r.neg ? tbls[r.tab].del : tbls[r.tab].add).push_back(x);
		if (print_updates || populate_tml_update)
			decompress_update(o::inf(), x, r);
	}
	bool b = false;
	// D: just temp ugly static, move this out of fwd/pass in, or in tables.
	static map<ntable, set<term>> mhits;
	for (ntable tab = 0; (size_t)tab != tbls.size(); ++tab) {
		table& tbl = tbls[tab];
		if (tbl.is_builtin()) {
			DBG(assert(tbl.del.empty());) // negated builtin fail
			if (!tbl.add.empty()) {
				head_builtin(tbl.add, tbl, tab);
				tbl.add.clear();
				if (unsat || halt) return true;
			}
		}
		bool changes = tbl.commit(DBG(bits));
		b |= changes;
		if (tbl.unsat) return unsat = true;
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
	for (ntable n = 0; n != (ntable)tbls.size(); ++n) r[n] = tbls.at(n).t;
	return r;
}

bool tables::contradiction_detected() {
	error = true, o::err() << err_contradiction << endl;
#ifdef WITH_EXCEPTIONS
	throw contradiction_exception();
#endif
	return false;
}
bool tables::infloop_detected() {
	error = true, o::err() << err_infloop << endl;
#ifdef WITH_EXCEPTIONS
	throw infloop_exception();
#endif
	return false;
}

// adds __fp__ fact and returns true if __fp__ fact does not exist
bool tables::add_fixed_point_fact() {
	raw_term rt;
	rt.arity = { 0 };
	rt.e.emplace_back(elem::SYM, dict.get_lexeme(string("__fp__")));
	term t = from_raw_term(rt);
	bool exists = false;
	decompress(tbls[t.tab].t && from_fact(t), t.tab,
		[&exists](const term& /*t*/) { exists = true; }, t.size());
	if (!exists) tbls[t.tab].t = tbls[t.tab].t || from_fact(t); // add if ne
	tbls[t.tab].internal = true;
	return !exists;
}

bool tables::pfp(size_t nsteps, size_t break_on_step) {
	error = false;
	level l = get_front();
	fronts.push_back(l);
	if (opts.bproof) levels.emplace_back(l);
	for (;;) {
		if (print_steps || opts.optimize)
			o::inf() << "# step: " << nstep << endl;
		++nstep;
		bool fwd_ret = fwd();
		if (halt) return true;
		level l = get_front();
		if (!fwd_ret) {
			if(opts.fp_step && add_fixed_point_fact()) return pfp();
			else return fronts.push_back(l), true;
		} else  fronts.push_back(l);
		if (halt) return true;
		if (unsat) return contradiction_detected();
		if ((break_on_step && nstep == break_on_step) ||
			(nsteps && nstep == nsteps)) return false; // no FP yet
		bool is_repeat =
			std::find(fronts.begin(), fronts.end() - 1, l) != fronts.end() - 1;
		if (!datalog && is_repeat)
			return opts.pfp3 ? true : infloop_detected();
		if (opts.bproof) levels.push_back(move(l));
	}
	DBGFAIL;
}

/* Run the given program with the given settings, put the query
 * results into the given out-parameter, and return true in the case
 * that it reaches a fixed point. Otherwise just return false. */

bool tables::run_prog(const raw_prog &rp, dict_t &dict, const ::options &opts,
	std::set<raw_term> &results)
{
	tables::options to;
	to.bproof            = opts.enabled("proof");
	to.optimize          = opts.enabled("optimize");
	to.bin_transform     = opts.enabled("bin");
	to.print_transformed = opts.enabled("t");
	to.apply_regexpmatch = opts.enabled("regex");
	tables tbl(dict, to);
	strs_t strs;
	if(tbl.run_prog(rp, strs)) {
		for(const term &result : tbl.decompress()) {
			results.insert(tbl.to_raw_term(result));
		}
		return true;
	} else {
		return false;
	}
}

/* Run the given program on the given extensional database and yield
 * the derived facts. Returns true or false depending on whether the
 * given program reaches a fixed point. Useful for query containment
 * checks. */

bool tables::run_prog(const std::set<raw_term> &edb, raw_prog rp,
	dict_t &dict, const ::options &opts, std::set<raw_term> &results)
{
	std::map<elem, elem> freeze_map, unfreeze_map;
	// Create a duplicate of each rule in the given program under a
	// generated alias.
	for(int_t i = rp.r.size() - 1; i >= 0; i--) {
		for(raw_term &rt : rp.r[i].h) {
			raw_term rt2 = rt;
			auto it = freeze_map.find(rt.e[0]);
			if(it != freeze_map.end()) {
				rt.e[0] = it->second;
			} else {
				elem frozen_elem = elem::fresh_temp_sym(dict);
				// Store the mapping so that the derived portion of each
				// relation is stored in exactly one place
				unfreeze_map[frozen_elem] = rt.e[0];
				rt.e[0] = freeze_map[rt.e[0]] = frozen_elem;
			}
			rp.r.push_back(raw_rule(rt2, rt));
		}
	}
	// Now add the extensional database to the given program.
	for(const raw_term &rt : edb) {
		rp.r.push_back(raw_rule(rt));
	}
	// Run the program to obtain the results which we will then filter
	std::set<raw_term> tmp_results;
	bool result = run_prog(rp, dict, opts, tmp_results);
	// Filter out the result terms that are not derived and rename those
	// that are derived back to their original names.
	for(raw_term res : tmp_results) {
		auto jt = unfreeze_map.find(res.e[0]);
		if(jt != unfreeze_map.end()) {
			res.e[0] = jt->second;
			results.insert(res);
		}
	}
	return result;
}

bool tables::run_prog(const raw_prog& p, const strs_t& strs, size_t steps,
	size_t break_on_step)
{
	clock_t start{}, end;
	double t;
	if (opts.optimize) measure_time_start();
	if (opts.bitunv) this->typenv = const_cast<raw_prog&>(p).get_typenv();
	if (!add_prog(p, strs)) return false;
	if (opts.optimize) {
		end = clock(), t = double(end - start) / CLOCKS_PER_SEC;
		o::ms() << "# pfp: ";
		measure_time_start();
	}
	DBG(o::dbg()<<endl<<p<<endl);

	nlevel begstep = nstep;
	bool r = true;
	// run program only if there are any rules
	if (rules.size()) {
		fronts.clear();
		r = pfp(steps ? nstep + steps : 0, break_on_step);
	} else {
		level l = get_front();
		fronts = {l, l};
	}
	size_t went = nstep - begstep;
	if (r && prog_after_fp.size()) {
		if (!add_prog(move(prog_after_fp), {}, false)) return false;
		r = pfp();
	}
	if (r && p.nps.size()) { // after a FP run the seq. of nested progs
		for (const raw_prog& np : p.nps) {
			steps -= went; begstep = nstep;
			r = run_prog(np, strs, steps, break_on_step);
			went = nstep - begstep;
			if (!r && went >= steps) break;
		}
	}
	if (opts.optimize)
		(o::ms() <<"add_prog: "<<t << " pfp: "),
		measure_time_end();
	return r;
}

tables::tables(dict_t dict, tables::options opts) :
	dict(move(dict)), opts(move(opts)) {}

tables::~tables() {
	//if (opts.optimize) delete &dict;
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
