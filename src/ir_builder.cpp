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
#include "analysis.h"
using namespace std;

#define mkchr(x) (opts.bitunv? ((int_t)(x)):(((((int_t)(x))<<2)|1)))
#define mknum(x) (opts.bitunv? ((int_t)(x)):(((((int_t)(x))<<2)|2)))

ir_builder::ir_builder(dict_t& dict_, rt_options& opts_/*, environment& env_*/) :
		dict(dict_), opts(opts_) /*, typenv(env_),*/ /*dynenv(0)*/ {
}
ir_builder::~ir_builder() {
}

void unquote(string_t& str) {
	for (size_t i = 0; i != str.size(); ++i)
		if (str[i] == (unsigned char) '\\') str.erase(str.begin() + i);
}

string_t _unquote(string_t str) { unquote(str); return str; }

void align_vars(vector<term>& v) {
	map<int_t, int_t> m;
	for (size_t k = 0; k != v.size(); ++k)
		for (size_t n = 0; n != v[k].size(); ++n)
			if (v[k][n] < 0 && !has(m, v[k][n]))
				m.emplace(v[k][n], -m.size() - 1);
	if (!m.empty()) for (term& t : v) t.replace(m);
}

/*
void align_vars_form(form* qbf,  map<int_t, int_t> &m) {
	if (qbf->arg < 0 && !has(m, qbf->arg)) m.emplace(qbf->arg, -m.size() - 1);
	if (qbf->tm)
		for (size_t n = 0; n != qbf->tm->size(); ++n) {
			if ((*(qbf->tm))[n] < 0 && !has(m, (*(qbf->tm))[n]))
				m.emplace((*(qbf->tm))[n], -m.size() - 1);
		}
	if (qbf->l)	align_vars_form(qbf->l, m);
	if (qbf->r) align_vars_form(qbf->r, m);
}

void replace_form(form* qbf,  map<int_t, int_t> &m) {
	if (qbf->tm)(*(qbf->tm)).replace(m);
	if (qbf->l)	replace_form(qbf->l, m);
	if (qbf->r) replace_form(qbf->r, m);
}

void align_vars_form(vector<term>& v) {
	assert(v.size() == 2);
	map<int_t, int_t> m;
	for (size_t n = 0; n != v[0].size(); ++n)
		if (v[0][n] < 0 && !has(m, v[0][n]))
			m.emplace(v[0][n], -m.size() - 1);
	align_vars_form(v[1].qbf.get(), m);
	if (!m.empty()) {
		v[0].replace(m);
		replace_form(v[1].qbf.get(), m);
	}
}
*/

flat_prog ir_builder::to_terms(const raw_prog& p) {
	flat_prog m;
	vector<term> v;
	term t;

	for (const raw_rule& r : p.r)
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

			for (const raw_term& x : r.h) {
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
	for(const auto &[functor, arity] : p.hidden_rels)
		dynenv->tbls[dynenv->get_table(get_sig(functor, arity))].hidden = true;
	
	return m;
}

sig ir_builder::get_sig(const raw_term&t) {
	int_t aux = dict.get_rel(t.e[0].e);
	return{aux ,t.arity};
}
sig ir_builder::get_sig(const lexeme& rel, const ints& arity) {
	return { dict.get_rel(rel), arity };
}
size_t ir_builder::sig_len(const sig& s) {
	size_t r = 0;
	for (int_t x : get<ints>(s)) if (x > 0) r += x;
	return r;
}

term ir_builder::from_raw_term(const raw_term& r, bool isheader, size_t orderid) {
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
			case elem::NUM:
				t.push_back(mknum(r.e[n].num)); break;
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
			case elem::SYM: t.push_back(dict.get_sym(r.e[n].e)); break;
			default: ;
		}
	// stronger 'realrel' condition for tables, only REL and header BLTIN
	ntable tab = realrel ? dynenv->get_table(get_sig(r)) : -1;
	// D: idbltin name isn't handled above (only args, much like rel-s & tab-s).
	if (extype == term::BLTIN) {
		int_t idbltin = dict.get_bltin(r.e[0].e);
		if (tab > -1) {
			// header BLTIN rel w table, save alongside table (for decomp. etc.)
			dynenv->tbls[tab].idbltin = idbltin;
			dynenv->tbls[tab].bltinargs = t; // if needed, for rule/header (all in tbl)
			dynenv->tbls[tab].bltinsize = nvars; // number of vars (<0)
			//count_if(t.begin(), t.end(), [](int i) { return i < 0; });
		}
		return term(r.neg, tab, t, orderid, idbltin,
			(bool) (r.e[0].num & 1), (bool) (r.e[0].num & 2));
	}
	return term(r.neg, extype, r.arith_op, tab, t, orderid);
	// ints t is elems (VAR, consts) mapped to unique ints/ids for perms.
}

elem ir_builder::get_elem(int_t arg) const {
	if (arg < 0) return elem(elem::VAR, dict.get_var_lexeme(arg));
	if( opts.bitunv == false) {
		if (arg & 1) return elem((char32_t) (arg >> 2));
		if (arg & 2) return elem((int_t) (arg >> 2));
	}
	else if(arg == 1 || arg == 0) return elem((bool)(arg));
	return elem(elem::SYM, dict.get_sym(arg));
}

void ir_builder::get_nums(const raw_term& t) {
	for (const elem& e : t.e)
		if (e.type == elem::NUM) nums = max(nums, e.num);
		else if (e.type == elem::CHR) chars = max(chars, (int_t)e.ch);
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

raw_term ir_builder::to_raw_term(const term& r) const {
		raw_term rt;
		rt.neg = r.neg;
		size_t args;
		if (r.extype == term::EQ) {//r.iseq)
			args = 2, rt.e.resize(args + 1), rt.e[0] = get_elem(r[0]),
			rt.e[1] = elem(elem::SYM, dict.get_lexeme(r.neg ? "!=" : "=")),
			rt.e[2] = get_elem(r[1]), rt.arity = {2}, rt.extype = raw_term::EQ;
			return rt;
		} else if (r.extype == term::LEQ) {//r.isleq)
			args = 2, rt.e.resize(args + 1), rt.e[0] = get_elem(r[0]),
			rt.e[1] = elem(elem::SYM, dict.get_lexeme("<=")),
			rt.e[2] = get_elem(r[1]), rt.arity = {2}, rt.extype = raw_term::LEQ;
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
				dict.get_bltin(r.idbltin));
			rt.e[0].num = r.renew << 1 | r.forget;
			rt.arity = { (int_t) args };
			for (size_t n = 1; n != args + 1; ++n)
				rt.e[n] = get_elem(r[n - 1]);
			rt.add_parenthesis();
		}
		else {
			if (r.tab != -1) {
				args = dynenv->tbls.at(r.tab).len, rt.e.resize(args + 1);
				rt.e[0] = elem(elem::SYM,
						dict.get_rel(get<0>(dynenv->tbls.at(r.tab).s)));
				rt.arity = get<ints>(dynenv->tbls.at(r.tab).s);
				for (size_t n = 1; n != args + 1; ++n)
					rt.e[n] = get_elem(r[n - 1]);
				rt.add_parenthesis();
			} else {
				args = 1;
				rt.e.resize(args);
				rt.e[0] = get_elem(r[0]);
			}
		}
		DBG(assert(args == r.size());)
		if( opts.bitunv ) {
			if(dynenv->spbu.get()->brev_transform(rt))
				rt.calc_arity(nullptr);
		}
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

			fresh_int = dt.get_fresh_var();
		else
			fresh_int = dt.get_fresh_sym();

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

void form::printnode(int lv, const ir_builder* tb) {
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
	int_t relp = dict.get_rel(dict.get_lexeme("equals"));
	svalt.tab = dynenv->get_table({relp, {(int_t)svalt.size()}});
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

	if (dynenv->str_rels.size() > 1) er(err_one_input);
	if (dynenv->str_rels.empty()) return false;
	eqr.resize(3); // three rules for substr equality
	for(size_t r = 0; r < eqr.size(); r++) {
		int_t var = 0;
		int_t i= --var, j= --var , k=--var, n= --var;
		ntable nt = dynenv->get_table({dict.get_rel(dict.get_lexeme("equals")), {4}});
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
			for( int vi=0; vi<2; vi++)
				eqr[r].emplace_back(false, term::textype::REL, t_arith_op::NOP,
									dynenv->get_table({*dynenv->str_rels.begin(),{2}}),
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

bool ir_builder::transform_grammar(vector<production> g, flat_prog& p, form*& /*r*/ ) {
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
	if (dynenv->strs.size() && enable_regdetect_matching) {
		string inputstr = to_string(dynenv->strs.begin()->second);
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
							t.tab = dynenv->get_table({dict.get_rel(elem.e),{2}});
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
					t.tab = dynenv->get_table({dict.get_rel(elem.e),{2}});
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
			t.tab = dynenv->get_table({dict.get_rel(x.p[0].e),{2}});
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

		// ref: maps ith sybmol production to resp. terms
		std::map<size_t, term> refs;
		DBG(o::dbg()<<x;)
		for (int_t n = 0; n != (int_t)x.p.size(); ++n) {
			term t;
			if (builtins.find(x.p[n].e) != builtins.end()) {
				t.tab = dynenv->get_table({*dynenv->str_rels.begin(), {3}});
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
				t.tab = dynenv->get_table({dict.get_rel(x.p[n].e),{2}});
				if (n) t[0] = -n, t[1] = -n-1;
				else t[0] = -1, t[1] = -(int_t)(x.p.size());
			} else if (x.p[n].type == elem::CHR) {
				unary_string us(sizeof(char32_t)*8);
				us.buildfrom(u32string(1, x.p[n].ch));
				int_t tv=n;
				//DBG(us.toprint(o::dbg()));
				for( auto rl: us.sort_rel) {
					int_t r = dict.get_rel(dict.get_lexeme(us.getrelin_str(rl)));
					term t; t.resize(1);
					t.tab= dynenv->get_table({r, {1}});
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
			dict.get_var_lexeme(dict.get_fresh_var());

		transform_grammar_constraints(x, v, p, refs);

		p.insert(move(v));
	}
	if (opts.print_transformed) printer->print(printer->print(o::to("transformed")
		<< "# after transform_grammar:\n", p)
		<< "\n# run after a fixed point:\n", dynenv->prog_after_fp)
		<< endl;
	return true;
}
