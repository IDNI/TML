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
#ifndef __FORM_H__
#define __FORM_H__
#include <cassert>
#include <vector>
#include <set>
#include <unordered_map>
#include <array>
#include <iostream>
#include <iomanip>
#include <cstdio>
#include <map>
#include <numeric>
#include <algorithm>
#include <functional>
#include "defs.h"

struct transformer;
struct form {
	friend struct transformer;

	int_t arg;
	term* tm;
	form* l;
	form* r;
	enum ftype {
		NONE, ATOM, FORALL1, EXISTS1, FORALL2, EXISTS2, UNIQUE1, UNIQUE2, AND, OR, NOT, IMPLIES, COIMPLIES
	} type;


	form() {
		type = NONE; l = NULL; r = NULL; arg = 0; tm = NULL;
	}

	form(ftype _type, int_t _arg = 0, term* _t = NULL, form* _l = NULL, form* _r = NULL) {
		arg = _arg; tm = _t; type = _type; l = _l; r = _r;
		if (_t) tm = new term(*_t); // , * tm = *_t;
		//if( _t) tm = new term(), *tm = *_t;
	}
	bool isquantifier() const {
		if (type == form::ftype::FORALL1 ||
			type == form::ftype::EXISTS1 ||
			type == form::ftype::UNIQUE1 ||
			type == form::ftype::EXISTS2 ||
			type == form::ftype::UNIQUE2 ||
			type == form::ftype::FORALL2)
			return true;
		return false;

	}

	~form() {
		if (l) delete l, l = NULL;
		if (r) delete r, r = NULL;
		if (tm) delete tm, tm = NULL;
	}
	void printnode(int lv = 0);
};

struct transformer {
	virtual bool apply(form*& root) = 0;
	form::ftype getdual(form::ftype type);
	virtual bool traverse(form*&);
};

struct implic_removal : public transformer {
	virtual bool apply(form*& root);
};

struct demorgan : public transformer {
	bool allow_neg_move_quant = false;
	bool push_negation(form*& root);
	virtual bool apply(form*& root);
	demorgan(bool _allow_neg_move_quant = false) {
		allow_neg_move_quant = _allow_neg_move_quant;
	}
};

struct pull_quantifier : public transformer {
	dict_t& dt;
	pull_quantifier(dict_t& _dt) : dt(_dt) {}
	virtual bool apply(form*& root);
	virtual bool traverse(form*& root);
	bool dosubstitution(form* phi, form* end);
};

struct substitution : public transformer {
	std::map<int_t, int_t> submap_var;
	std::map<int_t, int_t> submap_sym;

	void clear() { submap_var.clear(); submap_sym.clear(); }
	void add(int_t oldn, int_t newn) {
		if (oldn < 0)
			submap_var[oldn] = newn;
		else
			submap_sym[oldn] = newn;
	}

	virtual bool apply(form*& phi);

};

#endif // __FORM_H__