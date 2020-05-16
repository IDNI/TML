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
#include "tables.h"
#include "dict.h"
#include "input.h"
#include "output.h"
#include "err.h"
#include "infer_types.h"
#include "addbits.h"
#include "form.h"

form::ftype transformer::getdual(form::ftype type) {
	switch (type) {
	case form::ftype::OR: return form::ftype::AND;
	case form::ftype::AND: return form::ftype::OR;
	case form::ftype::FORALL1: return form::ftype::EXISTS1;
	case form::ftype::FORALL2: return form::ftype::EXISTS2;
	case form::ftype::EXISTS1: return form::ftype::FORALL1;
	case form::ftype::EXISTS2: return form::ftype::FORALL2;
	default: throw 0;
	}
}

bool demorgan::push_negation(form*& root) {

	if (!root) return false;
	if (root->type == form::ftype::AND ||
		root->type == form::ftype::OR) {

		root->type = getdual(root->type);
		if (!push_negation(root->l) ||
			!push_negation(root->r))
			throw 0;
		return true;
	}
	else if (allow_neg_move_quant && root->isquantifier()) {
		root->type = getdual(root->type);
		if (!push_negation(root->r)) throw 0;

		return true;
	}
	else {
		if (root->type == form::ftype::NOT) {
			form* t = root;
			root = root->l;
			t->l = t->r = NULL;
			delete t;
			return true;
		}
		else if (root->type == form::ftype::ATOM) {
			form* t = new form(form::ftype::NOT, 0, NULL, root);
			root = t;
			return true;
		}
		return false;
	}

}

bool demorgan::apply(form*& root) {

	if (root && root->type == form::ftype::NOT &&
		root->l->type != form::ftype::ATOM) {

		bool changed = push_negation(root->l);
		if (changed) {
			form* t = root;
			root = root->l;
			t->l = t->r = NULL;
			delete t;
			return true;
		}

	}
	return false;
}

bool implic_removal::apply(form*& root) {
	if (root && root->type == form::ftype::IMPLIES) {
		root->type = form::OR;
		form* temp = new form(form::NOT);
		temp->l = root->l;
		root->l = temp;
		return true;
	}
	return false;
}

bool substitution::apply(form*& phi) {
	if (phi && phi->type == form::ATOM) {
		if (phi->tm == NULL) {
			// simple quant leaf declartion
			auto it = submap_var.find(phi->arg);
			if (it != submap_var.end())		//TODO: Both var/sym should have mutually excl.
				return phi->arg = it->second, true;
			else if ((it = submap_sym.find(phi->arg)) != submap_sym.end())
				return phi->arg = it->second, true;
			else return false;
		}
		else {
			bool changed = false;
			for (int& targ : *phi->tm) {
				auto it = submap_var.find(targ);
				if (it != submap_var.end())		//TODO: Both var/sym should have mutually excl.
					targ = it->second, changed = true;
				else if ((it = submap_sym.find(targ)) != submap_sym.end())
					targ = it->second, changed = true;

			}
			return changed;
		}

	}
	return false;
}

void findprefix(form* curr, form*& beg, form*& end) {

	if (!curr || !curr->isquantifier()) return;

	beg = end = curr;
	while (end->r && end->r->isquantifier())
		end = end->r;
}

bool pull_quantifier::dosubstitution(form* phi, form* prefend) {

	substitution subst;
	form* temp = phi;

	int_t fresh_int;
	while (true) {
		if (temp->type == form::FORALL1 ||
			temp->type == form::EXISTS1 ||
			temp->type == form::UNIQUE1)

			fresh_int = dt.get_fresh_var(temp->l->arg);
		else
			fresh_int = dt.get_fresh_sym(temp->l->arg);

		subst.add(temp->l->arg, fresh_int);

		wprintf(L"\nNew fresh: %d --> %d ", temp->l->arg, fresh_int);
		if (temp == prefend) break;
		else temp = temp->r;
	}

	return subst.traverse(phi);
}

bool pull_quantifier::apply(form*& root) {

	bool changed = false;
	if (!root || root->isquantifier()) return false;

	form* curr = root;
	form* lprefbeg = NULL, * lprefend = NULL, * rprefbeg = NULL, * rprefend = NULL;

	findprefix(curr->l, lprefbeg, lprefend);
	findprefix(curr->r, rprefbeg, rprefend);

	if (lprefbeg && rprefbeg) {

		if (!dosubstitution(lprefbeg, lprefend) ||
			!dosubstitution(rprefbeg, rprefend))
			throw 0;
		curr->l = lprefend->r;
		curr->r = rprefend->r;
		lprefend->r = rprefbeg;
		rprefend->r = curr;
		root = lprefbeg;
		changed = true;
		wprintf(L"\nPulled both: ");
		wprintf(L"%d %d , ", lprefbeg->type, lprefbeg->arg);
		wprintf(L"%d %d\n", rprefbeg->type, rprefbeg->arg);
	}
	else if (lprefbeg) {
		if (!dosubstitution(lprefbeg, lprefend))
			throw 0;
		curr->l = lprefend->r;
		lprefend->r = curr;
		root = lprefbeg;
		changed = true;
		wprintf(L"\nPulled left: ");
		wprintf(L"%d %d\n", lprefbeg->type, lprefbeg->arg);
	}
	else if (rprefbeg) {
		if (!dosubstitution(rprefbeg, rprefend))
			throw 0;
		curr->r = rprefend->r;
		rprefend->r = curr;
		root = rprefbeg;
		changed = true;
		wprintf(L"\nPulled right: ");
		wprintf(L"%d %d\n", rprefbeg->type, rprefbeg->arg);
	}
	return changed;
}

bool pull_quantifier::traverse(form*& root) {

	bool changed = false;
	if (root == NULL) return false;
	if (root->l) changed |= traverse(root->l);
	if (root->r) changed |= traverse(root->r);

	changed = apply(root);

	return changed;
}

bool transformer::traverse(form*& root) {
	bool changed = false;
	if (root == NULL) return false;

	changed = apply(root);

	if (root->l) changed |= traverse(root->l);
	if (root->r) changed |= traverse(root->r);


	return changed;
}

void form::printnode(int lv) {
	if (r) r->printnode(lv + 1);
	wprintf(L"\n");
	for (int i = 0; i < lv; i++)
		wprintf(L"\t");
	wprintf(L" %d %d", type, arg);
	if (l) l->printnode(lv + 1);
}

