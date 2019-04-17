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
#include "driver.h"
using namespace std;

typedef pair<wstring, int_t> relarity;
typedef set<relarity> relarities;

void get_relarities(const raw_prog& p, relarities& all, relarities& tabling);
wostream& output_xsb_rule(wostream& os, const raw_rule& r);
wostream& output_xsb_term(wostream& os, const raw_term& t);
wostream& output_xsb_elem(wostream& os, const elem& e);

#define output_lexeme_adjust_first(os, l, fn) { (os)<< (wchar_t)fn(*((l)[0])); \
	if ((l)[1]-((l)[0]+1) > 0) (os) << lexeme{(l)[0]+1,(l)[1]}; }

wostream& driver::print_term_xsb(wostream& os, const term& t) const {
	if (t.neg()) os << L'~';
	output_lexeme_adjust_first(os, dict.get_rel(t.rel()), tolower);
	os << L'(';
	int_t skip, l = 0;
	for (size_t ar = 0, n = 0; ar != t.arity().size();) {
		skip = 0;
		while (t.arity()[ar] == -1) ++ar, os <<
			(l++ && t.arity()[ar-2] == 1 ? L"(" : (++skip, L""));
		for (int_t k = 0; k != t.arity()[ar]; ++k) {
			if (t.arg(n) < 0) throw 0;//os<<dict.get_var(t.args[n]);
			else if (t.arg(n) & 1) os << (wchar_t)(t.arg(n)>>2);
			else if (t.arg(n) & 2) os << (int_t)(t.arg(n)>>2);
			else if ((size_t)(t.arg(n)>>2) < dict.nsyms())
				output_lexeme_adjust_first(os, dict.get_sym(t.arg(n)), tolower)
			else os << L'[' << (t.arg(n)>>2) << L']';
			if (++n != t.nargs() && k != t.arity()[ar]-1) os << L',';
		}
		++ar;
		while (ar<t.arity().size() && t.arity()[ar] == -2) ar++,
			os << (--l && !skip ? L")" : (--skip, L""));
		if (ar > 1 && t.arity()[ar-1] == -2 &&
			ar != t.arity().size()) os<<L",";
	}
	return os << L")";
}

wostream& driver::print_xsb(wostream& os, const raw_prog& p) const {
	relarities all, tabling;
	get_relarities(p, all, tabling);
	os << L"% start of XSB program" << endl << endl;
	os << L"% {" << endl;
	for (auto x : p.r) output_xsb_rule(os, x) << endl;
	os << L"% }" << endl << endl;
	os << L"% enable tabling for all relations in heads"
		<< L" to avoid inf. loops:" << endl;
	for (auto ra : tabling) os << L":- table " << ra.first <<
		L'/' << ra.second << L'.' << endl;
	os << endl;
	os << L"% find all and dump to stdout:" << endl;
	os << L"dump_list([])." << endl;
	os << L"dump_list([H|T]) :- writeln(H), dump_list(T)."<< endl;
	os << L"dump(Q) :- findall(Q, Q, X), dump_list(X)." << endl;
	for (auto ra : all) {
		os << L":- dump(" << ra.first << L'(';
		for(int_t i = 0; i != ra.second; ++i) os << (i ? L",_" : L"_");
		os << L"))." << endl;
	}
	os << endl;
	os << L":- halt." << endl << endl;
	os << L"% end of XSB program" << endl;
	return os;
}

void get_relarities(const raw_prog& p, relarities& all, relarities& tabling) {
	wstring rel;
	int_t ar, trigger;
	for (auto r : p.r) {
		for (auto t : r.heads()) {
			rel = lexeme2str(t.e[0].e);
			rel[0] = towlower(rel[0]);
			ar = t.arity[0];
			trigger = 0;
			if (ar == 0)
				for (auto a : t.arity) {
					if (a == -1) trigger++;
					else if (a == -2 && !--trigger) ar++;
				}
			relarity ra = { rel, ar };
			all.insert(ra);
			if (r.nbodies()) tabling.insert(ra);
		}
		for (auto t : r.bodies())
			if (t.arity.size() == 1) {
				ar = t.arity[0];
				trigger = 0;
				if (ar == 0) {
					for (int_t a : t.arity)
						if (a == -1) trigger++;
						else if (a == -2 && !--trigger) ar++;
				}
				rel = lexeme2str(t.e[0].e);
				rel[0] = towlower(rel[0]);
				all.insert({ rel, t.arity[0] });
			}
	}
}

wostream& output_xsb_rule(wostream& os, const raw_rule& r) {
	switch (r.type) {
		case raw_rule::GOAL: os << L"% !" << endl; break;
		case raw_rule::TREE: os << L"% !!" << endl; break;
		default: ;
	}
	for (size_t n = 0; n < r.nheads(); ++n)
		if (output_xsb_term(os, r.head(n)), n != r.nheads() - 1) os << L',';
	if (!r.nbodies()) return os << L'.';
	os << L" :- ";
	for (size_t n = 0; n < r.nbodies(); ++n)
		if (output_xsb_term(os, r.body(n)), n != r.nbodies() - 1) os << L',';
	return os << L'.';
}

wostream& output_xsb_term(wostream& os, const raw_term& t) {
	if (t.neg) os << L'~';
	output_xsb_elem(os, t.e[0]);
	os << L'(';
	for (size_t ar = 0, n = 1; ar != t.arity.size();) {
		while (t.arity[ar] == -1) ++ar, os << L'(';
		if (n >= t.e.size()) break;
		while (t.e[n].type == elem::OPENP) ++n;
		for (int_t k = 0; k != t.arity[ar];)
			if (output_xsb_elem(os, t.e[n++]), ++k != t.arity[ar]) os << L", ";
		while (n < t.e.size() && t.e[n].type == elem::CLOSEP) ++n;
		++ar;
		while (ar < t.arity.size() && t.arity[ar] == -2) ++ar, os<<L')';
		if (ar > 0 && t.arity[ar-1] == -2 && ar != t.arity.size()) os<<", ";
	}
	return os << L')';
}

wostream& output_xsb_elem(wostream& os, const elem& e) {
	switch (e.type) {
		case elem::CHR:
			return os << '\'' <<
				(e.ch == '\'' || e.ch == '\\' ? L"\\" : L"") <<
				e.ch << '\'';
		case elem::VAR:
			output_lexeme_adjust_first(os,
				(lexeme{ e.e[0]+1, e.e[1] }), towupper);
			return os;
		case elem::OPENP:
		case elem::CLOSEP: return os << *e.e[0];
		case elem::NUM: return os << e.num;
		default:
			output_lexeme_adjust_first(os, e.e, towlower);
			return os;
	}
}
