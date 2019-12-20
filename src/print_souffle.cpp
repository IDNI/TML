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
#include <sstream>
#include "driver.h"
using namespace std;

typedef pair<wstring, bools> relation_info;
typedef set<relation_info> relations_info;

map<wstring, bools> default_type_signatures;

wstring souffle_rel_name(wstring rel, bools p);
relation_info get_rel_info(const raw_term& t);
relations_info get_rels_info(const raw_prog& p);
wostream& output_souffle_rule(wostream& os, const raw_rule& r);
wostream& output_souffle_term(wostream& os, const raw_term& t);
wostream& output_souffle_elem(wostream& os, const elem& e);

wostream& driver::print_souffle(wostream& os, const raw_prog& p) const {
	relations_info rels_info = get_rels_info(p);
	os << L"// start of Souffle program" << endl;
	os << endl;
	os << L"// Following declaration types are autodetected!" << endl;
	os << L"// Please review and correct declaration of your model:" <<endl;
	for (auto ri : rels_info) {
		os << L".decl " << ri.first << L'(';
		for (size_t i = 0; i != ri.second.size(); ++i)
			os << (i?L", ":L"") << "v" << (i+1) << ": " <<
			(ri.second[i] ? "number" : "symbol");
		os << L')' << endl;
	}
	os << endl;
	for (auto ri : rels_info) os << L".output " << ri.first << endl;
	os << endl;
	os << L"// {" << endl;
	for (auto x : p.r) output_souffle_rule(os, x) << endl;
	os << L"// }" << endl;
	os << L"// end of Soufflé program" << endl;
	return os;
}

wstring souffle_rel_name(wstring rel, bools p) {
//	DBG(o::out() << L"souffle_rel_name(" << rel << L", [ " << p << " ])" << endl;)
	auto it = default_type_signatures.find(rel);
	if (it == default_type_signatures.end()) {
		default_type_signatures[rel] = p;
		//DBG(o::out() << L"\treturn " << rel << endl;)
		return rel;
	}
//	DBG(o::out() << L"\tbools == dts["<<rel<<"]? " << (p == default_type_signatures[rel]? L'1' : L'0') << endl;)
	if (p == default_type_signatures[rel]) return rel;
	wstringstream wss;
	wss << rel << (p.size() ? L'_' : L'0');
	for (bool param : p) wss << (param ? L'1' : L'0');
	//DBG(o::out() << L"\treturn " << wss.str() << endl;)
	return wss.str();
}

relation_info get_rel_info(const raw_term& t) {
	wstring rel = lexeme2str(t.e[0].e);
	bools p = {};
	bool search = true;
	size_t l = 0;
	if (t.e.size() == 1) return { souffle_rel_name(rel, p), p };
	for (size_t i = 2; i < t.e.size(); ) {
		while (t.e[i].type == elem::OPENP) ++i, ++l;
		if (search) {
			search = false;
			p.push_back(t.e[i].type == elem::NUM ||
				t.e[i].type == elem::VAR);
		}
		++i;
		while (t.e[i].type == elem::CLOSEP) ++i, --l;
		if (!l) search = true;
	}
	return { souffle_rel_name(rel, p), p };
}

relations_info get_rels_info(const raw_prog& p) {
	relations_info ri;
	for (auto r : p.r) {
		for (auto t : r.h)
			ri.insert(get_rel_info(t));
		for (auto b : r.b) for (auto t : b)
			if (t.arity.size() == 1)
				ri.insert(get_rel_info(t));
	}
	return ri;
}

wostream& output_souffle_rule(wostream& os, const raw_rule& r) {
	switch (r.type) {
		case raw_rule::GOAL: os << L"// !" << endl; break;
		case raw_rule::TREE: os << L"// !!" << endl; break;
		default: ;
	}
	for (size_t n = 0; n < r.h.size(); ++n)
		if (output_souffle_term(os, r.h[n]), n != r.h.size() - 1)
			os << L',';
	if (!r.b.size()) return os << L'.';
	os << L" :- ";
	for (size_t m = 0; m < r.b.size(); ++m) {
		for (size_t n = 0; n < r.b[m].size(); ++n)
			if (output_souffle_term(os, r.b[m][n]),
				n != r.b[m].size() - 1) os << L',';
		if (m != r.b.size() - 1) os << L';';
	}
	return os << L'.';
}

wostream& output_souffle_term(wostream& os, const raw_term& t) {
	if (t.neg) os << L'!';
	relation_info ri = get_rel_info(t);
	os << ri.first << L'(';
	for (size_t ar = 0, n = 1; ar != t.arity.size();) {
		while (t.arity[ar] == -1) ++ar, os << L'(';
		if (n >= t.e.size()) break;
		while (t.e[n].type == elem::OPENP) ++n;
		for (int_t k = 0; k != t.arity[ar];) {
			if (output_souffle_elem(os,t.e[n++]),
				++k != t.arity[ar]) os << L", ";
		}
		while (n < t.e.size() && t.e[n].type == elem::CLOSEP) ++n;
		++ar;
		while (ar < t.arity.size() && t.arity[ar] == -2) ++ar, os<<L')';
		if (ar > 0 && t.arity[ar-1] == -2 && ar != t.arity.size())
			os << ", ";
	}
	return os << L')';
}

wostream& output_souffle_elem(wostream& os, const elem& e) {
	switch (e.type) {
		case elem::CHR:
			os << L'"';
			switch (e.ch) {
				case L'"':
				case L'\\': os << L'\\' << e.ch; break;
				case L'\r': os << L"\\r"; break;
				case L'\n': os << L"\\n"; break;
				case L'\t': os << L"\\t"; break;
				default: os << e.ch;
			}
			return os << L'"';
		case elem::VAR: return os << lexeme{ e.e[0]+1, e.e[1] };
		case elem::OPENP:
		case elem::CLOSEP: return os << *e.e[0];
		case elem::NUM: return os << e.num;
		default:
			return os << L'"' << e.e << L'"';
			// wstring el = lexeme2str(e.e);
			// array<wstring, 5> symbols = {
			// 	L"alpha", L"alnum", L"digit", L"space",
			// 	L"printable" };
			// for (const wstring &symbol : symbols)
			// 	if (el.compare(symbol) == 0)
			// 		return os << L'"' << e.e << L'"';
			// return os << e.e;
	}
}
