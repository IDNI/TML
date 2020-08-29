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

typedef pair<string, bools> relation_info;
typedef set<relation_info> relations_info;

map<string, bools> default_type_signatures;

string souffle_rel_name(string rel, bools p);
relation_info get_rel_info(const raw_term& t);
relations_info get_rels_info(const raw_prog& p);
template <typename T>
std::basic_ostream<T>& output_souffle_rule(std::basic_ostream<T>&, const raw_rule& r);
template <typename T>
std::basic_ostream<T>& output_souffle_term(std::basic_ostream<T>&, const raw_term& t);
template <typename T>
std::basic_ostream<T>& output_souffle_elem(std::basic_ostream<T>&, const elem& e);

template <typename T>
std::basic_ostream<T>& driver::print_souffle(std::basic_ostream<T>& os, const raw_prog& p) const {
	relations_info rels_info = get_rels_info(p);
	os << "// start of Souffle program" << endl;
	os << endl;
	os << "// Following declaration types are autodetected!" << endl;
	os << "// Please review and correct declaration of your model:" <<endl;
	for (auto ri : rels_info) {
		os << ".decl " << ri.first << '(';
		for (size_t i = 0; i != ri.second.size(); ++i)
			os << (i?", ":"") << "v" << (i+1) << ": " <<
			(ri.second[i] ? "number" : "symbol");
		os << ')' << endl;
	}
	os << endl;
	for (auto ri : rels_info) os << ".output " << ri.first << endl;
	os << endl;
	os << "// {" << endl;
	for (auto x : p.r) output_souffle_rule(os, x) << endl;
	os << "// }" << endl;
	os << "// end of Soufflé program" << endl;
	return os;
}
template ostream_t& driver::print_souffle(ostream_t& os, const raw_prog&) const;


string souffle_rel_name(string rel, bools p) {
//	DBG(o::out() << "souffle_rel_name(" << rel << ", [ " << p << " ])" << endl;)
	auto it = default_type_signatures.find(rel);
	if (it == default_type_signatures.end()) {
		default_type_signatures[rel] = p;
		//DBG(o::out() << "\treturn " << rel << endl;)
		return rel;
	}
//	DBG(o::out() << "\tbools == dts["<<rel<<"]? " << (p == default_type_signatures[rel]? '1' : '0') << endl;)
	if (p == default_type_signatures[rel]) return rel;
	stringstream ss;
	ss << rel << (p.size() ? '_' : '0');
	for (bool param : p) ss << (param ? '1' : '0');
	//DBG(o::out() << "\treturn " << wss.str() << endl;)
	return ss.str();
}

relation_info get_rel_info(const raw_term& t) {
	string rel = ws2s(lexeme2str(t.e[0].e));
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

template <typename T>
std::basic_ostream<T>& output_souffle_rule(std::basic_ostream<T>& os, const raw_rule& r) {
	switch (r.type) {
		case raw_rule::GOAL: os << "// !" << endl; break;
		case raw_rule::TREE: os << "// !!" << endl; break;
		default: ;
	}
	for (size_t n = 0; n < r.h.size(); ++n)
		if (output_souffle_term(os, r.h[n]), n != r.h.size() - 1)
			os << ',';
	if (!r.b.size()) return os << '.';
	os << " :- ";
	for (size_t m = 0; m < r.b.size(); ++m) {
		for (size_t n = 0; n < r.b[m].size(); ++n)
			if (output_souffle_term(os, r.b[m][n]),
				n != r.b[m].size() - 1) os << ',';
		if (m != r.b.size() - 1) os << ';';
	}
	return os << '.';
}

template <typename T>
std::basic_ostream<T>& output_souffle_term(std::basic_ostream<T>& os, const raw_term& t) {
	if (t.neg) os << '!';
	relation_info ri = get_rel_info(t);
	os << ri.first << '(';
	for (size_t ar = 0, n = 1; ar != t.arity.size();) {
		while (t.arity[ar] == -1) ++ar, os << '(';
		if (n >= t.e.size()) break;
		while (t.e[n].type == elem::OPENP) ++n;
		for (int_t k = 0; k != t.arity[ar];) {
			if (output_souffle_elem(os,t.e[n++]),
				++k != t.arity[ar]) os << ", ";
		}
		while (n < t.e.size() && t.e[n].type == elem::CLOSEP) ++n;
		++ar;
		while (ar < t.arity.size() && t.arity[ar] == -2) ++ar, os<<')';
		if (ar > 0 && t.arity[ar-1] == -2 && ar != t.arity.size())
			os << ", ";
	}
	return os << ')';
}

template <typename T>
std::basic_ostream<T>& output_souffle_elem(std::basic_ostream<T>& os, const elem& e) {
	switch (e.type) {
		case elem::CHR:
			os << '"';
			switch (e.ch) {
				case '"':
				case '\\': os << '\\' << e.ch; break;
				case '\r': os << "\\r"; break;
				case '\n': os << "\\n"; break;
				case '\t': os << "\\t"; break;
				default: os << e.ch;
			}
			return os << '"';
		case elem::VAR: return os << lexeme{ e.e[0]+1, e.e[1] };
		case elem::OPENP:
		case elem::CLOSEP: return os << *e.e[0];
		case elem::NUM: return os << e.num;
		default:
			return os << '"' << e.e << '"';
			// string el = lexeme2str(e.e);
			// array<string, 5> symbols = {
			// 	"alpha", "alnum", "digit", "space",
			// 	"printable" };
			// for (const string &symbol : symbols)
			// 	if (el.compare(symbol) == 0)
			// 		return os << '"' << e.e << '"';
			// return os << e.e;
	}
}
