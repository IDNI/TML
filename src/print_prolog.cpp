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
#include "driver.h"
using namespace std;

typedef pair<string, int_t> relarity;
typedef set<relarity> relarities;

relarity get_relarity(const raw_term& t);
void get_relarities(const raw_prog& p, relarities& ras);
template <typename T>
std::basic_ostream<T>& output_prolog_rule(std::basic_ostream<T>&, const raw_rule& r);
template <typename T>
std::basic_ostream<T>& output_prolog_term(std::basic_ostream<T>&, const raw_term& t);
template <typename T>
std::basic_ostream<T>& output_prolog_elem(std::basic_ostream<T>&, const elem& e);

#define output_lexeme_adjust_first(os, l, fn) (os) << (syschar_t)fn(*((l)[0])) <<\
	((l)[1]-((l)[0]+1)>0 ? lexeme{(l)[0]+1,(l)[1]} : lexeme{(l)[0], (l)[0]})

template <typename T>
std::basic_ostream<T>& driver::print_xsb(std::basic_ostream<T>& os,
	const raw_prog& rp) const
{
	return print_prolog(os, rp, XSB);
}
template ostream_t& driver::print_xsb(ostream_t& os, const raw_prog&) const;

template <typename T>
std::basic_ostream<T>& driver::print_swipl(std::basic_ostream<T>& os,
	const raw_prog& rp) const
{
	return print_prolog(os, rp, SWIPL);
}
template ostream_t& driver::print_swipl(ostream_t& os, const raw_prog&) const;

template <typename T>
std::basic_ostream<T>& driver::print_prolog(std::basic_ostream<T>& os,
	const raw_prog& p, prolog_dialect d) const
{
	relarities ras;
	get_relarities(p, ras);
	string name = d == SWIPL ? "SWI Prolog" : "XSB";
	os << "% start of " << name << " program" << endl;
	os << endl;
	os << "% enable tabling to avoid inf. loops" << endl;
	for (auto ra : ras) os << ":- table " << ra.first <<
		'/' << ra.second << '.' << endl;
	os << endl;
	if (d == SWIPL) {
		os << "% suppress singleton warnings" << endl;
		os << ":- style_check(-singleton)." << endl;
		os << endl;
		os << "% enable discontiguation" << endl;
		for (auto ra : ras) os << ":- discontiguous " << ra.first <<
			'/' << ra.second << '.' << endl,
		//for (auto ra : ras)
			os << ":- discontiguous '" << ra.first <<
			" tabled'" << '/' << ra.second << '.' << endl;
		os << endl;
		os << "% declare dynamic predicates" << endl;
		for (auto ra : ras) os << ":- dynamic '" << ra.first <<
			" tabled'" << '/' << ra.second << '.' << endl;
		os << endl;
	}
	os << "% {" << endl;
	for (auto x : p.r) output_prolog_rule(os, x) << endl;
	os << "% }" << endl;
	os << endl;
	os << "% find all and dump to stdout" << endl;
	os << "dump_list([])." << endl;
	os << "dump_list([H|T]) :- writeln(H), dump_list(T)."<< endl;
	os << "dump(Q) :- findall(Q, Q, X), dump_list(X)." << endl;
	for (auto ra : ras) {
		os << ":- dump(" << ra.first << '(';
		for(int_t i = 0; i != ra.second; ++i) os << (i ? ",_" : "_");
		os << "))." << endl;
	}
	os << endl;
	os << ":- halt." << endl;
	os << endl;
	os << "% end of "<< name << " program" << endl;
	return os;
}

template ostream_t& driver::print_prolog(ostream_t& os, const raw_prog&,
	prolog_dialect) const;

relarity get_relarity(const raw_term& t) {
	string rel = lexeme2str(t.e[0].e);
	rel[0] = towlower(rel[0]);
	int_t depth = 0, ar = t.arity[0];
	if (ar == 0)
		for (int_t a : t.arity) {
			if (a == -1) depth++;
			else if (a == -2 && !--depth) ar++;
		}
	return { rel, ar };
}

void get_relarities(const raw_prog& p, relarities& ras) {
	for (auto r : p.r) {
		for (auto t : r.h)
			ras.insert(get_relarity(t));
		for (auto b : r.b) for (auto t : b)
			ras.insert(get_relarity(t));
	}
}

template <typename T>
std::basic_ostream<T>& output_prolog_rule(std::basic_ostream<T>& os, const raw_rule& r) {
	switch (r.type) {
		case raw_rule::GOAL: os << "% !" << endl; break;
		case raw_rule::TREE: os << "% !!" << endl; break;
		default: ;
	}
	for (size_t n = 0; n < r.h.size(); ++n)
		if (output_prolog_term(os, r.h[n]), n != r.h.size() - 1)
			os << ',';
	if (!r.b.size()) return os << '.';
	os << " :- ";
	for (size_t m = 0; m < r.b.size(); ++m) {
		for (size_t n = 0; n < r.b[m].size(); ++n)
			if (output_prolog_term(os, r.b[m][n]),
				n != r.b[m].size() - 1) os << ',';
		if (m != r.b.size() - 1) os << ';';
	}
	return os << '.';
}

template <typename T>
std::basic_ostream<T>& output_prolog_term(std::basic_ostream<T>& os, const raw_term& t) {
	if (t.neg) os << '~';
	output_prolog_elem(os, t.e[0]);
	os << '(';
	for (size_t ar = 0, n = 1; ar != t.arity.size();) {
		while (t.arity[ar] == -1) ++ar, os << '(';
		if (n >= t.e.size()) break;
		while (t.e[n].type == elem::OPENP) ++n;
		for (int_t k = 0; k != t.arity[ar];)
			if (output_prolog_elem(os,t.e[n++]), ++k != t.arity[ar])
				os << ", ";
		while (n < t.e.size() && t.e[n].type == elem::CLOSEP) ++n;
		++ar;
		while (ar < t.arity.size() && t.arity[ar] == -2)
			++ar, os << ')';
		if (ar > 0 && t.arity[ar-1] == -2 && ar != t.arity.size())
			os << ", ";
	}
	return os << ')';
}

template <typename T>
std::basic_ostream<T>& output_prolog_elem(std::basic_ostream<T>& os, const elem& e) {
	switch (e.type) {
		case elem::CHR:
			os << '\'';
			switch (e.ch) {
				case '\'':
				case '\\': os << '\\' << e.ch; break;
				case '\r': os << "\\r"; break;
				case '\n': os << "\\n"; break;
				case '\t': os << "\\t"; break;
				default: os << e.ch;
			}
			return os << '\'';
		case elem::VAR: return output_lexeme_adjust_first(os,
			(lexeme{ e.e[0]+1, e.e[1] }), towupper);
		case elem::OPENP:
		case elem::CLOSEP: return os << *e.e[0];
		case elem::NUM: return os << e.num;
		default: return output_lexeme_adjust_first(os, e.e, towlower);
	}
}
