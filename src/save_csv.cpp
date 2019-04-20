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
#include <fstream>
#include <locale>
#include <codecvt>
#include "driver.h"
using namespace std;

wostream& driver::print_term_csv(wostream& os, const term& t) const {
	if (t.neg()) os << L'~';
	for (size_t ar = 0, n = 0; ar != t.arity().size();) {
		while (t.arity()[ar] == -1) ++ar;
		for (int_t k = 0; k != t.arity()[ar]; ++k) {
			if (t.arg(n) < 0) throw 0;
			else if (t.arg(n) & 1) os << (wchar_t)(t.arg(n)>>2);
			else if (t.arg(n) & 2) os << (int_t)(t.arg(n)>>2);
			else if ((size_t)(t.arg(n)>>2) < dict.nsyms())
				os << dict.get_sym(t.arg(n));
			else os << L'[' << (t.arg(n)>>2) << L']';
			if (++n != t.nargs() && k != t.arity()[ar]-1) os <<L'\t';
		}
		++ar;
		while (ar<t.arity().size() && t.arity()[ar] == -2) ar++;
		if (ar > 1 && t.arity()[ar-1] == -2 &&
			ar != t.arity().size()) os << L'\t';
	}
	return os;
}

void driver::save_csv(lp *p) const {
	save_csv(p->db, p->rng.bits);
}

void driver::save_csv(const db_t& db, size_t bits) const {
	map<int_t, wofstream> files;
	using convert_type = std::codecvt_utf8<wchar_t>;
	wstring_convert<convert_type, wchar_t> converter;
	for (auto x : db)
		if (builtin_rels.find(x.first.rel) == builtin_rels.end()) {
			auto it = files.find(x.first.rel);
			if (it == files.end()) {
				string fname = converter.to_bytes(
					lexeme2str(dict.get_rel(x.first.rel))) +
					".tml.csv";
				files.emplace(x.first.rel, wofstream(fname));
				it = files.find(x.first.rel);
			}
			wofstream& s = it->second;
			from_bits(x.second,bits,x.first,
				[&s,this](const term&t){
				print_term_csv(s, t)<<endl; });
		}
}
