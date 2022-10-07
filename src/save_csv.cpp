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
#include "driver.h"
using namespace std;

void driver::save_csv() const {
	map<elem, ofstream> files;
	#ifndef REMOVE_IR_BUILDER_FROM_TABLES
	tbl->out([&files](const raw_term& t) {
		auto it = files.find(t.e[0]);
		if (it == files.end()) {
			std::string fname = to_string(lexeme2str(t.e[0].e))
				+ ".csv";
			o::inf() << "Saving " << fname << endl;
			files.emplace(t.e[0], ofstream(fname));
			it = files.find(t.e[0]);
		}
		std::ostream& os = it->second;
		//auto elem2str = [](const elem&e) { return lexeme2str(e.e); };
		if (t.neg) os << '~';
		for (size_t ar = 0, n = 1; ar != t.arity.size();) {
			while (t.arity[ar] == -1) ++ar;
			if (n >= t.e.size()) break;
			while (t.e[n].type == elem::OPENP) ++n;
			for (int_t k = 0; k != t.arity[ar];)
				if ((os<<quote_sym(t.e[n++]),
					++k!=t.arity[ar])) os<<'\t';
			while (n<t.e.size() && t.e[n].type == elem::CLOSEP) ++n;
			++ar;
			while (ar < t.arity.size() && t.arity[ar] == -2) ++ar;
			if (ar > 1 && t.arity[ar-1] == -2 &&
				ar != t.arity.size()) os << '\t';
		}
		os << endl;
	});
	#endif // REMOVE_IR_BUILDER_FROM_TABLES
}
