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
	map<elem, wofstream> files;
	tbl->out([&files](const raw_term& t) {
		auto it = files.find(t.e[0]);
		if (it == files.end()) {
			wstring wfname = lexeme2str(t.e[0].e) + L".csv";
			o::inf() << L"Saving " << wfname << endl;
			files.emplace(t.e[0],
				wofstream(ws2s(wfname)));
			it = files.find(t.e[0]);
		}
		wofstream& os = it->second;
		if (t.neg) os << L'~';
		for (size_t ar = 0, n = 1; ar != t.arity.size();) {
			while (t.arity[ar] == -1) ++ar;
			if (n >= t.e.size()) break;
			while (t.e[n].type == elem::OPENP) ++n;
			for (int_t k = 0; k != t.arity[ar];)
				if ((os<<t.e[n++]),++k!=t.arity[ar]) os<<L'\t';
			while (n<t.e.size() && t.e[n].type == elem::CLOSEP) ++n;
			++ar;
			while (ar < t.arity.size() && t.arity[ar] == -2) ++ar;
			if (ar > 1 && t.arity[ar-1] == -2 &&
				ar != t.arity.size()) os << L'\t';
		}
		os << endl;
	});
}
