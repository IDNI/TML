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


namespace idni {
	
template <typename T>
void driver::out_goals(std::basic_ostream<T> &os) {
	if (tbl->goals.size()) {
		bdd_handles trues, falses, undefineds;
		// TODO Change this, fixpoint should be computed before
		// requesting to output the goals.
		if(tbl->compute_fixpoint(trues, falses, undefineds)) {
			for (term t : tbl->goals) {
				tbl->decompress(trues[t.tab], t.tab, 
					[&os, this](const term& r) {
						os << ir->to_raw_term(r) << ".\n"; 
					});
			}
		}
	}
}

template 
void driver::out_goals(std::basic_ostream<char> &os);
template 
void driver::out_goals(std::basic_ostream<wchar_t> &os);

template <typename T>
void driver::out_fixpoint(std::basic_ostream<T> &os) {
	bdd_handles trues, falses, undefineds;
	// TODO Change this, fixpoint should be computed before
	// requesting to output the fixpoint.
	if(tbl->compute_fixpoint(trues, falses, undefineds)) {
		for(ntable n = 0; n < (ntable)trues.size(); n++) {
			if(rt_opts.show_hidden || !tbl->tbls[n].hidden) {
				tbl->decompress(trues[n], n, [&os, this](const term& r) {
					os << ir->to_raw_term(r) << '.' << endl;
				});
			}
		}
	}
}

template
void driver::out_fixpoint(std::basic_ostream<char> &os);
template
void driver::out_fixpoint(std::basic_ostream<wchar_t> &os);

template <typename T>
void driver::out_result(std::basic_ostream<T> &os) {
		if (tbl) {
			if (tbl->goals.size()) out_goals(os);
			else out_fixpoint(os);
		}
}

template
void driver::out_result(std::basic_ostream<char> &os);
template
void driver::out_result(std::basic_ostream<wchar_t> &os);

} // namespace idni