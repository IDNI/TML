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

#include "tables_progress.h"

using namespace std;

void tables_progress::add_tml_update(tables &ts, const term& t, bool neg) {
	// TODO: decompose nstep if too big for the current universe
	ir_handler.nums = max(ir_handler.nums, (int_t)ts.nstep);
	ints arity = { (int_t) ir_handler.sig_len(ts.tbls.at(t.tab).s)};
	arity[0] += 3;
	ntable tab = ir_handler.get_table(ir_handler.get_sig(ts.rel_tml_update, arity));
	ints args = { mknum(ts.nstep), (neg ? ts.sym_del : ts.sym_add),
		dict.get_sym(dict.get_rel_lexeme(ts.tbls[t.tab].s.first)) };
	args.insert(args.end(), t.begin(), t.end());
	ts.tbls[tab].add.push_back(ts.from_fact(term(false, tab, args, 0, -1)));
}

void tables_progress::notify_update(tables &t, spbdd_handle& x, const rule& r) {
	nlevel step             = t.nstep - 1;
	static bool   printed   = false;
	static nlevel last_step = step;
	if (last_step != step) printed = false, last_step = step;
	if (t.print_updates) {
		if (!t.print_steps && !printed)
			o::inf() << "# step: " << step << endl, printed = true;
		// TODO fix operator<< for rules
	}
	t.decompress(x, r.tab, [&t, &r, this](const term& x) {
		if (t.print_updates)
			o::inf() << (r.neg ? "~" : "") << ir_handler.to_raw_term(x) << ". ";
		if (t.populate_tml_update) add_tml_update(t, x, r.neg);
	});
	if (t.print_updates) o::inf() << endl;
}
