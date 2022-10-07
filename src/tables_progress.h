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

#ifndef _TABLES_PROGRESS_H_
#define _TABLES_PROGRESS_H_


#ifdef REMOVE_IR_BUILDER_FROM_TABLES

#include <functional>

#include "defs.h"
#include "ir_builder.h"
#include "dict.h"
#include "output.h"
#include "tables.h"
#include "printing.h"

/*! This class monitors the progress of the execution of tables. Right now it is
 * a straightforward consumer as all the functions return void. In a more complex 
 * scenario they could return a boolean to point if the execution should continue
 * or a more complex object to fine tune the forthcoming execution. */
class tables_progress : public tables::progress {
public:
	/* This objects are part of tables rightnow, the main task of this class
	 * is to remove them from tables. The label REMOVE_IR_BUILDER_FROM_TABLES
	 * control wheter this class is used or not. */
	std::reference_wrapper<dict_t> dict;
	std::reference_wrapper<ir_builder> ir_handler;
	std::reference_wrapper<std::ostream_t> os;

	void add_tml_update((const term& t, bool neg){
		ir_handler.get().nums = std::max(ir_handler.get().nums, ts.nstep);
		//ints arity(1,ir_handler->sig_len(tbls.at(t.tab).s));
		ints arity = { (int_t) ir_handler.get().sig_len(tbls.at(t.tab).s)};
		arity[0] += 3;
		ntable tab = ir_handler.get().get_table(ir_handler.get().get_sig(ts.rel_tml_update, ts.arity));
		ints args = { mknum(ts.nstep), (neg ? ts.sym_del : ts.sym_add),
			dict.get().get_sym(dict.get().get_rel_lexeme(tbls[t.tab].s.first)) };
		args.insert(args.end(), t.begin(), t.end());
		tbls[tab].add.push_back(from_fact(term(false, ts.tab, ts.args, 0, -1))); /* refactor from_fact function */
	}

	void notify_update(tables &ts, spbdd_handle& x, 
			const rule& r) override {
		nlevel step             = nstep - 1;
		static bool   printed   = false;
		static nlevel last_step = step;
		if (last_step != step) printed = false, last_step = step;
		if (print_updates) {
			if (!print_steps && !printed)
				os << "# step: " << step << endl, printed = true;
			print(os << "#       ", r) << "\n#   ->  ";
		}
		decompress(x, r.tab, [&os, &r, this](const term& x) {
			#ifndef REMOVE_IR_BUILDER_FROM_TABLES
			if (print_updates)
				os << (r.neg ? "~" : "") << ir_handler->to_raw_term(x) << ". ";
			#endif // REMOVE_IR_BUILDER_FROM_TABLES
			if (populate_tml_update) add_tml_update(x, r.neg);
		});
		if (print_updates) os << endl;
		return os;
	}

	void notify_fixedpoint(std::vector<table> &tbls) {
		ntable tab;
		static spbdd_handle h = 0;
		raw_term rt;
		rt.arity = { 0 };
		rt.e.emplace_back(elem::SYM, dict.get().get_lexeme(string("__fp__"))); /* refactor string function */
		term t = ir_handler.get().from_raw_term(rt);
		tab = t.tab;
		tbls[tab].hidden = true;
		h = from_fact(t); /* refactor from_fact function */
	}

	template <typename T>
	void notify_out_goals(term t) {
		os << ir_handler.get().to_raw_term(t) << ", " << '.'
	}

	void notify_run_prog(bdd_ref x) {
		ir_handler.get().nums = std::max(ir_handler.get().nums, (int_t) x.second.size()+1);
		unary_string us(32);
		us.buildfrom(x.second);
		ir_handler.get().chars = std::max(ir_handler.get().chars, (int_t) us.rel.size());

	}

	void notify_run_webp_prog(std::set<raw_term> &tmp_results, tables &tbl) {
		for(const term &result : tbl.decompress())
			tmp_results.insert(ir_handler.get().to_raw_term(result));
	}

	void notify_add_print_updates_states(std::string tname, rt_options& opts) {
		opts.pu_states.insert(ir_handler.get().get_table(
				ir_handler.get().get_sig(dict.get().get_lexeme(tname), {0})));
	}

	void notify_decompress_update(rule &r, spbdd_handle& x) {
		os << (r.neg ? "~" : "") << ir_handler.get().to_raw_term(x) << ". ";
	}

	bool notify_add_prog_wprod(flat_prog m, const std::vector<production>& g) {
		return ir_handler.get().transform_grammar(g, m);
	}

	#ifdef BIT_TRANSFORM
	void notify_decompress(table tbl, term r) {
		if (ir_handler.get()bitunv_decompress(r, tbl))
	}
	#endif

	void notify_out_fixpoint(term r) {
		os << ir_handler.get().to_raw_term(r) << '.' << std::endl; 
	}

	void notify_get_proof(term &t) {
		os << ir_handler.get().to_raw_term(t) << '.' << std::endl;
	}

	void notify_init_print_builtins(term t, bool error, bool ln, bool to, bool delim) {
		print_to_delimited(ir_handler.get().to_raw_term(t), error, to, delim)
		<< (ln ? "\n" : "")
		#ifdef __EMSCRIPTEN__
		<< std::flush
		#endif
		;
	}

	void print_dot(std::wstringstream &ss, gnode &gh,  std::wstring sp ) {
		ss  << std::endl<< sp << size_t(&gh) << L"[label=\""<< " "<< ir_handler.get().to_raw_term(gh.t)<< L"\"];";
	}

	void notify_print(term t) {
		os << b.first << ' ' << ir_handler.get().to_raw_term(b.second) << ' ';
	}
	
	template <typename T>
	void notify_print(size_t n, tables::proof_elem y, std::set<tables::proof_elem> x) {
		(os<<n<<' '<<ir_handler.get().to_raw_term(x)<<" :- "),
		print(os, y);
	}

	template <typename T>
	void notify_print(term t) {
		os << ir_handler->to_raw_term(t) << ", " << '.'
	}
};

#endif // REMOVE_IR_BUILDER_FROM_TABLES
#endif // _TABLES_PROGRESS_H_