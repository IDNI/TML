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
#include <random>
#include <dlfcn.h>
#include "tables.h"

using namespace std;

void tables::fact_builtin(const term& b) {
	blt_ctx c(b);
	bltins.run_head(c);
}

void tables::head_builtin(const bdd_handles& hs, const table& tbl, ntable tab) {
	blt_ctx c(term(false,tab,ints(tbl.len, 0), 0, tbl.idbltin));
	//COUT << "head_builtin: " << hs << endl;
	for (auto h : hs) decompress(h, tab, [&c, this] (const term& t){
		// ground builtin vars by decompressed head
		//COUT << "head_builtin t: " << t << endl;
		for (size_t n = 0; n != t.size(); ++n) c.g[n] = t[n];
		bltins.run_head(c);
	}, 0, true);
}

void tables::body_builtins(spbdd_handle x, alt* a, bdd_handles& hs) {
	if (x == hfalse) return; // return if grounding failed
	vector<blt_ctx> ctx;
	for (term bt : a->bltins) // create contexts for each builtin
		ctx.emplace_back(bt, a); //, ctx.back().a = &a;
	if (a->bltinvars.size())	{ // decompress grounded terms
	    decompress(x,0, [&ctx, this] (const term t) {
		for (blt_ctx& c : ctx) {
			c.g = c.t; // ground vars by decompressed term
			for (size_t n = 0; n != c.g.size(); ++n)
				if (c.g[n] < 0 && has(c.a->bltinvars, c.g[n]))
					c.g[n] = t[c.a->grnd->vm.at(c.g[n])];
			bltins.run_body(c);
		}
	    }, a->grnd->varslen);
	    // collect outputs
	    for (blt_ctx& c : ctx) for (auto out : c.outs) hs.push_back(out);
	} else for (blt_ctx& c : ctx) { // no grounding -> just run
		bltins.run_body(c);
		for (auto out : c.outs) hs.push_back(out); // collect outputs
	}
}

bool tables::init_builtins() {
	const bool H = true, B = false;
	bltins.reset(dict);
	set<string> syms{ "alpha","alnum","digit","space","printable" };
	for (auto sym : syms) bltins.add(sym);

	bltins.add(H, "halt",          0, 0, [this](blt_ctx&) {
		//COUT << "halting" << endl;
		halt  = true; });
	bltins.add(H, "error",         0, 0, [this](blt_ctx&) {
		//COUT << "erroring" << endl;
		error = true; });
	bltins.add(H, "false",         0, 0, [this](blt_ctx&) {
		//COUT << "falsing" << endl;
		unsat = true; });
	bltins.add(H, "forget",        0, 0, [this](blt_ctx& c) {
		//COUT << "forgetting" << endl;
		bltins.forget(c); });
	bltins.add(B, "rnd", 3, 1, [this](blt_ctx& c) {
	//	// TODO: check that it's num const
		//COUT << "rnd " << c.g << " " << to_raw_term(c.g) << endl;
		int_t arg0 = c.arg_as_int(0);
		int_t arg1 = c.arg_as_int(1);
		//COUT << "arg0: " << arg0 << endl;
		//COUT << "arg1: " << arg1 << endl;
	//	DBG(assert(t.size() == 3););
		if (arg0 > arg1) swap(arg0, arg1);
		//int_t rnd = arg0 + (std::rand() % (arg1 - arg0 + 1));
		random_device rd;
		mt19937 gen(rd());
		uniform_int_distribution<> distr(arg0, arg1);
		int_t rnd = distr(gen);
		DBG(o::dbg()<<"rnd("<<arg0<<" "<<arg1<<" "<<rnd<<endl;)
		c.out(from_sym(c.outvarpos(0), c.a->varslen, c.mknum(rnd)));
	});
	
	bltins.add(B, "count", 2, 1, [this](blt_ctx& c) {
		spbdd_handle x = htrue;
		body* b = 0;		
		for (auto p : c.a->varbodies)
			if (p.first == c.arg(0)) b = p.second,
				x = b ? x && p.second->rlast : p.second->rlast;
		if (!b) return;
		if (b->inv.empty()) b->inv= b->init_perm_inv(c.a->varslen*bits);
		int_t cnt = bdd::satcount(x, b->inv);
		//COUT << "count result: " << cnt << endl;
		c.out(from_sym(c.outvarpos(), c.a->varslen, c.mknum(cnt)));
	}, 1);

	return  init_bdd_builtins() &&
		init_print_builtins() &&
		init_js_builtins();
}

bool tables::init_bdd_builtins() {
	const bool B = false;
	auto get_bw_h = [this](t_arith_op op) {
		return [this, op](blt_ctx& c) {
			bdd_handles hs;
			c.args_bodies(hs);
			c.out(bitwise_handler(
				c.varpos(0), c.varpos(1), c.varpos(2),
				hs[0], hs[1], c.a->varslen, op));
		};
	};
	auto get_pw_h = [this](t_arith_op op) {
		return [this, op](blt_ctx& c) {
			bdd_handles hs;
			c.args_bodies(hs);
			c.out(pairwise_handler(
				c.varpos(0), c.varpos(1), c.varpos(2),
				hs[0], hs[1], c.a->varslen, op));
		};
	};
	bltins.add(B, "bw_and",  3, 1, get_bw_h(BITWAND), 2);
	bltins.add(B, "bw_or",   3, 1, get_bw_h(BITWOR),  2);
	bltins.add(B, "bw_xor",  3, 1, get_bw_h(BITWXOR), 2);
	bltins.add(B, "bw_not",  3, 1, get_bw_h(BITWNOT), 2);
	bltins.add(B, "pw_add",  3, 1, get_pw_h(ADD),     2);
	bltins.add(B, "pw_mult", 3, 1, get_pw_h(MULT),    2);
	return true;
}

bool tables::init_print_builtins() {
	const bool H = true, B = false;
	auto printer = [this](bool ln, bool to, bool delim) {
		return [this, ln, to, delim] (blt_ctx& c) {
			//COUT << "printing ln/to/delim" << ln << "/" << to << "/" << delim << " " << to_raw_term(c.g) << endl;
			print_to_delimited(to_raw_term(c.g), error, to, delim)
				<< (ln ? "\n" : "");
		};
	};
	const bool NLN = false, NTO = false, NDLM = false;
	const bool  LN = true,   TO = true,   DLM = true;
	blt_handler h;
	bltins.add(H, "print",            -1, 0, h = printer(NLN, NTO, NDLM));
	bltins.add(B, "print",            -1, 0, h);
	bltins.add(H, "println",          -1, 0, h = printer( LN, NTO, NDLM));
	bltins.add(B, "println",          -1, 0, h);
	bltins.add(H, "println_to",       -1, 0, h = printer( LN,  TO, NDLM));
	bltins.add(B, "println_to",       -1, 0, h);
	bltins.add(H, "print_to",         -1, 0, h = printer(NLN,  TO, NDLM));
	bltins.add(B, "print_to",         -1, 0, h);
	bltins.add(H, "print_delim",      -1, 0, h = printer(NLN, NTO,  DLM));
	bltins.add(B, "print_delim",      -1, 0, h);
	bltins.add(H, "println_delim",    -1, 0, h = printer( LN, NTO,  DLM));
	bltins.add(B, "println_delim",    -1, 0, h);
	bltins.add(H, "print_to_delim",   -1, 0, h = printer(NLN,  TO,  DLM));
	bltins.add(B, "print_to_delim",   -1, 0, h);
	bltins.add(H, "println_to_delim", -1, 0, h = printer( LN,  TO,  DLM));
	bltins.add(B, "println_to_delim", -1, 0, h);
	return true;
}

bool tables::init_js_builtins() {
	const bool H = true, B = false;
	blt_handler h;
#ifdef __EMSCRIPTEN__
	bltins.add(H, "js_eval", -1, 0, h = [this](blt_ctx& c) {
		emscripten_run_script(to_string(to_raw_term(c.g)).c_str()); });
	bltins.add(B, "js_eval", -1, 0, h);
	//bltins.add(B, "js_eval_to_int", -1, 1, [this](blt_ctx& c) {
	//	term t(c.g);
	//	t.pop_back(); // remove last argument
	//	int r = emscripten_run_script_int(
	//		to_string((to_raw_term(t))).c_str());
	//	//COUT << "js_eval_to_int result: " << r << endl;
	//	// TODO check for universe size
	//	c.out(from_sym(c.outvarpos(), c.a->varslen, c.mknum(r)));
	//});
	//bltins.add(B, "js_eval_to_sym", -1, 1, [this](blt_ctx& c) {
	//	term t(c.g);
	//	t.pop_back(); // remove last argument
	//	string r = emscripten_run_script_string(
	//		to_string((to_raw_term(t))).c_str());
	//	//COUT << "js_eval_to_sym result: " << r << endl;
	//	//size_t nsyms = dict.nsyms();
	//	int_t sym = dict.get_sym(dict.get_lexeme(r));
	//	// TODO check for universe size
	//	// if (sym >= nsyms) DBGFAIL; // new sym in universe!
	//	c.out(from_sym(c.outvarpos(), c.a->varslen, sym));
	//});
#else // TODO embed a JS engine if not in browser?
	bltins.add(H, "js_eval", -1, 0, h = [this](blt_ctx) {
		o::err() << "js_eval is available only in a browser environment"
			" (ignoring)." << endl;
	});
	bltins.add(B, "js_eval", -1, 0, h);
	//bltins.add(B, "js_eval_to_int", -1, 1, h);
	//bltins.add(B, "js_eval_to_sym", -1, 1, h);
#endif
	return true;
}

