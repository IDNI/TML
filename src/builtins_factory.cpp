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
#include "builtins.h"
#include "driver.h"
#include "builtins_factory.h"

using namespace std;

extern uints perm_init(size_t n);

lexeme get_lexeme(ccs w, size_t l) {
	static std::set<lexeme, lexcmp> strs_extra;
	static 	std::vector<ccs> strs_allocated;
	if (l == (size_t)-1) l = strlen(w);
	auto it = strs_extra.find({ w, w + l });
	if (it != strs_extra.end()) return *it;
	cstr r = strdup(w);
	strs_allocated.push_back(r);
	lexeme lx = { r, r + l };
	strs_extra.insert(lx);
	return lx;
}
lexeme get_lexeme(const std::basic_string<unsigned char>& s) {
	ccs w = s.c_str();
	return get_lexeme(w, s.size());
}
lexeme get_lexeme(const std::basic_string<char>& s) {
	ccs w = (ccs) s.c_str();
	return get_lexeme(w, s.size());
}

builtins_factory& builtins_factory::add_basic_builtins() {
	// TODO builtins should be managed in a separated object unrelated 
	// to dict. Dict could contain a given builtin object a delegate queires
	// to it, but not otherwise.
	const bool H = true, B = false;
	set<string> syms{ "alpha","alnum","digit","space","printable" };
	for (auto sym : syms) dict.get_bltin(sym);

	bltins.add(H, dict.get_bltin(get_lexeme("halt")), "halt",  0, 0, [this](blt_ctx& c) {
		//COUT << "halting" << endl;
		c.tbls->halt  = true; });
	bltins.add(H, dict.get_bltin(get_lexeme("error")), "error", 0, 0, [this](blt_ctx& c) {
		//COUT << "erroring" << endl;
		c.tbls->error = true; });
	bltins.add(H, dict.get_bltin(get_lexeme("false")), "false", 0, 0, [this](blt_ctx& c) {
		//COUT << "falsing" << endl;
		c.tbls->unsat = true; });
	bltins.add(H, dict.get_bltin(get_lexeme("forget")), "forget", 0, 0, [this](blt_ctx& c) {
		//COUT << "forgetting" << endl;
		c.tbls->bltins.forget(c); });
	bltins.add(B, dict.get_bltin(get_lexeme("rnd")), "rnd", 3, 1, [this](blt_ctx& c) {
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
		c.out(c.tbls->from_sym(c.outvarpos(0), c.a->varslen, mknum(rnd)));
	});
	
	bltins.add(B, dict.get_bltin(get_lexeme("count")), "count", -1, 1, [this](blt_ctx& c) {
		/*
		for (auto x : *c.hs) {
			COUT << "bltin args\n";
			::out(COUT, x)<<endl<<endl;
		}
		*/
		spbdd_handle x = bdd_and_many(*c.hs);

		// -------------------------------------------------------
		//COUT << "count in\n";
		//::out(COUT, x)<<endl<<endl;
		size_t nargs = c.a->vm.size();
		uints perm = perm_init(nargs * (c.tbls->bits));
		int_t aux = 0;
		bools ex;
		int_t varsout = 0; //counts number of args that are ex
		for (size_t i = 0; i < c.tbls->bits; ++i)
			for (size_t j = 0; j< nargs; ++j)
				if(j == ((size_t)abs(*c.a->bltoutvars.begin())-1) ||
					(c.a->bltngvars.size() != 0 &&
					 c.a->bltngvars.find(-(j+1)) == c.a->bltngvars.end())) {
					ex.push_back(true);
					if (i == 0) varsout++;
				}
				else{
					perm[i*nargs+j] = aux;
					aux++;
					ex.push_back(false);
				}
		//x =  x/ex;
		//x =  x^perm;
		x = bdd_permute_ex(x,ex,perm);
		//COUT << "count after ex\n";
		//::out(COUT, x)<<endl<<endl;
		size_t cnt2 = satcount(x, (c.tbls->bits) * (c.a->varslen-varsout));
		//DBG(COUT << "count2 result: " << cnt2 << endl;)
		c.out(c.tbls->from_sym(c.outvarpos(), c.a->varslen, mknum(cnt2)));
	}, -1);

	return  *this;
}

builtins_factory& builtins_factory::add_bdd_builtins() {
	const bool B = false;
	auto get_bw_h = [this](t_arith_op op) {
		return [this, op](blt_ctx& c) {
			bdd_handles hs;
			c.args_bodies(hs);
			c.out(c.tbls->bitwise_handler(
				c.varpos(0), c.varpos(1), c.varpos(2),
				hs[0], hs[1], c.a->varslen, op));
		};
	};
	auto get_pw_h = [this](t_arith_op op) {
		return [this, op](blt_ctx& c) {
			//for (auto x : *c.hs) {
			//	COUT << "bltin args\n";
			//	::out(COUT, x)<<endl<<endl;
			//}

			bdd_handles hs;
			c.args_bodies(hs);
			c.out(c.tbls->pairwise_handler(
				c.varpos(0), c.varpos(1), c.varpos(2),
				hs[0], hs[1], c.a->varslen, op));
		};
	};
	auto bltin_leq_handler = [this]() {
		return [this](blt_ctx& c) {
			spbdd_handle arg0, arg1;
			size_t i = 0;
			size_t arg0_w = 0,arg1_w = 0;
			spbdd_handle const0 = htrue, const1 = htrue;

			assert(false && "BIT_TRASFORM leq_handler is disabled");
			/*
			for (auto &x : tab_type.at(c.t.tab)){
				//COUT << "bits " << x.pty.bsz << endl;
				if (i == 0) arg0_w = x.pty.bsz;
				else if (i == 1) arg1_w = x.pty.bsz;
				i++;
			}
			*/

			//workaround to get constants
			if (c.t[0] >= 0 || c.t[1] >= 0) {
				for (size_t i = 0; i < c.t.size(); ++i) {
					if (c.t[i] >= 0 && i % 2 == 0)
						const0 = const0 && ::from_bit(arg0_w-(i>>1) , c.t[i] == 1);
					else if (c.t[i] >= 0 && i % 2 == 1)
						const1 = const1 && ::from_bit(arg0_w+arg1_w-(i>>1)-1, c.t[i] == 1);
				}
			}

			//bdd_handles hs;
			//TODO debug why hs[1] is not created
			//c.args_bodies(hs);
			//::out(COUT, hs[0])<<endl<<endl;
			//::out(COUT, hs[1])<<endl<<endl;

			//TODO get output var, ?x or ?y
			i = 0;
			bool dual = false;
			for (auto x : *c.hs) {
				//COUT << "bltin args\n";
				//get ordering
				if(c.t[0] > c.t[1] && c.t[0] < 0) {
					if (i == 2) arg0 = x;
					else if (i == 3) arg1 = x;
				} else {
					dual = true;
					if (i == 2) arg1 = x;
					else if (i == 3) arg0 = x;
				}
				i++;
				//::out(COUT, x)<<endl<<endl;
			}

			spbdd_handle s0 = const0;
			if (const0 == htrue)
				s0 = c.tbls->perm_bit_reverse_bt(arg0, arg0_w, 0);
			//COUT << "### S0:"<< endl;
			//::out(COUT, s0)<<endl<<endl;

			spbdd_handle s1 = const1;
			if (const1 == htrue)
				s1 = c.tbls->perm_bit_reverse_bt(arg1, arg1_w, arg0_w);
			//COUT << "### S1:"<< endl;
			//::out(COUT, s1)<<endl<<endl;

			assert( bdd_root(s0) < bdd_root(s1) && "LEQ_handler: wrong assumed term/argument ordering");

			//COUT << " nvars : " << c.a->varslen;
			//COUT << ", total bits : " << bits << endl;
			//COUT << c.varpos(0), c.varpos(1),

			spbdd_handle leq = htrue;
			if (!dual)
				leq = bdd_leq(/*hs[0]*/ s0, s1 /*hs[1]*/, arg0_w, arg1_w
						/*, c.varpos(0), c.varpos(1), c.a->varslen , bits*/);
			else
				COUT << "LEQ_handler: DUAL operator GEQ is work in progress\n";

			//spbdd_handle m = bdd_max(s1, arg1_w)
			//COUT << "Leq Handler output MSB2LSB:"<< endl;
			//::out(COUT, leq)<<endl<<endl;

			//TODO: arg0_w when ?x in head, arg1_w when ?y in head
			spbdd_handle s2 = c.tbls->perm_bit_reverse_bt(leq, arg0_w, 0);
			//COUT << "Leq Handler output:"<< endl;
			//::out(COUT, s2)<<endl<<endl;

			c.out(s2);
			//hs.clear();
		};
	};

	bltins.add(B, dict.get_bltin(get_lexeme("bw_and")), "bw_and", 3, 1, get_bw_h(BITWAND), 2);
	bltins.add(B, dict.get_bltin(get_lexeme("bw_or")), "bw_or", 3, 1, get_bw_h(BITWOR),  2);
	bltins.add(B, dict.get_bltin(get_lexeme("bw_xor")), "bw_xor", 3, 1, get_bw_h(BITWXOR), 2);
	bltins.add(B, dict.get_bltin(get_lexeme("bw_not")), "bw_not", 3, 1, get_bw_h(BITWNOT), 2);
	bltins.add(B, dict.get_bltin(get_lexeme("pw_add")), "pw_add", 3, 1, get_pw_h(ADD),     2);
	bltins.add(B, dict.get_bltin(get_lexeme("pw_mult")), "pw_mult", 3, 1, get_pw_h(MULT),    2);
	bltins.add(B, dict.get_bltin(get_lexeme("leq")), "leq", 2, 1, bltin_leq_handler(), 2);
	return *this;
}

builtins_factory& builtins_factory::add_print_builtins() {
	const bool H = true, B = false;
	auto printer = [this](bool ln, bool to, bool delim) {
		return [this, ln, to, delim] (blt_ctx& c) {
			//COUT << "printing ln/to/delim" << ln << "/" << to << "/" << delim << " " << to_raw_term(c.g) << endl;
		};
	};
	const bool NLN = false, NTO = false, NDLM = false;
	const bool  LN = true,   TO = true,   DLM = true;
	blt_handler h;
	bltins.add(H, dict.get_bltin(get_lexeme("print")), "print",            -1, 0, h = printer(NLN, NTO, NDLM));
	bltins.add(B, dict.get_bltin(get_lexeme("print")), "print",           -1, 0, h);
	bltins.add(H, dict.get_bltin(get_lexeme("println")), "println",         -1, 0, h = printer( LN, NTO, NDLM));
	bltins.add(B, dict.get_bltin(get_lexeme("println")), "println",         -1, 0, h);
	bltins.add(H, dict.get_bltin(get_lexeme("println_to")), "println_to",      -1, 0, h = printer( LN,  TO, NDLM));
	bltins.add(B, dict.get_bltin(get_lexeme("println_to")), "println_to",      -1, 0, h);
	bltins.add(H, dict.get_bltin(get_lexeme("print_to")), "print_to",        -1, 0, h = printer(NLN,  TO, NDLM));
	bltins.add(B, dict.get_bltin(get_lexeme("print_to")), "print_to",        -1, 0, h);
	bltins.add(H, dict.get_bltin(get_lexeme("print_delim")), "print_delim",     -1, 0, h = printer(NLN, NTO,  DLM));
	bltins.add(B, dict.get_bltin(get_lexeme("print_delim")), "print_delim",     -1, 0, h);
	bltins.add(H, dict.get_bltin(get_lexeme("println_delim")), "println_delim",   -1, 0, h = printer( LN, NTO,  DLM));
	bltins.add(B, dict.get_bltin(get_lexeme("println_delim")), "println_delim",   -1, 0, h);
	bltins.add(H, dict.get_bltin(get_lexeme("print_to_delim")), "print_to_delim",  -1, 0, h = printer(NLN,  TO,  DLM));
	bltins.add(B, dict.get_bltin(get_lexeme("print_to_delim")), "print_to_delim",  -1, 0, h);
	bltins.add(H, dict.get_bltin(get_lexeme("println_to_delim")), "println_to_delim", -1, 0, h = printer( LN,  TO,  DLM));
	bltins.add(B, dict.get_bltin(get_lexeme("println_to_delim")), "println_to_delim", -1, 0, h);
	return *this;
}

builtins_factory& builtins_factory::add_js_builtins() {
	const bool H = true, B = false;
	blt_handler h;
#ifdef __EMSCRIPTEN__
	bltins.add(H, "js_eval", -1, 0, h = [this](blt_ctx& c) {
		emscripten_run_script(to_string(
			ir_handler->to_raw_term(c.g)).c_str()); });
	bltins.add(B, "js_eval", -1, 0, h);
	//bltins.add(B, "js_eval_to_int", -1, 1, [this](blt_ctx& c) {
	//	term t(c.g);
	//	t.pop_back(); // remove last argument
	//	int r = emscripten_run_script_int(
	//		to_string((to_raw_term(t))).c_str());
	//	//COUT << "js_eval_to_int result: " << r << endl;
	//	// TODO check for universe size
	//	c.out(from_sym(c.outvarpos(), c.a->varslen, mknum(r)));
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
	bltins.add(H, dict.get_bltin(get_lexeme("js_eval")), "js_eval", -1, 0, h = [](blt_ctx) {
		o::err() << "js_eval is available only in a browser environment"
			" (ignoring)." << endl;
	});
	bltins.add(B, dict.get_bltin(get_lexeme("js_eval")), "js_eval", -1, 0, h);
	//bltins.add(B, "js_eval_to_int", -1, 1, h);
	//bltins.add(B, "js_eval_to_sym", -1, 1, h);
#endif
	return *this;
}
