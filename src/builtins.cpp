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

#include "builtins.h"
#include "tables.h"

using namespace std;

size_t blt_ctx::varpos(size_t arg) const { return a->vm.at(g[arg]); }

int_t blt_ctx::outvarpos(size_t oarg) const {
	size_t size = args == -1 ? g.size() : args;
	DBG(assert(oarg < oargs && oargs <= size);)
	int_t arg = size + oarg - oargs;
	return a->vm.at(t[arg]);
}

void blt_ctx::args_bodies(bdd_handles& hs, size_t len) {
	if (!a) return;
	if (len == 0) len = a->bltngvars.size();
	hs = bdd_handles(len, htrue);
	for (auto p : a->varbodies)
		if (has(a->bltngvars, p.first)) {
			for (size_t n = 0; n != len; ++n)
				if (arg(n) == p.first)
					hs[n] =	hs[n] && p.second->rlast;
		}
}

void builtins::run(blt_ctx& c, bool ishead) {
	blt_cache_key k;
	if (!ishead && !c.t.renew) {
		k = c.key();
		auto cit = cache.find(c.key());
		if (cit != cache.end()) {
			if (cit->second.first) c.outs = cit->second.second;
			return;
		}
	}
	auto it = find(c.t.idbltin);
	if (it == end()) return;
	if ((ishead && !it->second.has_head) ||
		(!ishead && !it->second.has_body)) o::err()
			<< "builtin head/body error" << std::endl;
	builtin& b = ishead ? it->second.head : it->second.body;
	c.args = b.args, c.nargs = b.nargs, c.oargs = b.oargs;
	b.run(c);
	if (!ishead && !c.t.forget)
		cache.emplace(k, blt_cache_value(true, c.outs));
}

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
	const bool H = true, B = false;
	set<string> syms{ "alpha","alnum","digit","space","printable" };
	for (auto sym : syms) dict.get_bltin(sym);

	bltins.add(H, dict.get_bltin(get_lexeme("halt")), "halt",  0, 0, [this](blt_ctx& c) {
		c.tbls->halt  = true; });
	bltins.add(H, dict.get_bltin(get_lexeme("error")), "error", 0, 0, [this](blt_ctx& c) {
		c.tbls->error = true; });
	bltins.add(H, dict.get_bltin(get_lexeme("false")), "false", 0, 0, [this](blt_ctx& c) {
		c.tbls->unsat = true; });
	bltins.add(H, dict.get_bltin(get_lexeme("forget")), "forget", 0, 0, [this](blt_ctx& c) {
		c.tbls->bltins.forget(c); });
	bltins.add(B, dict.get_bltin(get_lexeme("rnd")), "rnd", 3, 1, [this](blt_ctx& c) {
		int_t arg0 = c.arg_as_int(0);
		int_t arg1 = c.arg_as_int(1);
		if (arg0 > arg1) swap(arg0, arg1);
		random_device rd;
		mt19937 gen(rd());
		uniform_int_distribution<> distr(arg0, arg1);
		int_t rnd = distr(gen);
		DBG(o::dbg()<<"rnd("<<arg0<<" "<<arg1<<" "<<rnd<<endl;)
		c.out(c.tbls->from_sym(c.outvarpos(0), c.a->varslen, mknum(rnd)));
	});
	
	bltins.add(B, dict.get_bltin(get_lexeme("count")), "count", -1, 1, [this](blt_ctx& c) {
		spbdd_handle x = bdd_and_many(*c.hs);
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
		x = bdd_permute_ex(x,ex,perm);
		size_t cnt2 = satcount(x, (c.tbls->bits) * (c.a->varslen-varsout));
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
			// TODO workaround to get constants
			if (c.t[0] >= 0 || c.t[1] >= 0) {
				for (size_t i = 0; i < c.t.size(); ++i) {
					if (c.t[i] >= 0 && i % 2 == 0)
						const0 = const0 && ::from_bit(arg0_w-(i>>1) , c.t[i] == 1);
					else if (c.t[i] >= 0 && i % 2 == 1)
						const1 = const1 && ::from_bit(arg0_w+arg1_w-(i>>1)-1, c.t[i] == 1);
				}
			}

			//TODO debug why hs[1] is not created
			//TODO get output var, ?x or ?y
			i = 0;
			bool dual = false;
			for (auto x : *c.hs) {
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
			}

			spbdd_handle s0 = const0;
			if (const0 == htrue)
				s0 = c.tbls->perm_bit_reverse_bt(arg0, arg0_w, 0);
			spbdd_handle s1 = const1;
			if (const1 == htrue)
				s1 = c.tbls->perm_bit_reverse_bt(arg1, arg1_w, arg0_w);
			assert( bdd_root(s0) < bdd_root(s1) && "LEQ_handler: wrong assumed term/argument ordering");

			spbdd_handle leq = htrue;
			if (!dual)
				leq = bdd_leq( s0, s1, arg0_w, arg1_w);
			else
				COUT << "LEQ_handler: DUAL operator GEQ is work in progress\n";
			//TODO: arg0_w when ?x in head, arg1_w when ?y in head
			spbdd_handle s2 = c.tbls->perm_bit_reverse_bt(leq, arg0_w, 0);
			c.out(s2);
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
			print_to_delimited(ir.to_raw_term(c.g), c.tbls->error, to, delim) << (ln ? "\n" : "")
				#ifdef __EMSCRIPTEN__
				<< std::flush
				#endif
				;		
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
#else // TODO embed a JS engine if not in browser?
	bltins.add(H, dict.get_bltin(get_lexeme("js_eval")), "js_eval", -1, 0, h = [](blt_ctx) {
		o::err() << "js_eval is available only in a browser environment"
			" (ignoring)." << endl;
	});
	bltins.add(B, dict.get_bltin(get_lexeme("js_eval")), "js_eval", -1, 0, h);
#endif
	return *this;
}
