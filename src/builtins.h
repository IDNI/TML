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
#ifndef __BUILTINS_H__
#define __BUILTINS_H__
#include <functional>
#include "dict.h"
#include "input.h"

typedef std::tuple<alt*, term, bdd_handles> blt_cache_key;
typedef std::pair<bool, bdd_handles> blt_cache_value;
typedef std::map<blt_cache_key, blt_cache_value> blt_cache;

struct blt_ctx {
	term t;              // builtin term
	term g;              // grounded term
	bdd_handles outs = {}; // handles of compressed outputs
	int_t   args = 0;    // number of args (-1 = can vary)
	size_t oargs = 0;    // number of output args
	size_t nargs = 0;    // number of args to keep ungrounded
	alt*       a = 0;    // alt if body builtin
	dict_t* dict = 0;
	bdd_handles* hs = 0;
	// builtin context for head term
	blt_ctx(term t) : t(t), g(t), args(t.size()), oargs(0) {}
	// builtin context for body term
	blt_ctx(term t, alt* a) : t(t), g(t), a(a) {}
	inline blt_cache_key key() const { return blt_cache_key{ a, g, outs }; }
	size_t varpos(size_t arg) const;
	inline int_t arg(size_t arg) const { return g[arg]; }
#ifndef TYPE_RESOLUTION
	inline int_t arg_as_int(size_t arg) const { return int_t(g[arg] >> 2); }
#else
	inline int_t arg_as_int(size_t arg) const { return int_t(g[arg]); }
#endif
	int_t outvarpos(size_t oarg = 0) const;
	void args_bodies(bdd_handles& hs, size_t len = 0);
	void out(spbdd_handle x) { outs.push_back(x); }
};

typedef std::function<void(blt_ctx& t)> blt_handler;

// structure containing number of builtin's arguments and its handler
struct builtin {
	int_t  args;   // number of arguments, -1 = can vary
	int_t oargs;   // number of out (return) arguments (first outarg starts at pos args - oargs)
	int_t nargs;   // number of arguments to not decompress (first such starts at pos = args - nargs - oargs)
	blt_handler h; // builtin's handler
	// return length of the builtin (number of its args);
	int_t length(const term& bt) const { return args==-1 ? bt.size() : args; }
	// collect vars: input vars to ground, to keep ungrounded and output vars
	void getvars(const term& bt, std::set<int_t>& invars,
		std::set<int_t>& ngvars, std::set<int_t>& outvars) const
	{
		//nargs == -1 encodes:
		// - builtin has variable number of args, single output
		// - last one is output
		// - no input requires "grounding"
		if (nargs != -1) {
			int_t l = length(bt), op = l - oargs, np = op - nargs;
			for (int_t n = 0; n != l; ++n) if (bt[n] < 0) {
				if (n < np) invars.insert(bt[n]);
				else if (n < op) ngvars.insert(bt[n]);
				else outvars.insert(bt[n]);
			}
		} else {
			int_t s = length(bt);
			for (int_t n = 0; n != s-1; ++n)
				if (bt[n] < 0) ngvars.insert(bt[n]);
			outvars.insert(bt[s-1]);
		}
	}
	// call the builtin's handler with the a context
	void run(blt_ctx& c) { if (h) h(c); }
};

// head and body builtins with the same name (=> id as well) are contained in
// builtins_pair. this is used in builtins container defined bellow
struct builtins_pair {
	bool has_head = false;
	bool has_body = false;
	builtin head;
	builtin body;	
};

// container for builtins represented by a map
// it's key is builtin's id and its value is a builtins_pair (head - body) 
struct builtins : std::map<int_t, builtins_pair> {
	dict_t* dict = 0;
	blt_cache cache; // builtins' cache for calls
	std::vector<sig> sigs;
	bool reset(dict_t& d) { return clear(), dict = &d, true; }
	// clear cache (TODO: add possibility to clear cache by builtin id)
	void forget(blt_ctx&) { cache.clear(); }
	// add builtin symbol (for non functions like digit, alnum...)
	bool add(const std::string& s) { return dict->get_bltin(s), true; }
	// add builtin. ishead to flag head or body builtin
	// @param ishead true if head builtin, false for body builtin
	// @param name   identifier of the builtin
	// @param args   number of arguments (-1 = can vary)
	// @param oargs  number of output arguments
	// @param h      building handler
	// @param nargs  number of arguments to keep ungrounded
	bool add(bool ishead, std::string name, int_t args, int_t oargs,
		blt_handler h, int_t nargs = 0)
	{
		int_t id = dict->get_bltin(name);
		auto it = find(id);
		if (it == end()) it = emplace(id, builtins_pair{}).first;
		builtins_pair& bp = it->second;
		if (ishead) 
		bp.has_head = true, bp.head = builtin{ args, oargs, nargs, h};
		else bp.has_body = true, bp.body = builtin{ args, oargs, nargs, h};
		return true;
	}
	void run_head(blt_ctx& c) { run(c, true);  }
	void run_body(blt_ctx& c) { run(c, false); }
	void run(blt_ctx& c, bool ishead = true);
	bool is_builtin(int_t id) const { return find(id) != end(); }
};

#endif
