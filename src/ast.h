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
#ifndef __AST_H__
#define __AST_H__
#include <map>
#include "defs.h"

struct ast {
	// neq: is it ok to just drop NEQ in, is any order / value hardcoded anywhere?
	enum type {
		SYM, NUM, CHR, VAR, OPENP, CLOSEP, ALT, STR, EQ, NEQ, REL, NEG, POS,
		TERM, HEAD, BODY, DOT, DELIM, NOT, AND, OR, GOAL, TREE, FACT,
		RULE, PROD, DIR, DIRNAME, OPENC, CLOSEC, PROG, PROGS
	} t;
	cws_range r;
	static std::map<type, std::wstring> names;
	static std::set<ast> nodes;
	static cws_range source;
	static std::wstring name(ast n) { return names[n.t]; };
	static void add(type t, cws_range r) { nodes.emplace(t, r); };
	static void clear() { nodes.clear(); }
	ast(type t, cws_range r) : t(t), r(r) {};
	bool operator<(const ast& n) const {
		return r[0] == n.r[0]
			? r[1] == n.r[1]
				? t > n.t
				: r[1] > n.r[1]
			: r[0] < n.r[0];
	};
};
#endif
