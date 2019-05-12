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
#ifndef __TOKEN_H__
#define __TOKEN_H__
#include "defs.h"

struct token {
	lexeme e;
	enum etype {
		SYM,
		NUM, CHR, VAR, OPENP, CLOSEP,
		ALT, STR, REL, NEG, POS,
		TERM, HEAD, BODY, DOT, DELIM,
		NOT, AND, OR, GOAL, TREE,
		FACT, RULE, PROD, DIR, OPENC,
		CLOSEC, PROG, PROGS
	} type;
	token(etype type, lexeme e) : e(e), type(type) {};
	bool operator<(const token& t) const {
		return e[0] == t.e[0]
			? e[1] == t.e[1]
				? type > t.type
				: e[1] > t.e[1]
			: e[0] < t.e[0];
	};
	static std::vector<std::wstring> names;
	static std::set<token> tokens;
	static void add(etype type, lexeme e) { tokens.emplace(type, e); };
	static void clear() { tokens.clear(); }
	static std::wstring name(etype type) { return names[type]; };
};
#endif
