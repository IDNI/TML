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
#ifndef __INPUT_H__
#define __INPUT_H__

#include "defs.h"
#include <vector>
#include <array>
#include <iostream>
#include <sys/stat.h>

namespace input {
	extern cws_range source;
}

bool operator==(const lexeme& x, const lexeme& y);

struct elem {
	enum etype {
		SYM, NUM, CHR, VAR, OPENP, CLOSEP, ALT, STR, EQ, NEQ, LEQ, GT
	} type;
	int_t num = 0;
	lexeme e;
	wchar_t ch;
	elem() {}
	elem(int_t num) : type(NUM), num(num) {}
	elem(wchar_t ch) : type(CHR), ch(ch) {}
	elem(etype type, lexeme e) : type(type), e(e) {
		DBG(assert(type!=NUM&&type!=CHR&&(type!=SYM||(e[0]&&e[1])));)
	}
	bool is_paren() const { return type == OPENP || type == CLOSEP; }
	bool parse(const lexemes& l, size_t& pos);
	bool operator<(const elem& t) const {
		if (type != t.type) return type < t.type;
		if (type == NUM) return num < t.num;
		if (type == CHR) return ch < t.ch;
		if (e[1]-e[0] != t.e[1]-t.e[0]) return e[1]-e[0]<t.e[1]-t.e[0];
		return wcsncmp(e[0], t.e[0], e[1]-e[0]) < 0;
	}
	bool operator==(const elem& t) const {
		if (type != t.type) return false;
		if (type == NUM) return num == t.num;
		if (type == CHR) return ch == t.ch;
		return e == t.e;
	}
	bool operator!=(const elem& t) const { return !(*this == t); }
};

struct raw_term {
	bool neg = false, iseq = false, isleq = false;
	std::vector<elem> e;
	ints arity;
	bool parse(const lexemes& l, size_t& pos);
	void calc_arity();
	void insert_parens(lexeme op, lexeme cl);
	void clear() { e.clear(), arity.clear(); }
	bool operator==(const raw_term& t) const {
		return neg == t.neg && e == t.e && arity == t.arity &&
			iseq == t.iseq && isleq == t.isleq;
		//return neg == t.neg && e == t.e && arity == t.arity;
	}
};

struct directive {
	elem rel;
	lexeme arg;
	raw_term t;
	int_t n;
	enum etype { STR, FNAME, CMDLINE, STDIN, STDOUT, TREE, TRACE, BWD }type;
	bool parse(const lexemes& l, size_t& pos);
};

struct production {
//	bool start = false;
//	raw_term t;
	std::vector<elem> p;
	bool parse(const lexemes& l, size_t& pos);
	bool operator<(const production& t) const { return p < t.p; }
};

bool operator==(const std::vector<raw_term>& x, const std::vector<raw_term>& y);

struct raw_rule {
	std::vector<raw_term> h;
	std::vector<std::vector<raw_term>> b;

	enum etype { NONE, GOAL, TREE };
	etype type = NONE;
	bool parse(const lexemes& l, size_t& pos);
	void clear() { h.clear(), b.clear(), type = NONE; }
	raw_rule(){}
	raw_rule(etype type, const raw_term& t) : h({t}), type(type) {}
	raw_rule(const raw_term& t) : raw_rule(NONE, t) {}
	raw_rule(const raw_term& h, const raw_term& b) : h({h}), b({{b}}) {}
	raw_rule(const raw_term& h, const std::vector<raw_term>& _b) : h({h}) {
		if (!_b.empty()) b = {_b};
	}
	static raw_rule getdel(const raw_term& t) {
		raw_rule r(t, t);
		return r.h[0].neg = true, r;
	}
	bool operator==(const raw_rule& r) const {
		return h == r.h && b == r.b;
	}
	bool operator!=(const raw_rule& r) const { return !(*this == r); }
};

struct raw_prog {
	std::vector<directive> d;
	std::vector<production> g;
	std::vector<raw_rule> r;
//	int_t delrel = -1;
	bool parse(const lexemes& l, size_t& pos);
};

struct raw_progs {
	std::vector<raw_prog> p;
	raw_progs(FILE*);
	raw_progs(const std::wstring& s);
};

void parse_error(cws o, std::wstring e);
void parse_error(cws o, std::wstring e, cws s);
void parse_error(cws o, std::wstring e, lexeme l);
void parse_error(cws o, std::wstring e, std::wstring s);
void parse_error(cws o, std::wstring e, cws s, size_t len);
void parse_error(std::wstring e, lexeme l);
void parse_error(std::wstring e, std::wstring s);
std::wostream& operator<<(std::wostream& os, const directive& d);
std::wostream& operator<<(std::wostream& os, const elem& e);
std::wostream& operator<<(std::wostream& os, const raw_term& t);
std::wostream& operator<<(std::wostream& os, const raw_rule& r);
std::wostream& operator<<(std::wostream& os, const raw_prog& p);
std::wostream& operator<<(std::wostream& os, const raw_progs& p);
std::wostream& operator<<(std::wostream& os, const lexeme& l);
std::wostream& operator<<(std::wostream& os, const production& p);
lexeme lex(pcws s);
lexemes prog_lex(cws s);
std::wstring file_read(std::wstring fname);
std::wstring file_read_text(FILE *f);
std::wstring file_read_text(std::wstring fname);
off_t fsize(cws s, size_t len);
bool operator==(const lexeme& l, cws s);
bool operator<(const raw_term& x, const raw_term& y);
bool operator<(const raw_rule& x, const raw_rule& y);
void parser_test();
#define lexeme2str(l) wstring((l)[0], (l)[1]-(l)[0])

struct parse_error_exception : public virtual std::runtime_error {
	using std::runtime_error::runtime_error;
};

#endif
