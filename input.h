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
#include "defs.h"
#include <vector>
#include <array>
#include <iostream>
#include <sys/stat.h>

struct directive {
	lexeme rel, arg;
	bool fname;
	bool parse(const lexemes& l, size_t& pos);
};

struct elem {
	enum etype { SYM, NUM, CHR, VAR, OPENP, CLOSEP } type;
	int_t num;
	lexeme e;
	bool parse(const lexemes& l, size_t& pos);
};

struct raw_term {
	bool neg;
	std::vector<elem> e;
	ints arity;
	bool parse(const lexemes& l, size_t& pos);
	void clear() { e.clear(), arity.clear(); }
};

struct production {
	std::vector<elem> p;
	bool parse(const lexemes& l, size_t& pos);
};

struct raw_rule {
	std::vector<raw_term> b;
	bool goal, pgoal = false;
	bool parse(const lexemes& l, size_t& pos);
};

struct raw_prog {
	std::vector<directive> d;
	std::vector<production> g;
	std::vector<raw_rule> r;
	bool parse(const lexemes& l, size_t& pos);
};

struct raw_progs {
	std::vector<raw_prog> p;
	raw_progs(FILE*);
	raw_progs(const std::wstring& s);
};

std::wostream& operator<<(std::wostream& os, const directive& d);
std::wostream& operator<<(std::wostream& os, const elem& e);
std::wostream& operator<<(std::wostream& os, const raw_term& t);
std::wostream& operator<<(std::wostream& os, const raw_rule& r);
std::wostream& operator<<(std::wostream& os, const raw_prog& p);
std::wostream& operator<<(std::wostream& os, const lexeme& l);
lexeme lex(pcws s);
lexemes prog_lex(cws s);
std::wstring file_read(std::wstring fname);
std::wstring file_read_text(FILE *f);
std::wstring file_read_text(std::wstring fname);
off_t fsize(cws s, size_t len);
void parser_test();
