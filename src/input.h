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
#include "types.h"
#include "dict.h"
#include <vector>
#include <set>
#include <array>
#include <iostream>
#include <memory>
#include <sys/stat.h>

namespace input {
	extern cws_range source;
}
struct raw_form_tree;
typedef std::shared_ptr<raw_form_tree> sprawformtree;

struct raw_prog;

bool operator==(const lexeme& x, const lexeme& y);

static const std::set<std::wstring> str_bltins = {
	L"count", L"rnd", L"print", L"lprint", L"halt", L"fail",
	L"bw_and", L"bw_or", L"bw_xor", L"bw_not", L"pw_add", L"pw_mult"
};

struct elem {
	enum etype {
		NONE, SYM, NUM, CHR, VAR, OPENP, CLOSEP, ALT, STR, EQ, NEQ, LEQ, GT, LT,
		GEQ, BLTIN, NOT, AND, OR, FORALL, EXISTS, UNIQUE, IMPLIES, COIMPLIES,
		ARITH, ARGTYP
	} type;
	t_arith_op arith_op = NOP;
	int_t num = 0;
	lexeme e;
	wchar_t ch;
	// D: this is temp/hack only to support decompress out to dump more info
	// TODO: remove it or move to out_term/out_elem instead
	arg_type bitype{base_type::NONE, size_t(-1)};
	elem() {}
	elem(int_t num) : type(NUM), num(num) {}
	elem(wchar_t ch) : type(CHR), ch(ch) {}
	elem(etype type, lexeme e) : type(type), e(e) {
		DBG(assert(type!=NUM&&type!=CHR&&(type!=SYM||(e[0]&&e[1])));)
	}
	// this is just temp, this should be the base ctor otherwise
	elem(int_t num, arg_type bitype_) : elem(num) { bitype = bitype_; }
	elem(wchar_t ch, arg_type bitype_) : elem(ch) { bitype = bitype_; }
	elem(etype type, lexeme e, arg_type bitype_):elem(type, e){bitype=bitype_;}

	etype peek(const lexemes& l, size_t& pos);
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
	// TODO: enum 'is...' stuff
	bool neg = false;
	//bool iseq = false, isleq = false, islt = false, isbltin = false;
	enum rtextype { REL, EQ, LEQ, BLTIN, ARITH } extype = raw_term::REL;
	t_arith_op arith_op = NOP;
	std::vector<elem> e;
	ints arity;
	size_t nargs = 0; // total count of args (useful for types handling later).
	bool parse(const lexemes& l, size_t& pos, const raw_prog& prog);
	void calc_arity();
	void insert_parens(lexeme op, lexeme cl);
	void clear() { e.clear(), arity.clear(); }
	bool operator==(const raw_term& t) const {
		return neg == t.neg && e == t.e && arity == t.arity &&
			extype == t.extype;
			//iseq == t.iseq && isleq == t.isleq && islt == t.islt;
		//return neg == t.neg && e == t.e && arity == t.arity;
	}
};

struct directive {
	elem rel;
	lexeme arg;
	raw_term t;
	int_t n;
	enum etype { STR, FNAME, CMDLINE, STDIN, STDOUT, TREE, TRACE, BWD }type;
	bool parse(const lexemes& l, size_t& pos, const raw_prog& prog);
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
	sprawformtree prft;

	enum etype { NONE, GOAL, TREE };
	etype type = NONE;
	bool parse(const lexemes& l, size_t& pos, const raw_prog& prog);
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

struct raw_prefix {
		elem qtype;
		elem ident;
		bool isfod =false;

	bool parse(const lexemes& l, size_t& pos);
};


struct raw_form_tree {
	elem::etype type;
	raw_term *rt; // elem::NONE is used to identify it
	elem * el;

	raw_form_tree *l;
	raw_form_tree *r;



	raw_form_tree (elem::etype _type, raw_term* _rt = NULL, elem *_el= NULL, raw_form_tree *_l= NULL, raw_form_tree *_r= NULL ) {

		type = _type;
		if(_rt)
			rt = new raw_term(*_rt);
		else rt = NULL;

		if(_el)
			el = new elem(*_el);
		else el = NULL;

		l = _l;
		r = _r;
	}
	~raw_form_tree() {
		if( l ) delete l, l= NULL;
		if (r ) delete r, r= NULL;
		if (rt) delete rt,rt= NULL;
		if (el) delete el, el= NULL;
	}
	void printTree(int level =0 );
};
struct raw_sof {
	const raw_prog& prog;
	raw_sof(const raw_prog& prog) :prog(prog) {}

	private:
	bool parseform(const lexemes& l, size_t& pos, raw_form_tree *&root, int precd= 0);
	bool parsematrix(const lexemes& l, size_t& pos, raw_form_tree *&root);

	public:
	bool parse(const lexemes& l, size_t& pos, raw_form_tree *&root);

};

struct raw_prog {
	std::vector<directive> d;
	std::vector<production> g;
	std::vector<raw_rule> r;
	std::set<lexeme, lexcmp> builtins;
//	int_t delrel = -1;
	bool parse(const lexemes& l, size_t& pos);
};

struct raw_progs {
	std::vector<raw_prog> p;
	raw_progs();
	void parse(const std::wstring& s, dict_t& dict, bool newseq = true);
};

void warning(cws o, std::wstring e);
void warning(cws o, std::wstring e, cws s);
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
std::wostream& operator<<(std::wostream& os,
	const std::pair<raw_term, std::wstring>& p);
std::wostream& operator<<(std::wostream& os, const raw_rule& r);
std::wostream& operator<<(std::wostream& os, const raw_prog& p);
std::wostream& operator<<(std::wostream& os, const raw_progs& p);
std::wostream& operator<<(std::wostream& os, const lexeme& l);
std::wostream& operator<<(std::wostream& os, const production& p);
lexeme lex(pcws s);
lexemes prog_lex(cws s);
int_t get_int_t(cws from, cws to);
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
