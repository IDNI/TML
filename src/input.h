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

#include <vector>
#include <set>
#include <array>
#include <cstring>
#include <iostream>
#include <memory>
#include <sys/stat.h>

#include "defs.h"
#include "dict.h"
#include "memory_map.h"

class archive;

struct input {
	friend class archive;
	enum type { STDIN, FILE, STRING } type_;
	bool newseq = false;
	size_t offset = 0;
	size_t pos = 0;
	lexemes l = {};
	input(bool ns = false) : type_(STDIN), newseq(ns), beg_(0), data_(0),
		size_(load_stdin()) {
		//COUT << "created stdin input *: " << beg_ << std::endl;
	}
	input(void* s, size_t sz, bool ns = false) : type_(STRING), newseq(ns),
		beg_((ccs) s), data_(beg_), size_(sz), allocated_(false) {
		//COUT << "created pointer input: " << beg_ << std::endl;
	}
	input(ccs s, bool ns = false) : type_(STRING), newseq(ns),
		beg_(strdup(s)),data_(beg_),size_(strlen(beg_)),allocated_(true)
	{	//COUT << "created string input *: " << s << std::endl;
	}
	input(std::string f, bool ns = false); // FILE
	~input();
	lexeme lex(pccs s);
	lexemes& prog_lex();
	// is l in this input? if true set l's offset into lr
	bool lexeme_pos(const size_t& beg, const lexeme& l, lexeme_range& lr) {
		if ((l[0] >= beg_ && l[0] < beg_ + size_)
		 || (l[1] >= beg_ && l[1] < beg_ + size_))
			return	lr[0] = l[0] - beg_ + beg,
				lr[1] = l[1] - beg_ + beg, true;
		return false;
	}
	input* next() { return next_.get(); }
	void set_next(std::unique_ptr<input> ni) { next_ = std::move(ni); }
	ccs begin() { return beg_; }
	ccs data() { return data_; }
	size_t size() { return size_; }
	void set_offset(size_t o) { offset = o; }
	static int_t get_int_t(ccs from, ccs to);
	void count_pos(ccs o, long& l, long& ch);
	void parse_error(ccs offset, const char* err) {
		return parse_error(offset, err, offset);
	}
	void parse_error(ccs offset, const char* err, ccs close_to);
	void parse_error(ccs offset, const char* err, lexeme close_to);

	static std::string file_read(std::string fname);
	static std::string file_read_text(::FILE *f);
	static std::string file_read_text(std::string fname);
	static off_t fsize(const char *fname);
	static off_t fsize(ccs s, size_t len);
private:
	memory_map mm_;
	ccs beg_  = 0;
	ccs data_ = 0;
	size_t size_ = 0;
	bool allocated_ = false;
	int fd_ = -1;
	std::unique_ptr<input> next_ = 0;
	size_t load_stdin() {
		ostringstream_t ss; ss << CIN.rdbuf();
		beg_ = (ccs) strdup((ws2s(ss.str())).c_str()),
		data_ = beg_,
		allocated_ = true;
		return ss.str().size();
	}
};

class inputs { 
	friend class archive;
	std::unique_ptr<input> first_ = 0;
	struct input *last_ = 0;
	size_t size_ = 0;
public:
	void add(std::unique_ptr<input> in) {
		//COUT << "inputs size: " << size_ << " adding input: " << in.get() << " last: " << last_<< std::endl;
		input *inp = in.get();
		if (last_) last_->set_next(std::move(in));
		else first_ = std::move(in);
		last_ = inp;
		size_++;
	}
	input* add_stdin() {
		std::unique_ptr<input> in = std::make_unique<input>();
		input* ret = in.get();
		add(std::move(in));
		return ret;
	}
	input* add_file(std::string filename) {
		//COUT << "adding file input: " << filename << std::endl;
		std::unique_ptr<input> in = std::make_unique<input>(filename);
		input* ret = in.get();
		add(std::move(in));
		//COUT << "inputs size: " << size() << " this: " << this <<std::endl;
		return ret;
	}
	input* add_string(const string_t& str) {
		//COUT << "adding string input: " << to_string(str) << std::endl;
		std::unique_ptr<input> in =std::make_unique<input>(str.c_str());
		input* ret = in.get();
		add(std::move(in));
		//COUT << "inputs size: " << size() << " this: " << this <<std::endl;
		return ret;
	}
	input* add_string(const std::string& str) {
		//COUT << "adding string input: " << str << std::endl;
		std::unique_ptr<input> in = std::make_unique<input>(
			to_string_t(str).c_str());
		input* ret = in.get();
		add(std::move(in));
		//COUT << "inputs size: " << size() << " this: " << this <<std::endl;
		return ret;
	}
	input* first() const { return first_.get(); }
	input* last() const { return last_; }
	size_t size() const { return size_; }
	//is l in inputs? then point *in to the input and set l's offset into lr
	bool lexeme_pos(size_t& beg, const lexeme& l, input** in,
		lexeme_range& lr)
	{
		input* it = first_.get();
		while (it) {
			beg += sizeof(size_t) + 1;
			if (it->lexeme_pos(beg, l, lr)) return *in = it, true;
			beg += it->size() + 1;
			it = it->next();
		}
		return *in = 0, false;
	}
};

struct raw_form_tree;
typedef std::shared_ptr<raw_form_tree> sprawformtree;

struct raw_prog;

bool operator==(const lexeme& x, const lexeme& y);

static const std::set<std::string> str_bltins =
	{ "alpha", "alnum", "digit", "space", "printable", "count",
		"rnd", "print", "lprint", "halt", "fail",
		"bw_and", "bw_or", "bw_xor", "bw_not", "pw_add", "pw_mult"};

struct elem {
	enum etype {
		NONE, SYM, NUM, CHR, VAR, OPENP, CLOSEP, ALT, STR, EQ, NEQ, LEQ, GT, LT,
		GEQ, BLTIN, NOT, AND, OR, FORALL, EXISTS, UNIQUE, IMPLIES, COIMPLIES, ARITH
	} type;
	t_arith_op arith_op = NOP;
	int_t num = 0;
	lexeme e{ 0, 0 };
	char32_t ch;
	elem() {}
	elem(int_t num) : type(NUM), num(num) {}
	elem(char32_t ch) : type(CHR), ch(ch) {}
	elem(etype type, lexeme e) : type(type), e(e) {
		DBG(assert(type!=NUM&&type!=CHR&&(type!=SYM||(e[0]&&e[1])));)
	}
	etype peek(input* in);
	bool is_paren() const { return type == OPENP || type == CLOSEP; }
	bool parse(input* in);
	bool operator<(const elem& t) const {
		if (type != t.type) return type < t.type;
		if (type == NUM) return num < t.num;
		if (type == CHR) return ch < t.ch;
		if (e[1]-e[0] != t.e[1]-t.e[0]) return e[1]-e[0]<t.e[1]-t.e[0];
		return strncmp(e[0], t.e[0], e[1]-e[0]) < 0;
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
	enum rtextype { REL, EQ, LEQ, BLTIN, ARITH, CONSTRAINT } extype = raw_term::REL;

	//XXX we can add FORM1, FORM2 etc to rtextype
	// and replace t_arith_op by a form (once we do parse for compound arithmetic formulas)
	t_arith_op arith_op = NOP;

	std::vector<elem> e;
	ints arity;
	bool parse(input* in, const raw_prog& prog, bool is_form = false,
		rtextype pref_type = raw_term::REL);
	void calc_arity(input* in);
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
	bool parse(input* in, const raw_prog& prog);
};

struct production {
//	bool start = false;
//	raw_term t;
	std::vector<elem> p;
	std::vector<raw_term> c{};   // constraints after production
	bool parse(input* in, const raw_prog& prog);
	bool operator<(const production& t) const { return p < t.p && c < t.c; }
};

bool operator==(const std::vector<raw_term>& x, const std::vector<raw_term>& y);

struct raw_rule {
	std::vector<raw_term> h;
	std::vector<std::vector<raw_term>> b;
	sprawformtree prft;

	enum etype { NONE, GOAL, TREE };
	etype type = NONE;
	bool parse(input* in, const raw_prog& prog);
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
	bool isfod = false;
	bool parse(input* in);
};

struct raw_form_tree {
	elem::etype type;
	raw_term *rt; // elem::NONE is used to identify it
	elem * el;

	raw_form_tree *l;
	raw_form_tree *r;

	raw_form_tree (elem::etype _type, raw_term* _rt = NULL, elem *_el =NULL,
		raw_form_tree *_l = NULL, raw_form_tree *_r = NULL)
	{
		type = _type;
		if(_rt) rt = new raw_term(*_rt);
		else rt = NULL;
		if(_el) el = new elem(*_el);
		else el = NULL;
		l = _l, r = _r;
	}
	~raw_form_tree() {
		if (l)  delete l,  l  = NULL;
		if (r)  delete r,  r  = NULL;
		if (rt) delete rt, rt = NULL;
		if (el) delete el, el = NULL;
	}
	void printTree(int level =0 );
};
struct raw_sof {
	const raw_prog& prog;
	raw_sof(const raw_prog& prog) :prog(prog) {}
private:
	bool parseform(input* in, raw_form_tree *&root, int precd= 0);
	bool parsematrix(input* in, raw_form_tree *&root);
public:
	bool parse(input* in, raw_form_tree *&root);

};

struct raw_prog {
	std::vector<directive> d;
	std::vector<production> g;
	std::vector<raw_rule> r;
	std::set<lexeme, lexcmp> builtins;
//	int_t delrel = -1;
	bool parse(input* in);
};

struct raw_progs {
	std::vector<raw_prog> p;
	raw_progs();
	void parse(input* in, dict_t& dict, bool newseq = true);
};

void throw_runtime_error(std::string err, std::string details = "");

void parse_error(const char* o, const char* e, ccs s);
void parse_error(const char* o, const char* e, lexeme l);
void parse_error(ccs o, const char* e, std::string s);
void parse_error(ccs o, const char* e);
void parse_error(const char* e, lexeme l);
void parse_error(const char* e);

template <typename T>
std::basic_ostream<T>& operator<<(std::basic_ostream<T>& os, const directive& d);
template <typename T>
std::basic_ostream<T>& operator<<(std::basic_ostream<T>& os, const elem& e);
template <typename T>
std::basic_ostream<T>& operator<<(std::basic_ostream<T>& os, const raw_term& t);
template <typename T>
std::basic_ostream<T>& operator<<(std::basic_ostream<T>& os, const std::pair<raw_term, std::string>& p);
template <typename T>
std::basic_ostream<T>& operator<<(std::basic_ostream<T>& os, const raw_rule& r);
template <typename T>
std::basic_ostream<T>& operator<<(std::basic_ostream<T>& os, const raw_prog& p);
template <typename T>
std::basic_ostream<T>& operator<<(std::basic_ostream<T>& os, const raw_progs& p);
template <typename T>
std::basic_ostream<T>& operator<<(std::basic_ostream<T>& os, const production& p);
std::basic_ostream<char>& operator<<(std::basic_ostream<char>& os, const lexeme& l);
std::basic_ostream<wchar_t>& operator<<(std::basic_ostream<wchar_t>& os, const lexeme& l);

bool operator==(const lexeme& l, std::string s);
bool operator==(const lexeme& l, const char* s);
bool operator<(const raw_term& x, const raw_term& y);
bool operator<(const raw_rule& x, const raw_rule& y);
void parser_test();

#define lexeme2str(l) string_t((l)[0], (l)[1]-(l)[0])

#endif
