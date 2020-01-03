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
#ifndef __DRIVER_H__
#define __DRIVER_H__
#include <map>
#ifdef __EMSCRIPTEN__
#include <emscripten.h>
#include <emscripten/bind.h>
#include <emscripten/val.h>
#endif
#include "tables.h"
#include "input.h"
#include "dict.h"
#include "output.h"
#include "options.h"

#define mkchr(x) ((((int_t)x)<<2)|1)
#define mknum(x) ((((int_t)x)<<2)|2)

typedef enum prolog_dialect { XSB, SWIPL } prolog_dialect;

struct prog_data {
	strs_t strs;
//	std::unordered_map<int_t, term> strtrees;
//	std::vector<term> out;
//	matpairs r;
//	matrix goals, tgoals;
	bool bwd = false;
};

class driver {
	friend struct flat_rules;
	friend struct pattern;
	friend std::ostream& operator<<(std::ostream& os, const driver& d);
	friend std::istream& operator>>(std::istream& is, driver& d);
//	dict_t dict;
	std::set<int_t> builtin_rels;//, builtin_symbdds;

	int_t nums = 0, chars = 0, syms = 0;
//	bool mult = false;

	std::set<lexeme, lexcmp> strs_extra, rels;
	lexeme get_var_lexeme(int_t i);
	lexeme get_new_var();
	lexeme get_lexeme(const std::wstring& s);
	lexeme get_new_rel();
//	std::function<int_t(void)> *fget_new_rel;
//	lexeme get_num_lexeme(int_t i);
//	lexeme get_char_lexeme(wchar_t i);
//	lexeme get_demand_lexeme(elem e, const ints& i, const bools& b);
	void refresh_vars(raw_term& t, size_t& v, std::map<elem, elem>& m);
	void refresh_vars(raw_prog& p);
	raw_rule refresh_vars(raw_term h, std::vector<std::vector<raw_term>> b);
	std::set<raw_rule> refresh_vars(raw_rule& r);
	std::set<raw_term> get_queries(const raw_prog& p);

	std::wstring directive_load(const directive& d);
	void directives_load(raw_prog& p, lexeme& trel);
	void transform(raw_progs& rp, size_t n, const strs_t& strtrees);
//	std::set<raw_rule> transform_ms(const std::set<raw_rule>& p,
//		const std::set<raw_term>& qs);
//	raw_prog transform_sdt(const raw_prog& p);
	void transform_bin(raw_prog& p);
	void transform_len(raw_term& r, const strs_t& s);
//	raw_prog transform_bwd(raw_prog& p);
	raw_term get_try_pred(const raw_term& x);
	void transform_bwd(const raw_term& h, const std::vector<raw_term>& b,
		std::set<raw_rule>& s);
	void transform_bwd(raw_prog& p);
	void transform_proofs(raw_prog& r, const lexeme& rel);
//	void transform_string(const std::wstring&, raw_prog&, int_t);
	void transform_grammar(raw_prog& r, lexeme rel, size_t len);
	raw_prog reify(const raw_prog& p);
	raw_term from_grammar_elem(const elem& v, int_t v1, int_t v2);
	raw_term from_grammar_elem_nt(const lexeme& r, const elem& c,
		int_t v1, int_t v2);
	raw_term from_grammar_elem_builtin(const lexeme& r,const std::wstring&b,
		int_t v);
	raw_term prepend_arg(const raw_term& t, lexeme s);
//	void get_trees(std::wostream& os, const term& root,
//		const std::map<term, std::vector<term>>&, std::set<term>& done);
//	std::wstring get_trees(const term& roots,const db_t& t,size_t bits);
	void progs_read(wstr s);
	void prog_run(raw_progs& rp, size_t n, strs_t& strtrees);
	driver(raw_progs, options o);
	driver(raw_progs);
	size_t load_stdin();
	bool pfp();
	std::wstring std_input;
	prog_data pd;
	std::set<int_t> transformed_strings;
	tables *tbl = 0;
	void output_pl(const raw_prog& p) const;
	std::set<lexeme> vars;
	void run_(raw_progs &rp);
public:
	bool result = true;
	options opts;
	static void init();
	driver(options o);
	driver(FILE *f, options o);
	driver(std::wstring, options o);
	driver(char *s, options o);
	driver(FILE *f);
	driver(std::wstring);
	driver(char *s);
	~driver();

	void run(raw_progs rp) { run_(rp); };
	void out(std::wostream& os) const { if (tbl) tbl->out(os); };
	void out(const tables::rt_printer& p) const { if (tbl) tbl->out(p); };
#ifdef __EMSCRIPTEN__
	void out(emscripten::val o) const { if (tbl) tbl->out(o); };
	emscripten::val to_bin() {
		std::stringstream ss; ss << (*this);
		std::string bin = ss.str();
		emscripten::val r = emscripten::val::global("Uint8Array")
							.new_(bin.size());
		int n = 0;
		for (unsigned char b : bin) r.set(n++, b);
		return r;
	}
#endif

//	std::wostream& printbdd(std::wostream& os, spbdd t, size_t bits,
//		const prefix&) const;
//	std::wostream& printbdd_one(std::wostream& os, spbdd t, size_t bits,
//		const prefix&) const;
	std::wostream& print_prolog(std::wostream&, const raw_prog&,
		const prolog_dialect) const;
	std::wostream& print_xsb(std::wostream&, const raw_prog&) const;
	std::wostream& print_swipl(std::wostream&, const raw_prog&) const;
	std::wostream& print_souffle(std::wostream&, const raw_prog&) const;
	void output_ast() const;
	std::wostream& print_ast(std::wostream&) const;
	std::wostream& print_ast_json(std::wostream&) const;
	std::wostream& print_ast_xml(std::wostream&) const;
	std::wostream& print_ast_html(std::wostream&) const;
	void save_csv() const;
};

#ifdef DEBUG
extern driver* drv;
//std::wostream& printdb(std::wostream& os, lp *p);
std::wostream& printbdd(std::wostream& os, cr_spbdd_handle t, size_t bits,
	ints ar, int_t rel);
std::wostream& printbdd_one(std::wostream& os, cr_spbdd_handle t, size_t bits,
	ints ar, int_t rel);
//std::wostream& printbdd(std::wostream& os, size_t t, size_t bits, ints ar,
//	int_t rel);
#endif
std::wstring _unquote(std::wstring str);
#endif
