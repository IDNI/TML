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
#include <map>
#include "lp.h"
#include "input.h"
#include "dict.h"

class driver {
	dict_t dict;
	std::set<int_t> builtin_rels;//, builtin_symbdds;
	matrix from_bits(spbdd x, size_t bits, const prefix& p) const;
	void from_bits(spbdd x, size_t bits, const prefix& p,
		std::function<void(const term&)> f) const;
	term one_from_bits(spbdd x, size_t bits, const prefix& p) const;

	int_t nums = 0, chars = 0, syms = 0;
//	bool mult = false;

	lexeme get_var_lexeme(int_t i);
	lexeme get_num_lexeme(int_t i);
	lexeme get_char_lexeme(wchar_t i);
	term get_term(raw_term r, const strs_t& s);
	std::pair<matrix, matrix> get_rule(const raw_rule&, const strs_t& s);
	void count_term(const raw_term& t, std::set<lexeme, lexcmp>& syms);
	void get_dict_stats(const raw_prog& p);

	std::wstring directive_load(const directive& d);
	void directives_load(raw_prog& p, prog_data& pd, lexeme& trel);
	void add_rules(raw_prog& p, prog_data& pd);
	void transform(raw_progs& rp, size_t n, prog_data& pd,
		const strs_t& strtrees);
	raw_prog transform_bwd(raw_prog& p);
	void transform_proofs(raw_prog& r, const lexeme& rel);
	void transform_string(const std::wstring&, raw_prog&, int_t);
	void transform_grammar(raw_prog& r, size_t len);
	raw_term from_grammar_elem(const elem& v, int_t v1, int_t v2);
	raw_term from_grammar_elem_nt(const lexeme& r, const elem& c,
		int_t v1, int_t v2);
	raw_term from_grammar_elem_builtin(const lexeme& r,const std::wstring&b,
		int_t v);
	raw_term prepend_arg(raw_term t, lexeme s);
	void get_trees(std::wostream& os, const term& root,
		const std::map<term, std::vector<term>>&, std::set<term>& done);
	std::wstring get_trees(const term& roots,const diff_t& t,size_t bits);
	void progs_read(wstr s);
	lp* prog_run(raw_progs& rp, size_t n, lp* last, strs_t& strtrees);
	driver(int argc, char** argv, raw_progs, bool print_transformed,
		bool xsb, bool souffle, bool csv);
	size_t load_stdin();
	bool pfp();
	std::wstring std_input;
	int argc;
	char** argv;
	bool print_transformed;
	bool xsb;
	bool souffle;
	bool csv;
public:
	bool result = true;
	driver(int argc, char** argv, FILE *f, bool print_transformed = false,
		bool xsb = false, bool souffle = false, bool csv = false);
	driver(int argc, char** argv, std::wstring,
	bool print_transformed = false, bool xsb = false, bool souffle = false,
	bool csv = false);

	matrix getbdd(size_t t) const;
	matrix getbdd_one(size_t t) const;
	matrix getdb() const;
	std::wostream& print_term(std::wostream& os, const term& t) const;
	std::wostream& printmat(std::wostream& os, const matrix& t) const;
	std::wostream& printmats(std::wostream& os, const matrices& t) const;
	std::wostream& printbdd(std::wostream& os, spbdd t, size_t bits,
		const prefix&) const;
	std::wostream& printbdd_one(std::wostream& os, spbdd t, size_t bits,
		const prefix&) const;
	std::wostream& printdb(std::wostream& os, lp *p) const;
	std::wostream& printdb(std::wostream& os, const db_t& db, size_t bits)
		const;
	std::wostream& printdiff(std:: wostream& os, const diff_t& d,
		size_t bits) const;
	std::wostream& print_xsb(std::wostream& os, const raw_prog& rp) const;
	std::wostream& print_souffle(std::wostream& os, const raw_prog& rp)
		const;
	std::wostream& print_term_xsb(std::wostream& os, const term& t) const;
	std::wostream& print_term_souffle(std::wostream& os, const term& t)
		const;
	std::wostream& print_term_csv(std::wostream& os, const term& t) const;
	void save_csv(lp *p) const;
	void save_csv(const db_t& db, size_t bits) const;
};

#ifdef DEBUG
extern driver* drv;
std::wostream& printdb(std::wostream& os, lp *p);
std::wostream& printdiff(std:: wostream& os, const diff_t& d, size_t bits);
std::wostream& printbdd(std::wostream& os, spbdd t, size_t bits, ints ar,
	int_t rel);
std::wostream& printbdd_one(std::wostream& os, spbdd t, size_t bits, ints ar,
	int_t rel);
//std::wostream& printbdd(std::wostream& os, size_t t, size_t bits, ints ar,
//	int_t rel);
#endif
std::wstring _unquote(std::wstring str);
