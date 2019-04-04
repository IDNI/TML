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
	std::set<size_t> builtin_rels;//, builtin_symbdds;
	matrix from_bits(size_t x, ints art, int_t rel) const;
	template<typename F>
	void from_bits(size_t x, ints art, int_t rel, F f) const;
	term one_from_bits(size_t x, ints art, int_t rel) const;

	bool mult = false;

	lexeme get_var_lexeme(int_t i);
	lexeme get_num_lexeme(int_t i);
	lexeme get_char_lexeme(wchar_t i);
	term get_term(const raw_term&);
	std::pair<matrix, matrix> get_rule(const raw_rule&);
	void count_term(const raw_term& t, std::set<lexeme, lexcmp>& rels,
		std::set<lexeme, lexcmp>& syms);
	strs_t get_dict_stats(const raw_prog& p,
		const std::map<lexeme, std::wstring>& s);

	std::wstring directive_load(const directive& d);
	std::map<lexeme, std::wstring> directives_load(
		const std::vector<directive>& p);
	raw_prog transform_bwd(const raw_prog& p,const std::vector<raw_term>&g);
	void insert_goals(raw_prog& r, const std::vector<raw_rule>& g);
	void transform_proofs(const raw_rule& x, raw_prog &r, raw_prog &_r);
	std::array<raw_prog, 2> transform_proofs(
		const std::vector<raw_prog> p,
		const std::vector<raw_rule>& g);
	void transform_string(const std::wstring&, raw_prog&, const lexeme&);
	std::array<raw_prog, 2> transform_grammar(const directive&,
		const std::vector<production>&, const std::wstring&);
	std::vector<std::pair<raw_prog, std::map<lexeme, std::wstring>>>
		transform(raw_prog p);
	bool print_transformed;
	void grammar_to_rules(const std::vector<production>& g, matrices& m,
		int_t rel);
	lp* prog_init(const raw_prog& rp, strs_t, lp* last);
	void progs_read(wstr s);
	driver(int argc, char** argv, raw_progs, bool print_transformed);
	size_t load_stdin();
	bool pfp();
	std::wstring std_input;
	int argc;
	char** argv;
public:
	size_t bits;
	bool result = true;
	driver(int argc, char** argv, FILE *f, bool print_transformed = false);
	driver(int argc, char** argv, std::wstring,
		bool print_transformed = false);

	matrix getbdd(size_t t) const;
	matrix getbdd_one(size_t t) const;
	matrix getdb() const;
	std::wostream& print_term(std::wostream& os, const term& t) const;
	std::wostream& printbdd(std::wostream& os, const matrix& t) const;
	std::wostream& printbdd(std::wostream& os, const matrices& t) const;
	std::wostream& printbdd(std::wostream& os, size_t t, ints ar, int_t rel)
		const;
	std::wostream& printbdd_one(std::wostream& os, size_t t, ints ar,
		int_t rel) const;
	std::wostream& printdb(std::wostream& os, lp *p) const;
	std::wostream& printdb(std::wostream& os, const db_t& db) const;
	std::wostream& printdiff(std:: wostream& os, const diff_t& d) const;
};

#ifdef DEBUG
extern driver* drv;
std::wostream& printdb(std::wostream& os, lp *p);
std::wostream& printdiff(std:: wostream& os, const diff_t& d);
std::wostream& printbdd(std::wostream& os, size_t t, ints ar, int_t rel);
std::wostream& printbdd_one(std::wostream& os, size_t t, ints ar, int_t rel);
//std::wostream& printbdd(std::wostream& os, size_t t, size_t bits, ints ar,
//	int_t rel);
#endif
