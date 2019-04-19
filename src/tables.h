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
#include <vector>
#include "bdd.h"

typedef int_t ntable;
typedef int_t rel_t;
struct raw_term;
class tables;
class dict_t;

typedef std::pair<rel_t, ints> sig_t;
typedef std::tuple<bool, sig_t, ints> term;

class tables {
private:
	struct item {
		bool neg;
		ntable tab;
		spbdd eq;
		bools ex;
		sizes perm, limit;
	};

	int_t syms = 0, nums = 0, chars = 0;
	size_t bits = 2, tbits = 0; // #bits for elem, #bits for table id
	dict_t& dict;

	std::map<sig_t, ntable> ts;
	std::vector<sig_t> sigs;
	bdds tbdds;
	size_t max_args = 0;
	std::map<std::array<int_t, 7>, spbdd> range_memo;

	spbdd db = F;

	size_t pos(size_t bit, size_t nbits, size_t arg, size_t args)const;
	size_t pos(size_t bit, size_t arg, size_t args) const;
	size_t arg(size_t v, size_t args) const;
	size_t bit(size_t v, size_t args) const;
	void add_bit();
	spbdd add_bit(spbdd x, ntable tab);
	void add_tbit();
	spbdd leq_const(int_t c, size_t arg, size_t args, size_t bit) const;
	spbdd range(size_t arg, ntable tab);
	void range_clear_memo();

	sig_t get_sig(const raw_term& t);
	ntable add_table(sig_t s);
	ntable get_table(const raw_term& t);
	spbdd from_row(const ints& row, ntable tab, bools *ex = 0);
	void add_terms(ntable tab, const std::vector<ints>& rows);
	void add_term(ntable tab, const ints& rows);
	void add_raw_term(const raw_term&);
	DBG(vbools allsat(spbdd x, ntable tab);)
public:
	typedef std::map<item, std::set<std::set<item>>> transaction;
	tables();
	~tables();
	void add_raw_terms(const std::vector<raw_term>& rows);
	void out(std::wostream&);
};

size_t sig_len(const sig_t& s);
