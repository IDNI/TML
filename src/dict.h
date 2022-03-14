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
#ifndef __DICT_H__
#define __DICT_H__
#include "defs.h"
#include <map>
#include <functional>

class inputs;
class dict_t {
	typedef std::map<lexeme, int_t, lexcmp> dictmap;
	dictmap syms_dict, vars_dict, rels_dict, bltins_dict, temp_syms_dict;
	std::vector<lexeme> syms, vars, rels, bltins, temp_syms;
	std::set<lexeme, lexcmp> strs_extra;
	std::vector<ccs> strs_allocated;
	inputs* ii = 0;
	bool bitunv = false;
public:
	dict_t();
	~dict_t();
	void set_inputs(inputs* ins) { ii = ins; }
	void set_bitunv(bool bu) { bitunv = bu; }

	int_t get_sym(const lexeme& l);
	int_t get_var(const lexeme& l);
	int_t get_rel(const lexeme& l);
	int_t get_bltin(const lexeme& l);
	int_t get_temp_sym(const lexeme& l);

	const lexeme& get_var_lexeme(int_t r) const { return vars[-r -1]; };
	const lexeme& get_rel(int_t t) const { return rels[t]; }
	const lexeme& get_bltin(int_t t) const { return bltins[t]; }

	int_t get_rel(const std::string& s) { return get_rel(get_lexeme(s)); }
	int_t get_bltin(const std::string& s) { return get_bltin(get_lexeme(s)); }
	lexeme get_lexeme(const std::basic_string<char>& s);
	lexeme get_lexeme(const std::basic_string<unsigned char>& s);

	size_t nsyms() const { return syms.size(); }
	size_t nvars() const { return vars_dict.size(); }
	size_t nrels() const { return rels.size(); }
	size_t nbltins() const { return bltins.size(); }

	bool is_bltin(const lexeme& l) const {
		auto it = bltins_dict.find(l);
		if (it != bltins_dict.end()) return true;
		return false;
	}


	// < --
	bool is_temp_sym(const lexeme& l) const { return temp_syms_dict.find(l) != temp_syms_dict.end(); }
	lexeme get_sym(int_t t) const;
	bool is_valid_sym_val(int_t val) const;
	lexeme get_temp_sym(int_t t) const;
	int_t get_fresh_sym();
	int_t get_fresh_temp_sym();
	int_t get_fresh_var();

	lexeme get_lexeme(ccs w, size_t l = (size_t)-1);

	ints get_rels(std::function<bool(const lexeme&)> filter = nullptr);
	bool is_valid_sym(int_t arg) const {
		return bitunv == false ? ((arg &1) || (arg&2) || (size_t(arg>>2) < syms.size())):
				(arg > 1 && (size_t(arg-2) < syms.size()));
	}
	// -->
};

template <typename T>
std::basic_ostream<T>& operator<<(std::basic_ostream<T>& os, const dict_t& d);

#endif // __DICT_H__
