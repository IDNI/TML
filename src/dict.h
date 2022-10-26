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

#ifdef REMOVE_DICT_FROM_BUILTINS
#include "builtins.h"
#endif

class inputs;
class dict_t {
	typedef std::map<lexeme, int_t, lexcmp> dictmap;
	dictmap syms_dict, vars_dict, rels_dict, temp_syms_dict;
	std::vector<lexeme> syms, vars, rels, temp_syms;

	#ifndef REMOVE_DICT_FROM_BUILTINS
	dictmap bltins_dict;
	std::vector<lexeme> bltins;
	#else 
	builtins bltins;
	#endif // REMOVE_DICT_FROM_BUILTINS

	std::set<lexeme, lexcmp> strs_extra;
	std::vector<ccs> strs_allocated;
	inputs* ii = 0;
public:

	#ifdef REMOVE_DICT_FROM_BUILTINS
	dict_t(builtins& bltins_) : bltins(bltins_) {};
	#else
	dict_t();
	#endif // REMOVE_DICT_FROM_BUILTINS

	~dict_t();

	void set_inputs(inputs* ins) { ii = ins; }

	int_t get_sym(const lexeme& l);
	int_t get_var(const lexeme& l);
	int_t get_rel(const lexeme& l);
	int_t get_bltin(const lexeme& l);
	const lexeme& get_sym_lexeme(int_t t) const  { return syms[t]; } ;
	const lexeme& get_var_lexeme(int_t r) const { return vars[-r-1]; };
	const lexeme& get_rel_lexeme(int_t t) const { return rels[t]; }
	const lexeme& get_bltin_lexeme(int_t t) const { 
		#ifndef REMOVE_DICT_FROM_BUILTINS
		return bltins[t]; 
		#else
		return bltins.bltins[t];
		#endif // REMOVE_DICT_FROM_BUILTINS

	}
	size_t nsyms() const { return syms.size(); }
	size_t nvars() const { return vars_dict.size(); }
	size_t nrels() const { return rels.size(); }
	size_t nbltins() const { return bltins.size(); }


	lexeme get_lexeme(ccs w, size_t l = (size_t)-1);
	lexeme get_lexeme(const std::basic_string<char>& s);
	lexeme get_lexeme(const std::basic_string<unsigned char>& s);
	int_t get_rel(const std::string& s) { return get_rel(get_lexeme(s)); }
	int_t get_bltin(const std::string& s) { return get_bltin(get_lexeme(s)); }

	int_t get_new_sym();
	int_t get_new_var();
	int_t get_new_rel();

	bool is_bltin(const lexeme& l) const {
		#ifndef REMOVE_DICT_FROM_BUILTINS
		auto it = bltins_dict.find(l);
		if (it != bltins_dict.end()) return true;
		#else
		auto it = bltins.bltins_dict.find(l);
		if (it != bltins.bltins_dict.end()) return true;
		#endif // REMOVE_DICT_FROM_BUILTINS
		return false;
	}

	ints get_rels(std::function<bool(const lexeme&)> filter = nullptr);

	// < -- to be deprecated
	int_t get_temp_sym(const lexeme& l);
	lexeme get_temp_sym(int_t t) const;
	int_t get_fresh_temp_sym();
	bool is_valid_sym_val(int_t t) const {
		return (t>>2 >= 0 && t>>2 < (int_t) syms.size());
	}
	// -->
};

template <typename T>
std::basic_ostream<T>& operator<<(std::basic_ostream<T>& os, const dict_t& d);

#endif // __DICT_H__
