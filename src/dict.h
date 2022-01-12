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
	std::vector<lexeme> vars, syms, rels, bltins, temp_syms;
	std::set<lexeme, lexcmp> strs_extra;
	std::vector<ccs> strs_allocated;
	inputs* ii;
	bool bitunv;
public:
	dict_t();
	dict_t(const dict_t& d) : syms_dict(d.syms_dict), vars_dict(d.vars_dict),
		rels_dict(d.rels_dict), bltins_dict(d.bltins_dict), temp_syms_dict(d.temp_syms_dict),
		vars(d.vars), syms(d.syms), rels(d.rels), bltins(d.bltins),
		ii(d.ii), bitunv(d.bitunv), op(d.op), cl(d.cl) { // strs_extra(d.strs_extra), 
		DBG(assert(false);); // we shouldn't be copying, use move instead
		std::map<ccs, ccs> remap;
		for (ccs c : d.strs_allocated) {
			ccs r = strdup(c);
			remap.insert({ c, r });
			strs_allocated.push_back(r);
		}
		for (const lexeme& l : d.strs_extra)
			for (ccs c : d.strs_allocated)
				if (l[0] == c) { // remapped
					auto it = remap.find(c);
					if (it == remap.end()) { DBGFAIL; }
					ccs r = it->second;
					size_t s = strlen(r);
					lexeme lx = { r, r+s };
					strs_extra.insert(lx);
				} else strs_extra.insert(l);
	}
	dict_t(dict_t&& d) noexcept : 
		syms_dict(std::move(d.syms_dict)),
		vars_dict(std::move(d.vars_dict)),
		rels_dict(std::move(d.rels_dict)), 
		bltins_dict(std::move(d.bltins_dict)),
		temp_syms_dict(std::move(d.temp_syms_dict)),
		//types_dict(std::move(d.types_dict)),
		vars(std::move(d.vars)), 
		syms(std::move(d.syms)), 
		rels(std::move(d.rels)), 
		bltins(std::move(d.bltins)),
		temp_syms(std::move(d.temp_syms)),
		//types(std::move(d.types)), 
		strs_extra(std::move(d.strs_extra)),
		strs_allocated(std::move(d.strs_allocated)),
		ii(d.ii), bitunv(d.bitunv),
		op(std::move(d.op)), cl(std::move(d.cl)) {
		std::fill(std::begin(d.op), std::end(d.op), nullptr);
		std::fill(std::begin(d.cl), std::end(d.cl), nullptr);
		//d.strs_extra.clear();
	}
	lexeme op, cl;
	bool is_valid_sym(int_t arg) const {
		return bitunv == false ? ((arg &1) || (arg&2) || (size_t(arg>>2) < syms.size())):
				(arg > 1 && (size_t(arg-2) < syms.size()));
	}
	void set_inputs(inputs* ins) { ii = ins; }
	void set_bitunv(bool bu) { bitunv = bu; }
	const lexeme& get_rel(int_t t) const { return rels[t]; }
	const lexeme& get_bltin(int_t t) const { return bltins[t]; }
	bool is_temp_sym(const lexeme& l) const { return temp_syms_dict.find(l) != temp_syms_dict.end(); }
	lexeme get_sym(int_t t) const;
	bool is_valid_sym_val(int_t val) const;
	lexeme get_temp_sym(int_t t) const;
	int_t get_var(const lexeme& l);
	int_t get_rel(const lexeme& l);
	int_t get_sym(const lexeme& l);
	int_t get_temp_sym(const lexeme& l);
	int_t get_bltin(const lexeme& l);
	int_t get_fresh_sym(int_t old);
	int_t get_fresh_temp_sym(int_t old);
	int_t get_fresh_var(int_t old);
	lexeme get_var_lexeme_from(int_t r);
	lexeme get_lexeme(ccs w, size_t l = (size_t)-1);
	lexeme get_lexeme(const std::basic_string<char>& s);
	lexeme get_lexeme(const std::basic_string<unsigned char>& s);
	int_t get_rel(const std::string& s) { return get_rel(get_lexeme(s)); }
	int_t get_bltin(const std::string& s) { return get_bltin(get_lexeme(s)); }
	size_t nsyms() const { return syms.size(); }
	size_t nvars() const { return vars_dict.size(); }
	size_t nrels() const { return rels.size(); }
	size_t nbltins() const { return bltins.size(); }
	ints get_rels(std::function<bool(const lexeme&)> filter = nullptr);

	// copy and swap (utilize move)
	dict_t& operator=(dict_t d) {
		using std::swap;
		DBG(assert(false););
		return
			swap(syms_dict, d.syms_dict),
			swap(vars_dict, d.vars_dict),
			swap(rels_dict, d.rels_dict),
			swap(bltins_dict, d.bltins_dict),
			swap(vars, d.vars),
			swap(syms, d.syms),
			swap(rels, d.rels),
			swap(bltins, d.bltins),
			swap(temp_syms_dict, d.temp_syms_dict),
			swap(strs_extra, d.strs_extra),
			swap(ii, d.ii),
			swap(bitunv, d.bitunv),
			swap(op, d.op),
			swap(cl, d.cl),
			//swap(types_dict, d.types_dict),
			//swap(types, d.types),
			*this;
	}
	~dict_t();
};

template <typename T>
std::basic_ostream<T>& operator<<(std::basic_ostream<T>& os, const dict_t& d);

#endif // __DICT_H__
