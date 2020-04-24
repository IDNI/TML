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
#include <map>
#include "defs.h"
#include "types.h"

class dict_t {
	typedef std::map<lexeme, int_t, lexcmp> dictmap;
	dictmap syms_dict, vars_dict, rels_dict, bltins_dict, types_dict;
	std::vector<lexeme> syms, rels, bltins;
	std::vector<arg_type> types;
	std::set<lexeme, lexcmp> strs_extra;
public:
	dict_t();
	dict_t(const dict_t& d) : syms_dict(d.syms_dict), vars_dict(d.vars_dict),
		rels_dict(d.rels_dict), bltins_dict(d.bltins_dict), 
		types_dict(d.types_dict), syms(d.syms), rels(d.rels), bltins(d.bltins),
		types(d.types), op(d.op), cl(d.cl) {
		DBG(assert(false);); // we shouldn't be copying, use move instead
		for (const lexeme& c : d.strs_extra) { 
			wstr r = wcsdup((wstr)c[0]);
			size_t s = wcslen(r);
			lexeme l = { r, r + s };
			strs_extra.insert(l);
		}
	}
	dict_t(dict_t&& d) noexcept : 
		syms_dict(std::move(d.syms_dict)), 
		vars_dict(std::move(d.vars_dict)),
		rels_dict(std::move(d.rels_dict)), 
		bltins_dict(std::move(d.bltins_dict)),
		types_dict(std::move(d.types_dict)), 
		syms(std::move(d.syms)), 
		rels(std::move(d.rels)), 
		bltins(std::move(d.bltins)),
		types(std::move(d.types)), 
		strs_extra(std::move(d.strs_extra)), 
		op(std::move(d.op)), cl(std::move(d.cl)) {
		std::fill(std::begin(d.op), std::end(d.op), nullptr);
		std::fill(std::begin(d.cl), std::end(d.cl), nullptr);
		//d.strs_extra.clear();
	}
	lexeme op, cl;
	const lexeme& get_rel(int_t t) const { return rels[t]; }
	const lexeme& get_bltin(int_t t) const { return bltins[t]; }
	const arg_type& get_type(int_t t) const { return types[t]; }
	lexeme get_sym(int_t t) const;
	int_t get_var(const lexeme& l);
	int_t get_rel(const lexeme& l);
	int_t get_sym(const lexeme& l);
	int_t get_bltin(const lexeme& l);
	int_t get_type(const lexeme& l);
	int_t get_type(const lexeme& l, int_t nums);
	int_t get_fresh_sym( int_t old);
	int_t get_fresh_var( int_t old);
	lexeme get_lexeme(const std::wstring& s);
	lexeme make_lexeme(const std::wstring& s) const;
	int_t get_sym(const std::wstring& s) { return get_sym(get_lexeme(s)); }
	int_t get_rel(const std::wstring& s) { return get_rel(get_lexeme(s)); }
	int_t get_bltin(const std::wstring& s) { return get_bltin(get_lexeme(s)); }
	int_t get_type(const std::wstring& s) { return get_type(get_lexeme(s)); }
	const arg_type& get_type_info(const lexeme& l)
	{ return get_type(get_type(l)); }
	const arg_type& get_type_info(const lexeme& l, int_t nums)
	{ return get_type(get_type(l, nums)); }
	size_t nsyms() const { return syms.size(); }
	size_t nvars() const { return vars_dict.size(); }
	size_t nrels() const { return rels.size(); }
	size_t nbltins() const { return bltins.size(); }
	size_t ntypes() const { return types.size(); }
	// copy and swap (utilize move)
	dict_t& operator=(dict_t d) { // noexcept 
		using std::swap;
		DBG(assert(false););
		return
			swap(syms_dict, d.syms_dict),
			swap(vars_dict, d.vars_dict),
			swap(rels_dict, d.rels_dict),
			swap(bltins_dict, d.bltins_dict),
			swap(syms, d.syms),
			swap(rels, d.rels),
			swap(bltins, d.bltins),
			swap(strs_extra, d.strs_extra),
			swap(op, d.op),
			swap(cl, d.cl),
			swap(types_dict, d.types_dict),
			swap(types, d.types),
			*this;
	}
	~dict_t();
};

std::wostream& operator<<(std::wostream& os, const dict_t& d);

#endif // __DICT_H__
