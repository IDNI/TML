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
#ifndef __TYPES_H__
#define __TYPES_H__
#include <cassert>
#include <vector>
#include <set>
#include <unordered_map>
#include <array>
#include <iostream>
#include <iomanip>
#include <cstdio>
#include <map>

#include "defs.h"

struct alt_arg;
struct bitsmeta;
struct term;

/* argument type's base-type enum */
//enum class basetype : std::uint8_t { NONE = 0, INT, CHR, STR };
enum class base_type { NONE = 0, INT, CHR, STR };

// D: make this just an int_t, lower bits for type + bitness the rest.
struct arg_type {
	base_type type = base_type::NONE;
	size_t bitness;
	arg_type() : type(base_type::NONE), bitness(0) {}
	arg_type(base_type btype, size_t bits) : type(btype), bitness(bits) {
		//DBG(assert(bitness < 100););
	}
	void set_bitness(size_t bits) { 
		DBG(assert(bits < 100););
		bitness = bits;
	}
	inline bool operator<(const arg_type& other) const {
		if (type != other.type) return type < other.type;
		return bitness < other.bitness;
	}
	inline bool operator==(const arg_type& other) const {
		return type == other.type && bitness == other.bitness;
	}
};

typedef std::vector<arg_type> argtypes;

struct tbl_arg {
	ntable tab;
	size_t arg;
	tbl_arg(ntable t, size_t i) : tab(t), arg(i) {}
	tbl_arg(const alt_arg& aa);
	inline bool operator<(const tbl_arg& other) const {
		if (tab != other.tab) return tab < other.tab;
		return arg < other.arg;
	}
	inline bool operator==(const tbl_arg& other) const {
		return tab == other.tab && arg == other.arg;
	}
	inline bool operator!=(const tbl_arg& r) const { return !operator==(r); }
	inline bool operator> (const tbl_arg& r) const { return r.operator<(*this);}
	inline bool operator<=(const tbl_arg& r) const { return !operator>(r); }
	inline bool operator>=(const tbl_arg& r) const { return !operator<(r); }
};
//inline bool operator!=(const tbl_arg& l, const tbl_arg& r)
//{ return !operator==(l, r); }
//inline bool operator> (const tbl_arg& l, const tbl_arg& r)
//{ return  operator<(r, l); }
//inline bool operator<=(const tbl_arg& l, const tbl_arg& r)
//{ return !operator>(l, r); }
//inline bool operator>=(const tbl_arg& l, const tbl_arg& r)
//{ return !operator<(l, r); }

typedef tbl_arg tbl_alt;

struct alt_arg {
	ntable tab;
	int_t alt;
	size_t arg;
	alt_arg(ntable t, int_t a, size_t i) : tab(t), alt(a), arg(i) {}
	alt_arg(const tbl_arg& ta) : tab(ta.tab), alt(-1), arg(ta.arg) {}
	bool operator<(const alt_arg& aa) const {
		if (tab != aa.tab) return tab < aa.tab;
		if (alt != aa.alt) return alt < aa.alt;
		return arg < aa.arg;
	}
};

struct arg_info {
	int_t val, num;
	arg_type type;
	tbl_arg arg;
	arg_info(int_t val_, arg_type type_, int_t num_, tbl_arg arg_ = { -1,0 })
		: val(val_), num(num_), type(type_), arg(arg_) {}
	inline bool operator<(const arg_info& other) const {
		return val < other.val;
		//if (val != other.val) return val < other.val;
		//return arg < other.arg;
	}
};

std::wostream& operator<<(std::wostream&, const alt_arg&);
std::wostream& operator<<(std::wostream&, const tbl_arg&);
std::wostream& operator<<(std::wostream&, const arg_type&);
std::wostream& operator<<(std::wostream&, const argtypes&);
std::wostream& operator<<(std::wostream& os, const bitsmeta& bm);
//bool operator<(const alt_arg& aarg, const tbl_arg& ta);

#endif // __TYPES_H__