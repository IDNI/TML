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
#ifndef __DEFS_H__
#define __DEFS_H__
#include <cassert>
#include <vector>
#include <set>
#include <unordered_map>
#include <array>
#include <iostream>
#include <iomanip>
#include <cstdio>
#include <map>
#include <memory>
#include <optional>

#ifndef __EMSCRIPTEN__
#ifdef __unix__
#include <execinfo.h>
#endif
#endif

typedef int32_t int_t;
typedef uint32_t uint_t;
typedef std::vector<uint_t> uints;
typedef std::vector<int_t> ints;
typedef std::vector<bool> bools;
typedef std::vector<bools> vbools;
typedef int_t ntable;
typedef size_t nlevel;

#include "char_defs.h"

#ifdef DEBUG
#define DBG(x) x
#define NDBG(x)
#define DBGFAIL assert(0)
#else
#define DBG(x)
#define NDBG(x) x
#define DBGFAIL
#endif

#define msb(x) ((sizeof(unsigned long long)<<3) - \
	__builtin_clzll((unsigned long long)(x)))
#define has(x, y) ((x).find(y) != (x).end())
#define hasb(x, y) std::binary_search(x.begin(), x.end(), y)
#define hasbc(x, y, f) std::binary_search(x.begin(), x.end(), y, f)
#define measure_time_start() start = clock()
#define measure_time_end() end = clock(), \
		o::ms() << std::fixed << std::setprecision(2) << \
		(double(end - start) / CLOCKS_PER_SEC) * 1000 \
		<< " ms" << endl
#define measure_time(x) measure_time_start(); x; measure_time_end()
#define elem_openp elem(elem::OPENP)
#define elem_closep elem(elem::CLOSEP)
#define elem_eq elem(elem::EQ, get_lexeme("="))
#define htrue bdd_handle::T
#define hfalse bdd_handle::F

template<typename T> T sort(const T& x){T t=x;return sort(t.begin(),t.end()),t;}

/* Get the given key from the map and if this fails, return the supplied
 * default. */

template<template<class, class, class ...> class M, typename K, typename V, typename ... Args>
		V at_default(const M<K, V, Args ...> &m, const K &k, const V &d) {
	auto it = m.find(k);
	if(it != m.end()) {
		return it->second;
	} else {
		return d;
	}
}

/* Generically hash vectors using the hasher for the element type. */

template<typename X> struct std::hash<std::vector<X>> {
	size_t operator()(const std::vector<X>&) const;
};

template<typename X> size_t
		std::hash<std::vector<X>>::operator()(const std::vector<X>& vec) const {
	std::hash<X> hasher;
	size_t seed = vec.size();
	for(auto& i : vec) {
		seed ^= hasher(i) + 0x9e3779b9 + (seed << 6) + (seed >> 2);
	}
	return seed;
}

#ifdef _WIN32
std::string temp_filename();
#else
int temp_fileno();
std::string filename(int fd);
#endif

typedef std::map<int_t, int_t> env;

// Modes in which proof extraction code can be run
enum proof_mode { none, tree, forest, partial_tree, partial_forest };

//runtime options
typedef struct {
	bool optimize, print_transformed, apply_regexpmatch, fp_step, bitunv,
		show_hidden;
	enum proof_mode bproof;
	size_t bitorder;
	std::set<ntable> pu_states;
} rt_options;


typedef enum { REL, EQ, LEQ, BLTIN, ARITH, CONSTRAINT, VAR, FORM1, FORM2 } t_term;

typedef enum  {
	NOP, ADD, SUB, MULT, BITWAND, BITWOR, BITWXOR, BITWNOT, SHR, SHL
} t_arith_op;

struct alt;
struct form;
struct body;
struct pnf_t;
typedef enum {EX, UN, FA, EXH, UNH, FAH} quant_t;
typedef std::map<int_t, size_t> varmap;
typedef std::shared_ptr<class bdd_handle> spbdd_handle;
typedef std::shared_ptr<form> spform_handle;
typedef const spform_handle& cr_spform_handle;

template<typename T> struct ptrcmp {
	bool operator()(const T* x, const T* y) const { return *x < *y; }
};

//-----------------------------------------------------------------------------
#define TML_NATIVES
//#define TYPE_RESOLUTION //work-in-progress, dependent on TML_NATIVES
//#define BIT_TRANSFORM  //to be deprecated, use it with --bitunv option
#if defined(BIT_TRANSFORM) | defined(TYPE_RESOLUTION)
#define mkchr(x) ((int_t) x )
#define mknum(x) ((int_t) x )
#define mksym(x) ((int_t) x )
#else
#define mkchr(x) ((int_t) ((x) << 2) | 1)
#define mknum(x) ((int_t) ((x) << 2) | 2)
#define mksym(x) ((int_t) ((x) << 2) )
#endif

#ifdef TML_NATIVES
typedef enum {UNDEF, UINT, INT, RATIONAL, UCHAR, SYMB, POLY} native_type;
struct tml_native_t {
	native_type type = UNDEF;
	int_t bit_w = -1;
	bool operator==(const tml_native_t& l) const {
	     return (l.type == type && l.bit_w == bit_w) || (l.type == UNDEF) || (l.type == POLY);
	}
	bool operator<(const tml_native_t& l) const {
		//if (*this == l) return false;
		//return l.type < type && l.bit_w < bit_w;
		return std::tie(l.type, l.bit_w) < std::tie(type, bit_w);
	}
};
typedef std::vector<tml_native_t> tml_natives;
typedef std::pair<int_t, tml_natives> sig;  //<rel_id, args_types>
#else
typedef std::pair<int_t, ints> sig;
#endif

//-----------------------------------------------------------------------------
// GIT_* macros are populated at compile time by -D or they're set to "n/a"
#ifndef GIT_DESCRIBED
#define GIT_DESCRIBED   "n/a"
#endif
#ifndef GIT_COMMIT_HASH
#define GIT_COMMIT_HASH "n/a"
#endif
#ifndef GIT_BRANCH
#define GIT_BRANCH      "n/a"
#endif
#endif
