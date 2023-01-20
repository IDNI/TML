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
#include <cstring>

#ifndef __EMSCRIPTEN__
#ifdef __unix__
#include <execinfo.h>
#endif
#endif

#define WITH_ARITH 1
#include "bdd.h"
#include "characters.h"


namespace idni {

#ifdef DEBUG
#define DBG(x) x
#define NDBG(x)
#define DBGFAIL assert(0)
#else
#define DBG(x)
#define NDBG(x) x
#define DBGFAIL
#endif

typedef unsigned char char_t;               // internal char representation
typedef char_t* cstr;
typedef int32_t int_t;
typedef uint32_t uint_t;
typedef std::vector<uint_t> uints;
typedef std::vector<int_t> ints;
typedef std::vector<bool> bools;
typedef std::vector<bools> vbools;
typedef int_t ntable;
typedef size_t nlevel;

extern std::wostream wcnull;
extern std::ostream cnull;

#ifdef WITH_WCHAR
typedef wchar_t syschar_t;
#define CIN   std::wcin
#define COUT  std::wcout
#define CERR  std::wcerr
#define CNULL wcnull
#define EMPTY_STRING L""
#else // WITH_WCHAR
typedef char syschar_t;
#define CIN   std::cin
#define COUT  std::cout
#define CERR  std::cerr
#define CNULL cnull
#define EMPTY_STRING ""
#endif // WITH_WCHAR

typedef utf8char char_t;
typedef utf8string string_t;
std::string to_string(int_t v);
template <typename T>
string_t to_string_t(const T& v) { return to_utf8string(v); }

typedef std::basic_string<syschar_t>        sysstring_t;
typedef std::basic_istream<syschar_t>       istream_t;
typedef std::basic_ostream<syschar_t>       ostream_t;
typedef std::basic_ofstream<syschar_t>      ofstream_t;
typedef std::basic_ostringstream<syschar_t> ostringstream_t;
typedef std::basic_istringstream<syschar_t> istringstream_t;
typedef std::vector<std::string>            strings;
typedef std::vector<std::wstring>           wstrings;

typedef const char_t* ccs;
typedef std::array<ccs, 2> lexeme;
const lexeme null_lexeme{ 0, 0 };
typedef std::vector<lexeme> lexemes;
typedef std::array<size_t, 2> lexeme_range;

struct lexcmp { bool operator()(const lexeme& x, const lexeme& y) const; };
bool operator==(const lexeme& l, std::string s);
bool operator==(const lexeme& l, const char* s);
bool operator<(const lexeme&, const lexeme&);
bool operator==(const lexeme& x, const lexeme& y);
#define lexeme2str(l) string_t((l)[0], (l)[1]-(l)[0])
#define str2lexeme(s) { (unsigned char *) (s), (unsigned char *) (s) + sizeof(s) - 1 }

typedef std::map<lexeme, string_t, lexcmp> strs_t;

std::wstring s2ws(const std::string&);
std::wstring s2ws(const std::wstring&);
std::string  ws2s(const std::string&);
std::string  ws2s(const std::wstring&);

std::wostream& operator<<(std::wostream& os, const std::string& s);
std::ostream&  operator<<(std::ostream&  os, const char c);

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

#ifdef _WIN32
std::string temp_filename();
#else
int temp_fileno();
std::string filename(int fd);
#endif

typedef std::map<int_t, int_t> env;

// Modes in which proof extraction code can be run
enum proof_mode { none, tree, forest_mode, partial_tree, partial_forest };

//runtime options
typedef struct {
	bool optimize, print_transformed, apply_regexpmatch, fp_step,
		show_hidden, bin_lr, incr_gen_forest,
		binarize = true, print_binarized = false; //needed default values

	enum proof_mode bproof;
	size_t bitorder;
	std::set<ntable> pu_states;
} rt_options;


typedef enum {
	REL, EQ, LEQ, BLTIN, ARITH, CONSTRAINT, VAR, FORM1, FORM2
} t_term;

typedef enum  {
	NOP, ADD, SUB, MULT, BITWAND, BITWOR, BITWXOR, BITWNOT, SHR, SHL
} t_arith_op;

struct alt;
struct form;
struct body;
struct pnf_t;
typedef std::map<int_t, size_t> varmap;
typedef std::shared_ptr<form> spform_handle;
typedef const spform_handle& cr_spform_handle;

template<typename T> struct ptrcmp {
	bool operator()(const T* x, const T* y) const { return *x < *y; }
};

//-----------------------------------------------------------------------------
//#define BIT_TRANSFORM  //to be deprecated,

#define TML_NATIVES
// #define TYPE_RESOLUTION //work-in-progress, depends on TML_NATIVES
// #define BIT_TRANSFORM_V2 //work-in-progress, depends on TYPE_RESOLUTION

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
typedef enum { SYMB = 0, UINT = 1, UCHAR = 2, POLY = 3, UNDEF, INT, RATIONAL } native_type;
struct tml_native_t {
	native_type type = UNDEF;
	int_t bit_w = -1;
	bool operator==(const tml_native_t& l) const {
	     return (l.type == type) || (l.type == UNDEF) || (l.type == POLY);
	}
	bool operator<(const tml_native_t& l) const {
		return std::tie(type, bit_w) < std::tie(l.type, l.bit_w);
	}
};
typedef std::vector<tml_native_t> tml_natives;
typedef std::pair<int_t, tml_natives> sig;  //<rel_id, args_types>
#else
typedef std::pair<int_t, ints> sig;
#endif
//-----------------------------------------------------------------------------
#define FOL_V1 //mutually exclusive with FOL_V2
//#define FOL_V2
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

} // idni namespace

#endif // __DEFS_H__
