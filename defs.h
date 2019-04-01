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
typedef int64_t int_t;
typedef wchar_t* wstr;
typedef const wchar_t* cws;
typedef cws* pcws;
typedef std::array<cws, 2> lexeme;
typedef std::vector<lexeme> lexemes;
typedef std::vector<int_t> ints;
typedef std::unordered_map<int_t, std::wstring> strs_t;
typedef std::vector<bool> bools;
typedef std::vector<bools> vbools;

//#define DEBUG
#ifdef DEBUG
#define DBG(x) x
#else
#define DBG(x)
#endif
#define _er(x)	perror(x), exit(0)
#define msb(x) ((sizeof(unsigned long long)<<3) - \
	__builtin_clzll((unsigned long long)(x)))
#endif
#define POS(bit, bits, arg, args) ((bits - (bit) - 1)*(args)+(arg))
#define ARG(pos, args) ((pos)%(args))
#define BIT(pos, args, bits) (bits-((pos)/(args))-1)
