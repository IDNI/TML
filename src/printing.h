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
#ifndef __PRINTING_H__
#define __PRINTING_H__
#include "defs.h"

template <typename T, typename T1, typename T2>
std::basic_ostream<T>& operator<<(std::basic_ostream<T>& os,
	const std::map<T1,T2>& m);

template<typename T>
std::basic_ostream<T>& operator<<(std::basic_ostream<T>& os, const env& e);

template <typename T>
std::basic_ostream<T>& operator<<(std::basic_ostream<T>& os, const vbools& x);

struct elem;

std::string quote_sym(const elem& e);

#endif // __PRINTING_H__
