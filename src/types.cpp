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
#include <algorithm>
#include <list>
#include "types.h"
#include "bitsmeta.h"
#include "err.h"
#include "input.h"
//#include "term.h"
//#include "tables.h"

using namespace std;

tbl_arg::tbl_arg(const alt_arg& other) 
	: tab(other.tab), arg(other.arg), subarg(other.subarg) {
	//DBG(assert(other.alt == -1););
}

tbl_arg::tbl_arg(const vm_arg& other)
	: tab(other.tab), arg(other.arg), subarg(other.subarg) {
}

vector<size_t> type::normalize_sig(vector<size_t> sig) {
	for (size_t& el : sig)
		if (el != elem::etype::OPENP &&
			el != elem::etype::CLOSEP)
			el = elem::etype::NONE;
	return sig;
}

wostream& operator<<(wostream& os, const alt_arg& arg) {
	if (arg.alt == -1)
		return os << L"(" << arg.tab << L"," << arg.arg << L")"; // << endl;
	return os << L"(" << arg.tab << L"," << arg.alt << L"," << arg.arg << L")"; 
}
wostream& operator<<(wostream& os, const tbl_arg& arg) {
	return os << L"(" << arg.tab << L"," << arg.arg << L")"; // << endl;
}

wostream& operator<<(wostream& os, const primitive_type& type) {
	switch (type.type) {
	case base_type::CHR: os << L":chr"; break;
	case base_type::STR: os << L":str"; break;
	case base_type::INT: os << L":int"; break;
	case base_type::NONE: os << L":none"; break;
	}
	return os << L"[" << type.bitness << L"]";
}

wostream& operator<<(wostream& os, const arg_type& type) {
	if (type.isPrimitive())
		return os << type.primitive;
	else if (type.isCompound()) {
		const primtypes& types = type.compound.types;
		//auto types = type.get_types();
		os << L"(";
		for (size_t i = 0; i != types.size(); ++i) {
			//if (i != 0) os << L" ";
			os << types[i];
		}
		os << L")";
		return os;
	}
	else throw 0;
}

wostream& operator<<(wostream& os, const argtypes& types) {
	//for (const arg_type& type : types) {
	for (size_t i = 0; i != types.size(); ++i) {
		if (i > 0) os << L" ";
		os << types[i];
	}
	return os;
}

wostream& operator<<(wostream& os, const bitsmeta& bm) {
	//for (const arg_type& type : types) {
	for (size_t i = 0; i != bm.types.size(); ++i) {
		if (i > 0) os << L" ";
		os << bm.types[i];
		auto type = bm.types[i];
		if (type.isPrimitive())
			os << L"[" << type.primitive.num << L"]";
		else if (type.isCompound()) {
			const primtypes& types = type.compound.types;
			os << L"[";
			for (size_t i = 0; i != types.size(); ++i) {
				if (i != 0)
					os << L" ";
				os << types[i].num;
			}
			os << L"]";
			return os;
		}
		//else {} // throw 0;
		//os << L"[" << bm.types[i].nums[i] << L"]";
	}
	return os;
}

