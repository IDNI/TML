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
#include <numeric>
#include <algorithm>
#include "defs.h"

struct alt_arg;
struct bitsmeta;
struct term;

/* argument type's base-type enum */
//enum class basetype : std::uint8_t { NONE = 0, INT, CHR, STR };
enum class base_type { NONE = 0, INT, CHR, STR };

// D: make this just an int_t, lower bits for type + bitness the rest.

//struct arg_type {
struct primitive_type {
	primitive_type() : type(base_type::NONE), bitness(0) {}
	primitive_type(base_type type_, size_t bits) : type(type_), bitness(bits) {
		if (bits > 4) {
			//o::dump() << L"bits > 4" << std::endl;
		}
	}
	primitive_type(base_type type_, size_t bits, int_t num) 
		: type(type_), bitness(bits), num(num) {
		if (num > 9) {
			//o::dump() << L"num > 9" << std::endl;
		}
		if (bits > 4) {
			//o::dump() << L"bits > 4" << std::endl;
		}
	}

	//primitive_type(const primitive_type& other) {
	//	type = other.type;
	//	bitness = other.bitness;
	//}
	//primitive_type(primitive_type&& other) noexcept {
	//	type = other.type;
	//	bitness = other.bitness;
	//}
	//primitive_type& operator=(primitive_type&& other) {
	//	type = other.type;
	//	bitness = other.bitness;
	//	//type(std::move(other.type));
	//	//bitness(std::move(other.bitness));
	//	return *this;
	//}
	//primitive_type& operator=(primitive_type other) {
	//	using std::swap;
	//	type = other.type;
	//	bitness = other.bitness;
	//	return *this;
	//}

	inline bool operator<(const primitive_type& other) const {
		if (type != other.type) return type < other.type;
		return bitness < other.bitness;
	}
	inline bool operator==(const primitive_type& other) const {
		return type == other.type && bitness == other.bitness;
	}
	inline bool operator!=(const primitive_type& r) const 
	{ return !operator==(r); }
	inline bool operator> (const primitive_type& r) const 
	{ return r.operator<(*this); }
	inline bool operator<=(const primitive_type& r) const 
	{ return !operator>(r); }
	inline bool operator>=(const primitive_type& r) const 
	{ return !operator<(r); }

	inline bool isNone() const {
		return type == base_type::NONE;
	}

	int_t get_chars() const { return type == base_type::CHR ? 255 : 0; }
	int_t get_syms(size_t nsyms = 0) const {
		return type == base_type::STR ? nsyms : 0;
	}

	void set_bitness(size_t bits) {
		//DBG(assert(bits < 100););
		if (bits > 4) {
			//o::dump() << L"bits > 4" << std::endl;
		}
		bitness = bits;
	}

	void set_num(int_t num_) {
		if (num_ > 9) {
			//o::dump() << L"num > 9" << std::endl;
		}
		num = num_;
	}

	base_type type = base_type::NONE;
	size_t bitness = 0;
	// we need to track exact 'nums' for the range leq (bits are not enough).
	int_t num = 0;
};

//typedef primitive_type arg_type;
//typedef std::vector<arg_type> argtypes;

//typedef std::vector<arg_type> argtypes;
//typedef arg_type primitive_type;
typedef std::vector<primitive_type> primtypes;

/* compound type (only has primitive types?) */
struct compound_type {
	compound_type() {} // only if we remove union
	compound_type(primtypes types_) : types(types_) { // std::move
		//sumOfBits = calc_sum();
	}

	//compound_type(const compound_type& other) { // noexcept
	//	types = other.types;
	//	sumOfBits = other.sumOfBits;
	//	//sumOfBits = calc_sum();
	//}
	//compound_type(compound_type&& other) noexcept {
	//	types = std::move(other.types); break;
	//	sumOfBits = other.sumOfBits;
	//	//sumOfBits = calc_sum();
	//}
	//compound_type& operator=(const compound_type& other) { // noexcept 
	//	types = other.types;
	//	sumOfBits = other.sumOfBits;
	//	return *this;
	//}

	inline bool operator<(const compound_type& other) const {
		return types < other.types;
	}
	inline bool operator==(const compound_type& other) const {
		return types == other.types;
	}
	inline bool operator!=(const compound_type& r) const
	{ return !operator==(r); }
	inline bool operator> (const compound_type& r) const
	{ return r.operator<(*this); }
	inline bool operator<=(const compound_type& r) const
	{ return !operator>(r); }
	inline bool operator>=(const compound_type& r) const
	{ return !operator<(r); }

	inline static size_t calc_sum(const primtypes& types) {
		size_t sum = 0;
		for (auto type : types) sum += type.bitness;
		return sum;
		//return std::accumulate(types.begin(), types.end(), 0,
		//	[](size_t accumulator, const primitive_type& type) {
		//		return accumulator + type.bitness;
		//	});
	}

	size_t get_bits() const {
		return calc_sum(types);
		//if (sumOfBits == 0 && !types.empty()) // assume it's not sum==0
		//	sumOfBits = std::accumulate(types.begin(), types.end(), 0,
		//		[](size_t accumulator, const primitive_type& type) {
		//			return accumulator + type.bitness;
		//		});
		//return sumOfBits;
	}

	//std::vector<size_t> get_bits_vector() {
	//	//std::vector<std::size_t> vbits;
	//	if (vbits.empty())
	//		std::transform(
	//			types.begin(), types.end(), std::back_inserter(vbits),
	//			[](const primitive_type& type) { return type.bitness; });
	//	return vbits;
	//}

	size_t get_bits(size_t subarg) const {
		if (subarg >= types.size()) throw 0;
		return types[subarg].bitness;
	}
	base_type get_type(size_t subarg) const {
		if (subarg >= types.size()) throw 0;
		return types[subarg].type;
	}
	primtypes get_types() const { return types;	}

	primtypes types;
	//size_t sumOfBits = 0;
	//std::vector<size_t> vbits;
};
struct sub_type {
	inline bool operator<(const sub_type&) const {
		return true; // types < other.types;
	}
	inline bool operator==(const sub_type&) const {
		return true; // types == other.types;
	}
	inline bool operator!=(const sub_type& r) const {
		return !operator==(r);
	}
	inline bool operator> (const sub_type& r) const {
		return r.operator<(*this);
	}
	inline bool operator<=(const sub_type& r) const {
		return !operator>(r);
	}
	inline bool operator>=(const sub_type& r) const {
		return !operator<(r);
	}
};
struct union_type {
	inline bool operator<(const union_type&) const {
		return true; // types < other.types;
	}
	inline bool operator==(const union_type&) const {
		return true; // types == other.types;
	}
	inline bool operator!=(const union_type& r) const {
		return !operator==(r);
	}
	inline bool operator> (const union_type& r) const {
		return r.operator<(*this);
	}
	inline bool operator<=(const union_type& r) const {
		return !operator>(r);
	}
	inline bool operator>=(const union_type& r) const {
		return !operator<(r);
	}
};

struct type;
//typedef std::vector<type> vtypes;

//struct field {
//	type type;
//	std::wstring name;
//};

/* record type */
struct record_type {
	inline bool operator<(const record_type& other) const {
		if (types != other.types) return types < other.types;
		return names < other.names;
	}
	inline bool operator==(const record_type& other) const {
		return types == other.types && names == other.names;
	}
	inline bool operator!=(const record_type& r) const {
		return !operator==(r);
	}
	inline bool operator> (const record_type& r) const {
		return r.operator<(*this);
	}
	inline bool operator<=(const record_type& r) const {
		return !operator>(r);
	}
	inline bool operator>=(const record_type& r) const {
		return !operator<(r);
	}

	std::vector<type> types;
	std::vector<std::wstring> names;
};

//enum class type_type { Primitive, Compound, Record };

struct type {
	//type(base_type type_, size_t bits):kind(Primitive),primitive{type_,bits}{}
	//type(primitive_type type_) : kind(Primitive), primitive(type_) {}
	type() : kind(Primitive), primitive() {} // needed for bitsmeta types(len)
	type(base_type type_, size_t bits):kind(Primitive), primitive{type_, bits}{}
	type(base_type type_, size_t bits, int_t num)
		: kind(Primitive), primitive{type_, bits, num} {}
	type(primitive_type type_) : type(type_.type, type_.bitness) {}
	type(compound_type type_) : kind(Compound), compound(type_) {}
	type(record_type type_) : kind(Record), record(type_) {}
	type(sub_type type_) : kind(Sub), sub(type_) {}
	type(union_type type_) : kind(Union), uni(type_) {}

	// copy ctor, move, op=, dctor is only because of the union, nothing special
	type(const type& other) { // noexcept
		kind = other.kind;
		switch (kind) {
			case Primitive: primitive = other.primitive; break;
			case Compound: compound = other.compound; break;
			case Record: record = other.record; break;
			case Sub: sub = other.sub; break;
			case Union: uni = other.uni; break;
			default: break; // throw 0;
		}
	}
	type(type&& other) noexcept {
		kind = other.kind;
		switch (kind) {
			case Primitive: primitive = std::move(other.primitive); break;
			case Compound: compound = std::move(other.compound); break;
			case Record: record = std::move(other.record); break;
			case Sub: sub = std::move(other.sub); break;
			case Union: uni = std::move(other.uni); break;
			default: break; // throw 0;
		}
	}
	// TODO: suboptimal for this, make this a copy instead (or a move)
	//type& operator=(type other) { // noexcept 
	//	using std::swap;
	//	kind = other.kind;
	//	switch (kind) {
	//		case Primitive: swap(primitive, other.primitive); break;
	//		case Compound: swap(compound, other.compound); break;
	//		case Record: swap(record, other.record); break;
	//		case Sub: swap(sub, other.sub); break;
	//		case Union: swap(uni, other.uni); break;
	//		default: break; // throw 0;
	//	}
	//	return *this;
	//}
	type& operator=(const type& other) { // noexcept 
		kind = other.kind;
		switch (kind) {
			case Primitive: primitive = other.primitive; break;
			case Compound: compound = other.compound; break;
			case Record: record = other.record; break;
			case Sub: sub = other.sub; break;
			case Union: uni = other.uni; break;
			default: break; // throw 0;
		}
		return *this;
	}
	~type() {}

	inline bool operator<(const type& other) const {
		if (kind != other.kind) return kind < other.kind;
		switch (kind) {
			case Primitive: return primitive < other.primitive;
			case Compound: return compound < other.compound;
			case Record: return record < other.record;
			case Sub: return sub < other.sub;
			case Union: return uni < other.uni;
			default: return false; // throw 0;
		}
	}
	inline bool operator==(const type& other) const {
		if (kind != other.kind) return false;
		switch (kind) {
			case Primitive: return primitive == other.primitive;
			case Compound: return compound == other.compound;
			case Record: return record == other.record;
			case Sub: return sub == other.sub;
			case Union: return uni == other.uni;
			default: return false; // throw 0;
		}
	}
	inline bool operator!=(const type& r) const { return !operator==(r); }
	inline bool operator> (const type& r) const { return r.operator<(*this); }
	inline bool operator<=(const type& r) const { return !operator>(r); }
	inline bool operator>=(const type& r) const { return !operator<(r); }

	/* isempty, isEmpty, is_empty, empty() ? */
	inline bool isNone() const {
		return isPrimitive() && primitive.type == base_type::NONE;
	}
	/* 
	 check whether 2 types are sync compatible 
	 note: if one is primitive/NONE other can be anything (non-primitive too)
	*/
	inline bool isCompatible(const type& other) const {
		if (kind == other.kind || 
			isNone() ||
			other.isNone()) 
			return true;
		return false;
	}

	bool isPrimitive() const { return kind == Primitive; }
	bool isCompound() const { return kind == Compound; }
	bool isRecord() const { return kind == Record; }
	bool isSub() const { return kind == Sub; }
	bool isUnion() const { return kind == Union; }

	int_t get_chars() const {
		switch (kind) {
			case Primitive: return primitive.type == base_type::CHR ? 255 : 0;
			case Compound: 
			default:
				throw 0;
		}
	}
	int_t get_syms(size_t nsyms = 0) const {
		switch (kind) {
			case Primitive: return primitive.type == base_type::STR ? nsyms : 0;
			case Compound: 
			default:
				throw 0;
		}
	}
	size_t get_bits() const { 
		switch (kind) {
			case Primitive: return primitive.bitness;
			case Compound: return compound.get_bits();
			default: throw 0;
		}
	}
	size_t get_bits(size_t subarg) const {
		switch (kind) {
		case Primitive:
			if (subarg != 0) throw 0; // allow only 0 for primitives (?)
			return primitive.bitness;
		case Compound: return compound.get_bits(subarg);
		default: throw 0;
		}
	}
	//std::vector<size_t> get_bits_vector() const {
	//	switch (kind) {
	//		case Primitive: return { primitive.bitness };
	//		case Compound: return compound.get_bits_vector();
	//		default: throw 0;
	//	}
	//}
	base_type get_type() const {
		switch (kind) {
			case Primitive: return primitive.type;
			default: throw 0;
		}
	}
	base_type get_type(size_t subarg) const {
		switch (kind) {
			case Primitive: 
				if (subarg != 0) throw 0; // allow only 0 for primitives (?)
				return primitive.type;
			case Compound: return compound.get_type(subarg);
			default: throw 0;
		}
	}

	/* 
	 get all primitive types regardless of the kind (for 'viewing' only) 
	 (we need an interator for editing)
	*/
	primtypes get_types() const { 
		switch (kind) {
			case Primitive: return { primitive };
			case Compound: return compound.get_types();
			default: throw 0;
		}
	}


	//type_type ofType;
	//enum class type_type { Primitive, Compound, Record, Sub, Union } ofType;
	enum { Primitive, Compound, Record, Sub, Union } kind;
	// TODO: turned off for debugging. Also make union private, provide get_...
	//union {
		primitive_type primitive;
		compound_type compound;
		record_type record;
		sub_type sub;
		union_type uni;
	//};
};

typedef std::vector<type> vtypes;
typedef std::vector<type> argtypes;
//typedef primitive_type arg_type;
typedef type arg_type;

//template<typename T, typename... Args>
//struct compound_type {
//	std::tuple<Args...> types2;
//};

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
	int_t val; // , num
	arg_type type;
	tbl_arg arg;
	arg_info(int_t val_, arg_type type_, tbl_arg arg_ = { -1,0 }) //, int_t num_
		: val(val_), type(type_), arg(arg_) {} // num(num_), 
	inline bool operator<(const arg_info& other) const {
		return val < other.val;
		//if (val != other.val) return val < other.val;
		//return arg < other.arg;
	}
};

std::wostream& operator<<(std::wostream&, const alt_arg&);
std::wostream& operator<<(std::wostream&, const tbl_arg&);
std::wostream& operator<<(std::wostream&, const primitive_type&);
std::wostream& operator<<(std::wostream&, const arg_type&);
std::wostream& operator<<(std::wostream&, const argtypes&);
std::wostream& operator<<(std::wostream& os, const bitsmeta& bm);
//bool operator<(const alt_arg& aarg, const tbl_arg& ta);

#endif // __TYPES_H__