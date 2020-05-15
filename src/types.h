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
#include <functional>
#include "defs.h"

struct alt_arg;
struct vm_arg;
struct bitsmeta;
struct term;

/* argument type's base-type enum */
//enum class basetype : std::uint8_t { NONE = 0, INT, CHR, STR };
enum class base_type { NONE = 0, INT, CHR, STR };

// D: make this just an int_t, lower bits for type + bitness the rest.
struct arg {
	//static constexpr int_t none = -1;
	static constexpr size_t none = 0;
};

struct primitive_type {
	primitive_type() : type(base_type::NONE), bitness(0) {}
	primitive_type(base_type type_, size_t bits) : type(type_), bitness(bits) {}
	primitive_type(base_type type_, size_t bits, int_t num) 
		: type(type_), bitness(bits), num(num) {}

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

	// TODO: move this out, make them free, I was just lazy
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
		bitness = bits;
	}

	void set_num(int_t num_) {
		num = num_;
	}

	base_type type = base_type::NONE;
	size_t bitness = 0;
	// we need to track exact 'nums' for the range leq (bits are not enough).
	int_t num = 0;
};

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
	}

	size_t get_bits() const {
		return calc_sum(types);
	}

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

//struct field {
//	type type;
//	std::wstring name;
//};

/* record type */
struct record_type {
	inline bool operator<(const record_type&) const {
		return true; // types < other.types;
		//if (types != other.types) return types < other.types;
		//return names < other.names;
	}
	inline bool operator==(const record_type&) const {
		return true; // types < other.types;
		//return types == other.types && names == other.names;
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

	//std::vector<type> types;
	//std::vector<std::wstring> names;
};

struct type {
	//type(base_type type_, size_t bits):kind(Primitive),primitive{type_,bits}{}
	//type(primitive_type type_) : kind(Primitive), primitive(type_) {}
	type() : kind(Primitive), primitive() {} // needed for bitsmeta types(len)
	type(base_type type_, size_t bits):kind(Primitive), primitive{type_, bits}{}
	type(base_type type_, size_t bits, int_t num)
		: kind(Primitive), primitive{type_, bits, num} {}
	type(primitive_type type_, std::vector<size_t> sig_ = {}) 
		//: type(type_.type, type_.bitness), sig(move(sig_)) {
		: kind(Primitive), primitive{type_}, sig(move(sig_)) {
		if (!type_.isNone() && !sig_.empty())
			throw std::runtime_error("only none-primitive can have sig!");
	}
	type(compound_type type_, std::vector<size_t> sig_ = {})
		: kind(Compound), compound(type_), sig(move(sig_)) {}
	type(record_type type_) : kind(Record), record(type_) {}
	type(sub_type type_) : kind(Sub), sub(type_) {}
	type(union_type type_) : kind(Union), uni(type_) {}

	// copy ctor, move, op=, dctor is only because of the union, nothing special
	type(const type& other) { // noexcept
		kind = other.kind;
		sig = other.sig;
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
		sig = std::move(other.sig);
		switch (kind) {
			case Primitive: primitive = std::move(other.primitive); break;
			case Compound: compound = std::move(other.compound); break;
			case Record: record = std::move(other.record); break;
			case Sub: sub = std::move(other.sub); break;
			case Union: uni = std::move(other.uni); break;
			default: break; // throw 0;
		}
	}
	// TODO: suboptimal for this, make this a copy instead (or a move ass.)
	//type& operator=(type other) { // noexcept 
	//	using std::swap;
	//	kind = other.kind;
	//	sig = swap(other.sig);
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
		sig = other.sig;
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

	primitive_type& operator[](size_t idx) {
		switch (kind) {
			case Primitive: 
				if (idx > 0) 
					throw std::out_of_range("type.operator[]<primitive>: id > 0");
				return primitive;
			case Compound:
				if (idx >= compound.types.size())
					throw std::out_of_range("type.operator[]<compound>: id > 0");
				return compound.types[idx];
			default: 
				throw std::runtime_error("type[]: type kind not implemented?");
		}
	}
	const primitive_type& operator[](size_t idx) const {
		switch (kind) {
			case Primitive: 
				if (idx > 0) throw std::out_of_range("type[]<primitive>: id > 0");
				return primitive;
			case Compound:
				if (idx >= compound.types.size())
					throw std::out_of_range("type[]<compound>: id > 0");
				return compound.types[idx];
			default: 
				throw std::runtime_error("type[]: type kind not implemented?");
		}
	}

	/* isempty, isEmpty, is_empty, empty() ? */
	inline bool isNone() const {
		return isPrimitive() && primitive.type == base_type::NONE;
	}
	/* 
	 check whether 2 types are sync compatible 
	 note: if one is primitive/NONE other can be anything (non-primitive too)
	*/
	inline bool isCompatible(const type& other) const {
		if (!isSigCompatible(*this, other)) return false;
		if (kind == other.kind ||
			isNone() ||
			other.isNone()) {
			if (isPrimitive() ||
				other.isPrimitive() ||
				sig == other.sig || 
				sig.empty() || 
				other.sig.empty())
				return true;
			else if (isCompound()) { // sig-s are different, drill into it
				// sig-s are compatible so no need for this
				return true;
				//if (compound.types.size()!=other.compound.types.size())
				//	return false;
				//for (size_t i = 0; i != compound.types.size(); ++i) {
				//	if (compound.types[i].isNone() ||
				//		other.compound.types[i].isNone()) continue;
				//	if (compound.types[i].type == 
				//		other.compound.types[i].type) continue;
				//	// we don't care about bitness?
				//	return false;
				//}
				//if (normalize_sig(sig) == normalize_sig(other.sig))
				//	return true;
			}
			// should we throw here actually? throw runtime_error("");
			return false; //return true;
		}
		return false;
	}

	static bool isCompatible(
		const std::vector<type>& l, const std::vector<type>& r) {
		if (l.size() != r.size()) return false;
		for (size_t i = 0; i != l.size(); ++i)
			if (!l[i].isCompatible(r[i])) return false;
		return true;
	}

	static bool isSigCompatible(const type& l, const type& r) {
		if (l.sig == r.sig) return true; // in any case that's fine?
		if (l.isNone() && !l.sig.empty())
			return r.isCompound() && normalize_sig(l.sig)==normalize_sig(r.sig);
		if (r.isNone() && !r.sig.empty())
			return l.isCompound() && normalize_sig(l.sig)==normalize_sig(r.sig);
		if (l.isNone() || r.isNone()) return true; // none and no-sig, all fine
		if (l.isCompound() && r.isCompound()) {
			if (l.sig.empty() || r.sig.empty()) {
				// is this possible and allowed?
				return true; // false;
			}
			// sig-s are different, drill into it
			if (l.compound.types.size() != r.compound.types.size())
				return false;
			for (size_t i = 0; i != l.compound.types.size(); ++i) {
				if (l.compound.types[i].isNone() ||
					r.compound.types[i].isNone()) continue;
				// we don't care about bitness?
				if (l.compound.types[i].type ==
					r.compound.types[i].type) continue;
				return false;
			}
			if (normalize_sig(l.sig) == normalize_sig(r.sig))
				return true;
			// should we throw here actually? throw runtime_error("");
			return false;
		}
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
			if (subarg != arg::none) throw 0;
			return primitive.bitness;
		case Compound: return compound.get_bits(subarg);
		default: throw 0;
		}
	}
	size_t get_start(size_t subarg) const {
		switch (kind) {
			case Primitive:
			{
				if (subarg != arg::none) throw 0;
				return 0;
				break;
			}
			case Compound:
			{
				size_t startbit = 0;
				for (size_t i = 0; i != compound.types.size(); ++i) {
					const primitive_type& type = compound.types[i];
					if (i == subarg) return startbit;
					startbit += type.bitness;
				}
				throw 0;
				break;
			}
			default: throw 0;
		}
	}

	base_type get_type() const {
		switch (kind) {
			case Primitive: return primitive.type;
			default: throw 0;
		}
	}
	base_type get_type(size_t subarg) const {
		switch (kind) {
			case Primitive: 
				if (subarg != arg::none) throw 0;
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

	static std::vector<size_t> normalize_sig(std::vector<size_t> sig);

	struct iter {
		const ints& vals;
		bool is_multival;
		const primitive_type& type;
		int_t val;
		// usually a 'sub-argument' within the compound type
		size_t i;
		size_t startbit, bits;
		bool exit = false;
		iter(const ints& vals, bool ismulti, const primitive_type& type,
			 int_t val, size_t i, size_t startbit, size_t bits) :
			vals(vals), is_multival(ismulti), type(type), val(val), i(i),
			startbit(startbit), bits(bits) {}
		iter(const ints& vals, const primitive_type& type, size_t i, 
			 size_t startbit, size_t bits) : 
			vals(vals), is_multival(true), type(type), val(0), i(i),
			startbit(startbit), bits(bits) {}
	};
	
	/* 
	 poor men's iterator over all types within (mostly for compounds)... 
	 - predicate (lambda) should be (*)(type::iter) (or (iter&))
	*/
	template<typename _Predicate>
	void iterate(const ints& vals, _Predicate f, size_t tbits = 0) const {
		const primtypes& types = get_types();
		for (size_t i = 0, startbit = 0; i != vals.size(); ++i) {
			// if we have just ?x for comp, treat it the same as primitives
			size_t bits = vals.size() > 1 ? 
				types[i].bitness : 
				(tbits ? tbits : get_bits());
			bool is_multival = vals.size() > 1;
			size_t arg = i ? i : arg::none;
			f(iter{vals, is_multival, types[i], vals[i], arg, startbit, bits});
			startbit += bits;
		}
	}

	/*
	 poor men's iterator over all types within (mostly for compounds)...
	 - predicate (lambda) should be (*)(type::iter) (or (iter&))
	*/
	template<typename _Predicate>
	void iterate(_Predicate f) const {
		const primtypes& types = get_types();
		for (size_t i = 0, startbit = 0; i != types.size(); ++i) {
			size_t bits = types[i].bitness;
			size_t arg = i ? i : arg::none;
			iter it{ ints{}, types[i], arg, startbit, bits };
			f(it);
			if (it.exit) break;
			startbit += it.bits; //startbit += bits;
		}
	}

	/*
	 poor men's iterator over all types within (mostly for compounds)...
	 - predicate (lambda) should be (*)(type::iter) (or (iter&))
	*/
	template<typename T, typename _Predicate>
	static void iterate(const T& type, const ints& vals, _Predicate&& f) {
		const primtypes& types = type.get_types();
		for (size_t i = 0, startbit = 0; i != vals.size(); ++i) {
			// if we have just ?x for comp, treat it the same as primitives
			size_t bits = vals.size() > 1 ? types[i].bitness : type.get_bits();
			bool is_multival = vals.size() > 1;
			f(iter{ vals, is_multival, types[i], vals[i], i, startbit, bits });
			startbit += bits;
		}
	}

	//enum class type_type { Primitive, Compound, Record, Sub, Union } ofType;
	enum { Primitive, Compound, Record, Sub, Union } kind;

	// TODO: optimize this (mem), also make it private etc.
	// (poly vec or so, though we have too little types normally to bother)
	primitive_type primitive;
	compound_type compound;
	record_type record;
	sub_type sub;
	union_type uni;

	std::vector<size_t> sig;
};

typedef std::vector<type> vtypes;
typedef std::vector<type> argtypes;
typedef type arg_type;

//template<typename T, typename... Args>
//struct compound_type {
//	std::tuple<Args...> types2;
//};

struct tbl_arg {
	ntable tab;
	size_t arg;
	/* 
	 this is arg within arg, like for compounds 
	 - it's normally '0' for all, and shouldn't disrupt non-compounds, sort etc.
	*/
	size_t subarg;
	tbl_arg(ntable tab_, size_t arg_, size_t subarg_ = 0) 
		: tab(tab_), arg(arg_), subarg(subarg_) {}
	tbl_arg(size_t arg_, size_t subarg_)
		: tab(-1), arg(arg_), subarg(subarg_) {}
	explicit tbl_arg(const alt_arg&);
	explicit tbl_arg(const vm_arg&);
	inline bool operator<(const tbl_arg& other) const {
		if (tab != other.tab) return tab < other.tab;
		if (arg != other.arg) return arg < other.arg;
		return subarg < other.subarg;
		//return arg < other.arg;
	}
	inline bool operator==(const tbl_arg& other) const {
		return tab == other.tab && arg == other.arg && subarg == other.subarg;
	}
	inline bool operator!=(const tbl_arg& r) const { return !operator==(r); }
	inline bool operator> (const tbl_arg& r) const { return r.operator<(*this);}
	inline bool operator<=(const tbl_arg& r) const { return !operator>(r); }
	inline bool operator>=(const tbl_arg& r) const { return !operator<(r); }
};

typedef tbl_arg tbl_alt;

/*
 used for alt-s only (and vm mapping)
 - id - is an index into alt's types, i.e. the order # of alt's variable
   (it's 'flattened' list of vars, while header args could be much less)
 - tab, arg, subarg - is pointing to the actual table/arg/sub (header or body)
 - {alt,id} != {h.tab,arg} no longer true, one h arg could have many vars (subs)
*/
struct vm_arg {
	/* order id - what was the vm value / second arg before, i.e. vm[var] */
	size_t id;
	ntable tab;
	size_t arg;
	/*
	 this is for (sub)arg within the arg, like for compounds (could be others)
	 - it's normally '0' for all, and shouldn't disrupt non-compounds, sort etc.
	 (this is safe as first subarg can't be a var (only leafs as per the specs))
	 ??(- correction: none is -1, for ?x->compound (full arg map) vs )
	*/
	size_t subarg; // int_t subarg;
	//vm_arg() {} // needed for varmap, work around it
	vm_arg(size_t id, ntable tab, size_t arg, size_t subarg = arg::none)
		: id(id), tab(tab), arg(arg), subarg(subarg) {}
	vm_arg(size_t arg, size_t subarg) 
		: id(0), tab(-1), arg(arg), subarg(subarg) {}
	vm_arg(const tbl_arg& other, size_t id)
		: id(id), tab(other.tab), arg(other.arg), subarg(other.subarg) {}

	explicit operator tbl_arg() const { return { tab, arg, subarg }; }

	bool operator<(const vm_arg& other) const {
		if (tab != other.tab) return tab < other.tab;
		if (arg != other.arg) return arg < other.arg;
		if (subarg != other.subarg) return subarg < other.subarg;
		return id < other.id;
	}
	bool operator==(const vm_arg& other) const {
		return tab == other.tab &&
			   arg == other.arg &&
			   subarg == other.subarg &&
			   id == other.id;
	}

	bool is_empty() { return tab == -1; }

	/* to avoid empty .ctor */
	static vm_arg get_empty() { 
		return vm_arg{ 0, ntable(-1), arg::none, arg::none };
	}

};

struct alt_arg {
	ntable tab;
	int_t alt;
	size_t arg;
	/*
	 this is for (sub)arg within the arg, like for compounds (could be others)
	 - it's normally '0' for all, and shouldn't disrupt non-compounds, sort etc.
	*/
	size_t subarg;
	alt_arg(ntable tab_, int_t alt_, size_t arg_, size_t subarg_ = 0) 
		: tab(tab_), alt(alt_), arg(arg_), subarg(subarg_) {}
	alt_arg(const tbl_arg& other, int_t alt_ = -1) 
		: tab(other.tab), alt(alt_), arg(other.arg), subarg(other.subarg) {}
	alt_arg(const vm_arg& other, int_t alt_ = -1)
		: tab(other.tab), alt(alt_), arg(other.arg), subarg(other.subarg) {}

	explicit operator tbl_arg() const { return { tab, arg, subarg }; }

	bool operator<(const alt_arg& other) const {
		if (tab != other.tab) return tab < other.tab;
		if (alt != other.alt) return alt < other.alt;
		if (arg != other.arg) return arg < other.arg;
		return subarg < other.subarg;
	}
	bool operator==(const alt_arg& other) const {
		return tab == other.tab && 
			   alt == other.alt &&
			   arg == other.arg && 
			   subarg == other.subarg;
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

#endif // __TYPES_H__