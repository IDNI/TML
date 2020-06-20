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

typedef std::vector<size_t> sizes;

/* argument type's base-type enum */
//enum class basetype : std::uint8_t { NONE = 0, INT, CHR, STR };
enum class base_type { NONE = 0, INT, CHR, STR };

// D: make this just an int_t, lower bits for type + bitness the rest.
struct arg {
	static constexpr int_t none = -1;
	static constexpr size_t zero = 0;
	//static constexpr size_t none = 0;
	static bool is_zero(int_t arg) { return arg == none || arg == 0; }
	// == none || == 0 ? 0 : arg
	static size_t get_zero_based(int_t arg) { return is_zero(arg) ? 0 : arg; }
};

struct multi_arg {
	ntable tab;
	size_t arg;
	/* 
	 this is arg within arg, like for compounds (sequential id of a primitive)
	 - it's normally '0' for all, and shouldn't disrupt non-compounds, sort etc.
	*/
	//size_t subarg;
	int_t subarg;
	sizes path;
	enum spec_val { None, Size, Element, Sum, } special = spec_val::None;

	multi_arg(ntable tab_, size_t arg_, int_t subarg_, sizes path_, 
			  spec_val special_ = spec_val::None)
		:tab(tab_), arg(arg_), subarg(subarg_), path(path_), special{special_}{}
	multi_arg(size_t arg_, int_t subarg_, sizes path_)
		: tab(-1), arg(arg_), subarg(subarg_), path(path_) {}
	explicit multi_arg(const alt_arg&);
	explicit multi_arg(const vm_arg&);
	static multi_arg get_empty() { 
		return {-1, arg::zero, arg::none, {}}; 
	}
};
inline bool operator<(const multi_arg& l, const multi_arg& r) {
	if (l.tab != r.tab) return l.tab < r.tab;
	if (l.arg != r.arg) return l.arg < r.arg;
	if (l.subarg != r.subarg) return l.subarg < r.subarg;
	// ignore path, as subarg is enough to identify
	if (l.path != r.path) {
		((void)l);
	}
	return l.subarg < r.subarg;
	//return l.path < r.path;
}
inline bool operator==(const multi_arg& l, const multi_arg& r) {
	return	l.tab == r.tab && 
			l.arg == r.arg && 
			l.subarg == r.subarg &&
			true; // l.path == r.path;
}
inline bool operator!=(const multi_arg& l, const multi_arg& r)
{return !operator==(l, r);}
inline bool operator> (const multi_arg& l, const multi_arg& r)
{return operator<(r, l);}
inline bool operator<=(const multi_arg& l, const multi_arg& r)
{return !operator>(l, r);}
inline bool operator>=(const multi_arg& l, const multi_arg& r)
{return !operator<(l, r);}


struct primitive_type {
	primitive_type() : type(base_type::NONE), bitness(0) {}
	primitive_type(base_type type_, size_t bits) : type(type_), bitness(bits) {}
	primitive_type(base_type type_, size_t bits, int_t num) 
		: type(type_), bitness(bits), num(num) {}
	primitive_type(size_t bits) : type(base_type::NONE), bitness(bits), num(0){}

	inline bool isNone() const { return type == base_type::NONE; }
	int_t get_chars() const { return type == base_type::CHR ? 255 : 0; }
	int_t get_syms(size_t nsyms = 0) const 
	{ return type == base_type::STR ? nsyms : 0; }
	void set_bitness(size_t bits) { bitness = bits; }
	void set_num(int_t num_) { num = num_; }
	int_t get_null() const { return (1 << bitness) - 1; }
	//static primitive_type get_empty() { return {}; }

	base_type type = base_type::NONE;
	size_t bitness = 0;
	// we need to track exact 'nums' for the range leq (bits are not enough).
	int_t num = 0;
};
// TODO: move this out for all here, make them free, I was just lazy
inline bool operator<(const primitive_type& l, const primitive_type& r) { 
	if (l.type != r.type) return l.type < r.type;
	if (l.bitness != r.bitness) return l.bitness < r.bitness;
	return l.num < r.num;
}
inline bool operator==(const primitive_type& l, const primitive_type& r) { 
	return l.type == r.type && l.bitness == r.bitness && l.num == r.num;
}
inline bool operator!=(const primitive_type& l, const primitive_type& r)
{return !operator==(l, r);}
inline bool operator> (const primitive_type& l, const primitive_type& r)
{return operator<(r, l);}
inline bool operator<=(const primitive_type& l, const primitive_type& r)
{return !operator>(l, r);}
inline bool operator>=(const primitive_type& l, const primitive_type& r)
{return !operator<(l, r);}


typedef std::vector<primitive_type> primtypes;
typedef std::vector<std::pair<primitive_type, sizes>> primtype_paths;

struct type;
typedef std::vector<type> vtypes;

/* compound type (only has primitive types?) */
struct compound_type {
	compound_type() {} // only if we remove union
	compound_type(vtypes types_, bool isroot_ = false, bool bitaligned_ = false)
		: types(types_), isroot(isroot_), bitaligned(bitaligned_),
		  alignment{ make_alignment(bitaligned, types) } {
		if (!check_sub_types_noalign()) throw std::runtime_error("aligned?");
		//sumOfBits = calc_sum();
	}
	compound_type(const compound_type& original, bool isroot_, bool bitaligned_)
		: types(original.types), isroot(isroot_), bitaligned(bitaligned_),
		alignment{ make_alignment(bitaligned, types) } {
		//alignment{ bitaligned ? BSR(types.size()) : 0 } {
		if (!check_sub_types_noalign()) throw std::runtime_error("aligned?");
		(void)isroot;
	}

	static size_t calc_sum(const vtypes& types);
	size_t get_bits() const {
		//if (sumOfBits && sumOfBits != calc_sum(types))
		//	throw std::runtime_error("sumOfBits?");
		//return sumOfBits = calc_sum(types);
		// test first, not sure of reinit
		return sumOfBits = (sumOfBits ? sumOfBits : calc_sum(types));
	}
	size_t get_bits_w_align() const { 
		return get_bits() + alignment.bitness;
	}
	static size_t calc_no_primitives(const vtypes& types);
	size_t get_no_primitives() const {
		//if (sumOfPrimitives && sumOfPrimitives != calc_no_primitives(types))
		//	throw std::runtime_error("sumOfPrimitives?");
		//return sumOfPrimitives = calc_no_primitives(types);
		return sumOfPrimitives =
			(sumOfPrimitives ? sumOfPrimitives : calc_no_primitives(types));
	}
	//size_t get_bits(size_t subarg) const;
	vtypes get_types() const { return types; }
	primtypes get_primitives() const;
	primtype_paths get_primitives(sizes path) const;
	//const type& get_sub_type(size_t idx) const;

	bool isAllNone() const;

	bool has_alignment() const { return alignment.bitness > 0; }
	primitive_type& get_alignment() { return alignment; }
	const primitive_type& get_alignment() const { return alignment; }
	size_t get_alignment_bits() const { return alignment.bitness; }

	bool check_sub_types_noalign() const;

	static compound_type trim_align(compound_type original);
	static void set_align_bits_flag(bool alignbits) { align_bits = alignbits; }

	friend struct type;
	friend bool operator<(const compound_type& l, const compound_type& r);
	friend bool operator==(const compound_type& l, const compound_type& r);

private:
	void reset_alignment() {
		isroot = bitaligned = false;
		alignment.bitness = 0;
		reset();
	}
	void reset() { 
		sumOfBits = 0;
		sumOfPrimitives = 0;
	}
	void init() {
		calc_sum(types);
		calc_no_primitives(types);
	}

	inline static size_t BSR(size_t num) {
		size_t bits;
		for (bits = 0; num > 0; num >>= 1) ++bits;
		return bits;
	}
	inline static primitive_type make_alignment(bool bitaligned, vtypes types) {
		return bitaligned && align_bits ? BSR(types.size()) : 0;
	}

	vtypes types;
	bool isroot = false;
	bool bitaligned = false;
	primitive_type alignment{ base_type::NONE, 0};
	mutable size_t sumOfBits = 0;
	mutable size_t sumOfPrimitives = 0;
	static bool align_bits;
};
inline bool operator<(const compound_type& l, const compound_type& r)
{ return l.types < r.types; }
inline bool operator==(const compound_type& l, const compound_type& r)
{ return l.types == r.types; }
inline bool operator!=(const compound_type& l, const compound_type& r)
{return !operator==(l, r);}
inline bool operator> (const compound_type& l, const compound_type& r)
{return operator<(r, l);}
inline bool operator<=(const compound_type& l, const compound_type& r)
{return !operator>(l, r);}
inline bool operator>=(const compound_type& l, const compound_type& r)
{return !operator<(l, r);}

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
	type() : kind(Primitive), primitive() {} // needed for bitsmeta types(len)
	type(base_type type_, size_t bits):kind(Primitive), primitive{type_, bits}{}
	type(base_type type_, size_t bits, int_t num)
		: kind(Primitive), primitive{type_, bits, num} {}
	type(primitive_type type_, sizes sig_ = {})
		//: type(type_.type, type_.bitness), sig(move(sig_)) {
		: kind(Primitive), primitive{type_}, sig(move(sig_)) {
		if (!type_.isNone() && !sig_.empty())
			throw std::runtime_error("only none-primitive can have sig!");
	}
	type(compound_type type_, sizes sig_ = {})
		: kind(Compound), compound(type_), sig(move(sig_)) {}
	type(record_type type_) : kind(Record), record(type_) {}
	type(sub_type type_) : kind(Sub), sub(type_) {}
	type(union_type type_) : kind(Union), uni(type_) {}

	// copy ctor, move, op=, dctor is only because of the union, nothing special
	type(const type& other); // noexcept
	type(type&& other) noexcept;
	//type& operator=(type other);
	type& operator=(const type& other); // noexcept 
	~type() {}

	// - arg.subarg - is what was idx - but into get_primitives()
	// - arg.path - points to a direct hierarchy drill-down to get to it
	type& operator[](multi_arg arg) {
		if (arg.path.empty())
			return get_sub_type(arg.subarg);
		check_arg_path(arg);
		return get_idx(arg.path);
	}

	const type& operator[](multi_arg arg) const {
		if (arg.path.empty())
			return get_sub_type(arg.subarg);
		check_arg_path(arg);
		return get_idx(arg.path);
	}

	// TODO: make a template for code deduplication or so
	type& get_idx(sizes path, size_t level = 0);
	const type& get_idx(sizes path, size_t level = 0) const;

	// isempty, isEmpty, is_empty, empty() ?
	inline bool isNone() const {
		return isPrimitive() && primitive.type == base_type::NONE;
	}
	inline bool isAllNone() const {
		return 
			(isPrimitive() && primitive.isNone()) || 
			(isCompound() && compound.isAllNone());
	}

	// check whether 2 types are sync compatible 
	// note: if one is primitive/NONE other can be anything (non-primitive too)
	bool isCompatible(const type& other, bool optimistic = false) const;
	static bool isCompatible(
		const vtypes& l, const vtypes& r, const multiints& multivals, 
		bool optimistic = false);
	static bool isCompatible(
		const vtypes& l, const multiints& multivals, bool optimistic = false);
	static bool isSigCompatible(
		const type& l, const type& r, bool optimistic = false);

	bool isPrimitive() const { return kind == Primitive; }
	bool isCompound() const { return kind == Compound; }
	bool isRecord() const { return kind == Record; }
	bool isSub() const { return kind == Sub; }
	bool isUnion() const { return kind == Union; }

	void ensureCompound(const std::string& msg) const 
	{ if (!isCompound()) throw std::runtime_error(msg); }
	void ensureCompound() const 
	{ if (!isCompound()) throw std::runtime_error("compound expected!"); }

	int_t get_chars() const;
	int_t get_syms(size_t nsyms = 0) const;
	inline size_t get_bits(bool walign = false) const { 
		switch (kind) {
			case Primitive: return primitive.bitness;
			case Compound: 
				return walign ?
					compound.get_bits_w_align() : compound.get_bits();
			default: throw 0;
		}
	}
	inline size_t get_bits_w_align() const { return get_bits(true); }

	inline size_t get_no_primitives() const {
		switch (kind) {
			case Primitive: return 1;
			case Compound: 
				return compound.get_no_primitives();
			default: throw 0;
		}
	}

	size_t get_start(const multi_arg& arg) const;
	size_t get_compound_start(int_t subarg) const; // size_t subarg

	vtypes get_types() const;
	primtypes get_primitives() const;
	primtype_paths get_primitives(sizes path) const;
	size_t sizeof_primitives() const;
	void calc_primes_map();

	primitive_type& get_primitive(size_t idx);
	type& get_sub_type(int_t idx); // size_t idx
	const type& get_sub_type(int_t idx) const; // size_t idx
	void init();
	bool can_discard_path(multi_arg) const;
	bool check_arg_path(multi_arg arg) const;
	type& get_tail_type();
	type& get_tail_compound();
	vtypes& get_tail_types();
	static vtypes& get_tail_types(vtypes& types);
	static vtypes& get_tail_types(vtypes& types, size_t level);

	//sizes generate_sig();
	static sizes normalize_sig(sizes sig);

	bool has_alignment() const 
	{ return isCompound() && compound.has_alignment(); }
	primitive_type& get_alignment() { ensureCompound(); 
		return compound.get_alignment();
	}
	const primitive_type& get_alignment() const { ensureCompound();
		return compound.get_alignment();
	}
	size_t get_alignment_bits() const { ensureCompound(); 
		return compound.get_alignment_bits();
	}
	bool check_sub_types_noalign() const {
		return !isCompound() || compound.check_sub_types_noalign();
	}

	static type trim_align(type original) {
		if (!original.isCompound()) return original;
		original.compound.reset_alignment();
		return type{
			compound_type::trim_align(std::move(original.compound)), 
			original.sig};
	}

	ints get_not_null_vals(ints vals) const {
		ints validvals;
		for (const auto& it : *this) {
			if (it.get_type().get_null() == vals[it.id]) break;
			validvals.push_back(vals[it.id]);
		}
		return validvals;
	}
	const type& get_right_part(size_t size) const {
		if (size == 0) throw std::runtime_error("get_right_part: ...");
		size_t left = get_no_primitives() - size;
		if (left <= 0) return *this;
		for (auto iter = (*this).begin(); iter != (*this).end(); ++iter) {
			auto& it = *iter;
			if (it.id == left) {
				if (size==1 || iter.stack.size() == 1)
					return iter.stack.rbegin()[0].container;
					//return (iter.stack[0]).container; // throw 0
				// TODO: this assumes lot of things, just a list a(b(c(d(e(...
				return iter.stack.rbegin()[1].container;
			}
		}
		throw std::runtime_error("get_right_part: shouldn't be here?");
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

	sizes sig;
	std::vector<sizes> mprimes;

public:

	template<bool isConst>
	struct iterator_data {
		using T = type;
		using TValue = primitive_type;
		using container_type = T; // same in our case, or make it input param
		using difference_type = std::ptrdiff_t; // could be size_t but don't care
		using size_type = size_t;
		using value_type = TValue;
		using reference = typename std::conditional_t<isConst,
			TValue const&, TValue&>;
		using pointer = typename std::conditional_t<isConst,
			TValue const*, TValue*>;
		//using container_type_reference = T const&;
		using container_type_reference = typename std::conditional_t<isConst,
			T const&, T&>;

		iterator_data() = delete; // default;
		iterator_data(container_type_reference container_, size_t startbit_ = 0,
			size_t level_ = 0, sizes path_ = {}, size_t id_ = 0, size_t bits_=0,
			int_t arg_ = arg::none)
			: container(container_), startbit(startbit_), level(level_), 
			  path(path_), id(id_), bits(bits_), arg(arg_) {}

		reference get_type() const {
			if (container.isCompound()) throw std::runtime_error("type: prim?");
			return container.primitive;
		}
		reference get_type() {
			if (container.isCompound()) throw std::runtime_error("type: prim?");
			return container.primitive;
		}

		container_type_reference container;
		size_t startbit;
		size_t level;
		sizes path;
		size_t i;
		size_t id;
		size_t bits;
		int_t arg;
		int_t val;
	private:
		//size_t i;
	};

	// iterator implementation...
	//template<typename T, bool isConst>
	template<bool isConst>
	struct iterator_t {
		using T = type;
		using TValue = primitive_type;
		using container_type = T; // same in our case, or make it input param
		using difference_type = std::ptrdiff_t; // could be size_t but don't care
		using size_type = size_t;
		using value_type = TValue;
		//using const_pointer = const T*;
		//using const_reference = const T&;
		using reference = typename std::conditional_t<isConst, 
			TValue const&, TValue&>;
		using pointer = typename std::conditional_t<isConst, 
			TValue const*, TValue*>;
		//using container_type_reference = T const&;
		using container_type_reference = typename std::conditional_t<isConst,
			T const&, T&>;
		using data_type_reference = typename std::conditional_t<isConst,
			const iterator_data<isConst>&, iterator_data<isConst>&>;
		using data_type_pointer = typename std::conditional_t<isConst,
			const iterator_data<isConst>*, iterator_data<isConst>*>;
		using iterator_category = std::forward_iterator_tag;
		//random_access_iterator_tag;

		friend type;

		iterator_t() = default;
		iterator_t(container_type_reference container, size_t startbit_ = 0,
				   size_t level_ = 0, sizes path_ = {}, size_t id_ = 0,
				   size_t bits_ = 0, int_t arg_ = 0) :
			ismulti(container.isCompound() && container.compound.types.size()>1),
			stack{{container, startbit_, level_, path_, id_, bits_, arg_}},
			vals() {}
		iterator_t(container_type_reference container, ints vals_) :
			//ismulti(container.isCompound() && container.compound.types.size()>1),
			ismulti(vals_.size() > 1),
			stack{ {container, 0, 0, {}, 0, 0, 0} },
			vals(vals_) {}
		iterator_t(const iterator_t&) = default;

		template<bool isConst_ = isConst, class = std::enable_if_t<isConst_>>
		iterator_t(const iterator_t<false>& rhs) : //<T, false>
			stack(rhs.stack) {}

		iterator_data<isConst>& data() { return stack.back(); }
		const iterator_data<isConst>& data() const { return stack.back(); }

		iterator_t& begin() {
			begin(stack.back());
			return *this;
		}

		void begin(iterator_data<isConst>& data) {
			auto& 
				[container, startbit, level, path, i, id, bits, arg, val]= data;
			if (level != path.size())
				throw std::runtime_error("iterator: level");
			//path.push_back(0);
			//path[level] = 0;
			// need it here in case var/0
			arg = id || ismulti ? (int_t)id : arg::none;
			// vals 'trick' should work for a) full-type or b) current mid-comp
			if (!vals.empty() && !(vals.size() > id))
				throw std::runtime_error("begin: vals, types out of sync");
			// just non-empty vals[id] should cover all, id is 0 so vals[0],
			// and should be < 0, if prims > 1 & vals.size==1 & const => error
			// if prims==1 + ...=> that's in sync & is going to unwind naturally
			// even more, just vals/primes size==1 and const will skip primitive
			// and will return undefined primitive, while we do need it!
			if (!vals.empty() && 
				vals[id] < 0 &&
				((level==0 && vals.size()==1) || id == vals.size()-1)) {
				if (isvar) throw std::runtime_error("begin: var in progress??");
				if (level == 0) // only if 0-level, or path's set by comp above
					path.push_back(0);
				isvar = true;
				// if we have just ?x for comp, treat it the same as primitives
				// set bits / val and done (startbit is 0) - to finish in next.
				// if taking container bits, it could be root & have align bits
				// (poss uses iterator and most of the time we need real bits)
				bits = container.get_bits_w_align(); // full / all bits
				val = vals[id];
				// we don't need primitive in this case, so shouldn't rely on it
				return;
			}
			if (container.isPrimitive()) {
				if (level == 0) // only if 0-level, or path's set by comp above
					path.push_back(0);
				//path[level] = 0;
				//arg = id || ismulti ? id : arg::none;
				bits = container.primitive.bitness; // we need this here
				if (!vals.empty()) {
					if (!(vals.size() > id))
						throw std::runtime_error("begin: vals, types mismatch");
					val = vals[id];
				}
			} else if (container.isCompound()) {
				// not used, but here is the right time, at init
				bits = container.compound.get_bits_w_align();
				i = 0;
				path.push_back(0);
				// end() shouldn't happen, empty? nothing to unwind, we're last
				if (!(i < container.compound.types.size())) return;
				container_type_reference type = (container.compound.types[i]);
				path[level] = i;
				stack.emplace_back(
					type, startbit, level + 1, path, id, bits, arg);
				begin(stack.back());
			} else throw std::runtime_error("iterator: kind...");
		}

		void next() { next(stack.back()); }
		void next(iterator_data<isConst>& data) {
			auto&
				[container, startbit, level, path, i, id, bits, arg, val]= data;
			// only do isvar if previously set in begin (same level)
			// this is important to be in sync, startbit, level, everything
			if (isvar) {
				if (!vals.empty() && !(vals.size() > id))
					throw std::runtime_error("begin: vals, types out of sync");
				if (vals.empty() || vals[id] >= 0)
					throw std::runtime_error("begin: var but not??");
				isvar = false; // reset back to be in sync if any more
				// we're done but it's like primitive, we gotta to advance ptrs
				startbit += container.get_bits_w_align();
				++id; // only primitive can update count, and inc only on exit
			}
			else if (container.isPrimitive()) {
				startbit += container.primitive.bitness;
				// this is ok, we're done w/ primitive, it's for parent on exit
				++id; // only primitive can update count, and inc only on exit
				// end() // unwind at exit...
			} else if (container.isCompound()) {
				if (!(i < container.compound.types.size()))
					throw std::runtime_error("++: compound i past end()?");
				// i has finished (begin starts 0 i and so on)...
				startbit += container.compound.types[i].get_bits_w_align();
				++i;
				if (i < container.compound.types.size()) {
					container_type_reference type = container.compound.types[i];
					path[level] = i;
					stack.emplace_back(
						type, startbit, level + 1, path, id, bits, arg);
					// we're starting new type, so begin, next is called for 
					// last on the stack, so we'll never invoke it manually
					begin(stack.back());
					// we could set startbit this way, it's 'safer':)
					//for (int istack = 0; istack < stack.size() - 1; ++istack)
					//	stack[istack].startbit = stack.back().startbit;
					return;
				}
				// end(), unwind at exit //bits = container.compound.get_bits();
			} else throw std::runtime_error("iterator: kind...");

			if (stack.size() > 1) {
				// unwind if there're nodes above
				size_t idx = id; // save it...
				//size_t startbit_ = startbit;
				//size_t bits_ = bits;
				stack.pop_back(); // is ok to del self? no vars're used any more
				// we always update the 'parent' on exit, so it's maintained...
				stack.back().id = idx;
				next(); // call back the parent again, as we hit end here...
			} else { // we're first/last and done (end())
				// bits could be zero (before the inference), types are always>0
				isend = true;
				// bits are always set to >0 at begin (and for all containers),
				// (we can't have zero types or zero bits, anywhere, and even if
				// it'd be possible, 0 bits is reason enough to exit)
				// reset to 0 to mark this as finished/end()
				//bits = 0;
				// data().startbit == data().type().bitness - is wrong, or maybe
				// not, as we try to unwind, back up, we'll end up at 0-type,
				// its startbit was 0 to start w/ and type bitness is full bits,
				// should equal to startbit at end(), interesting (bug not bug).
			}
		}

		// shows if iterator is valid or not (basicaly at end()).
		// it's used by == != to compare it to end(), if both false => equals
		operator bool() const {
			// - the only 'right' state is 'sitting' at a primitive data/type.
			//   (or on a ?var val on a compound - as an exception)
			// - begin always puts us in the 'right' place, and init/advances to
			//   that first primitive. If that's the only one, we're done.
			// - if var/0-val vals, we only have comp begin, on next we're done.
			// - begin is done at ctor time, this compare comes before next().
			return stack.empty() ||									// end()
				   isend ||											// has ended
				   (!isvar && data().container.isCompound())		// !ok state
				? false : true;
		}

		//reference operator*() const {}
		data_type_reference operator*() const { 
			if (stack.empty() || 
				isend ||
				(!isvar && data().container.isCompound()))
				throw std::runtime_error("* on end()?");
			return stack.back(); // .container.primitive;
		}
		data_type_reference operator*() {
			if (stack.empty() || 
				isend ||
				(!isvar && data().container.isCompound()))
				throw std::runtime_error("* on end()?");
			return stack.back(); // .container.primitive;
		}
		pointer operator->() const { return &operator*(); }

		iterator_t& operator++() {
			next();
			return *this;
		}
		iterator_t operator++(int) {
			iterator_t temp(*this);
			operator++(); // ++(*this);
			return temp;
		}

		// param needs to be different from the class one (for friends)
		template<bool const_> friend bool operator==(
			const iterator_t<const_>& lhs, const iterator_t<const_>& rhs);
		template<bool const_> friend bool operator!=(
			const iterator_t<const_>& lhs, const iterator_t<const_>& rhs);

	private:
		bool ismulti;
		std::vector<iterator_data<isConst>> stack;
		ints vals;
		bool isend = false;
		bool isvar = false;
	};

	using iterator = type::iterator_t<false>; // type, 
	using const_iterator = type::iterator_t<true>; // type, 

	iterator begin() { return iterator(*this).begin(); }
	iterator begin(ints vals) { return iterator(*this, vals).begin(); }
	iterator end() { return iterator(); }
	const_iterator begin() const { return const_iterator(*this).begin(); }
	const_iterator begin(ints vals) const 
	{ return const_iterator(*this, vals).begin(); }
	const_iterator end() const { return const_iterator(); }
	const_iterator cbegin() const { return const_iterator(*this).begin(); }
	const_iterator cend() const { return const_iterator(); }
};

// add type constraints
// , typename std::enable_if_t<std::is_same_v<type, std::remove_reference_t<T>>>* = nullptr
// , typename std::enable_if_t<std::is_same_v<T, type>, int> =0
template<typename T>
struct type_vals {
	//using T = type;
	//using reference = typename std::conditional_t<isConst, const T&, T&>;
	//reference type;
	static constexpr bool isconst = std::is_const<T>::value;
	//using iterator = type::iterator_t<std::is_const<T>::value>;
	//using const_iterator = type::iterator_t<std::is_const<T>::value>;
	using iterator = type::iterator_t<isconst>;
	T& type_;
	ints vals;
	type_vals(T& type_, ints vals_) :type_(type_), vals(vals_) {}
	iterator begin() { return iterator(type_, vals).begin(); }
	iterator end() { return iterator(); }
	iterator begin() const { return iterator(type_, vals).begin(); }
	iterator end() const { return iterator(); }
	//type::const_iterator begin() const
	//{ return type::const_iterator(type, vals).begin(); }
	//type::const_iterator end() const { return type::const_iterator(); }
};

template<bool isConst>
inline bool operator==(
	const type::iterator_t<isConst>& lhs, const type::iterator_t<isConst>& rhs){
	if (!lhs && !rhs) return true;
	if (!lhs || !rhs) return false;
	return (lhs.data().container == rhs.data().container) &&
		   (lhs.data().path == rhs.data().path) &&
		   (lhs.data().container.isPrimitive() == 
			   rhs.data().container.isPrimitive()) &&
		   (lhs.data().container.primitive == rhs.data().container.primitive);
}

template<bool isConst>
inline bool operator!=(
	const type::iterator_t<isConst>& lhs, const type::iterator_t<isConst>& rhs){
	return !(lhs==rhs);
}

inline bool operator<(const type& l, const type& r) {
	if (l.kind != r.kind) return l.kind < r.kind;
	if (l.sig != r.sig) return l.sig < r.sig;
	switch (l.kind) {
		case type::Primitive: return l.primitive < r.primitive;
		case type::Compound: return l.compound < r.compound;
		case type::Record: return l.record < r.record;
		case type::Sub: return l.sub < r.sub;
		case type::Union: return l.uni < r.uni;
		default: return false;
	}
}
inline bool operator==(const type& l, const type& r) {
	if (l.kind != r.kind) return false;
	if (l.sig != r.sig) return false;
	switch (l.kind) {
		case type::Primitive: return l.primitive == r.primitive;
		case type::Compound: return l.compound == r.compound;
		case type::Record: return l.record == r.record;
		case type::Sub: return l.sub == r.sub;
		case type::Union: return l.uni == r.uni;
		default: return false;
	}
}
inline bool operator!=(const type& l, const type& r) {return !operator==(l, r);}
inline bool operator> (const type& l, const type& r) {return operator<(r, l);}
inline bool operator<=(const type& l, const type& r) {return !operator>(l, r);}
inline bool operator>=(const type& l, const type& r) {return !operator<(l, r);}


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
	//size_t subarg;
	int_t subarg;
	tbl_arg(ntable tab_, size_t arg_, int_t subarg_ = 0)
		: tab(tab_), arg(arg_), subarg(subarg_) {}
	tbl_arg(size_t arg_, int_t subarg_)
		: tab(-1), arg(arg_), subarg(subarg_) {}
	explicit tbl_arg(const alt_arg&);
	//explicit tbl_arg(const vm_arg&);
	static tbl_arg get_empty() { return {-1, arg::zero, arg::none}; }
};
inline bool operator<(const tbl_arg& l, const tbl_arg& r) {
	if (l.tab != r.tab) return l.tab < r.tab;
	if (l.arg != r.arg) return l.arg < r.arg;
	return l.subarg < r.subarg;
}
inline bool operator==(const tbl_arg& l, const tbl_arg& r) {
	return l.tab == r.tab && l.arg == r.arg && l.subarg == r.subarg;
}
inline bool operator!=(const tbl_arg& l, const tbl_arg& r)
{return !operator==(l, r);}
inline bool operator> (const tbl_arg& l, const tbl_arg& r)
{return operator<(r, l);}
inline bool operator<=(const tbl_arg& l, const tbl_arg& r)
{return !operator>(l, r);}
inline bool operator>=(const tbl_arg& l, const tbl_arg& r)
{return !operator<(l, r);}

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
	//size_t subarg;
	int_t subarg;
	sizes path;
	//vm_arg() {} // needed for varmap, work around it
	vm_arg(size_t id, ntable tab, size_t arg, int_t subarg, sizes path)
		: id(id), tab(tab), arg(arg), subarg(subarg), path(path) {}
	vm_arg(size_t arg, int_t subarg, sizes path)
		: id(0), tab(-1), arg(arg), subarg(subarg), path(path) {}
	vm_arg(const multi_arg& other, size_t id)
		: id(id), tab(other.tab), arg(other.arg), subarg(other.subarg), 
		path(other.path) {}

	explicit operator multi_arg() const { return { tab, arg, subarg, path }; }
	bool is_empty() { return tab == -1; }
	// to avoid empty .ctor
	static vm_arg get_empty() { 
		return { 0, ntable(-1), arg::zero, arg::none, {} };
	}

};
inline bool operator<(const vm_arg& l, const vm_arg& r) {
	if (l.tab != r.tab) return l.tab < r.tab;
	if (l.arg != r.arg) return l.arg < r.arg;
	if (l.subarg != r.subarg) return l.subarg < r.subarg;
	if (l.path != r.path) return l.path < r.path;
	return l.id < r.id;
}
inline bool operator==(const vm_arg& l, const vm_arg& r) {
	return l.tab == r.tab &&
		   l.arg == r.arg &&
		   l.subarg == r.subarg &&
		   l.id == r.id &&
		   l.path == r.path;
}


struct alt_arg {
	ntable tab;
	int_t alt;
	size_t arg;
	/*
	 this is for (sub)arg within the arg, like for compounds (could be others)
	 - it's normally '0' for all, and shouldn't disrupt non-compounds, sort etc.
	*/
	//size_t subarg;
	int_t subarg;
	sizes path{};
	multi_arg::spec_val special = multi_arg::spec_val::None;
	alt_arg(ntable tab_, int_t alt_, size_t arg_,
			int_t subarg_ = 0, sizes path_ = {} ) 
		: tab(tab_), alt(alt_), arg(arg_), subarg(subarg_), path{path_} {}
	alt_arg(ntable tab_, int_t alt_, size_t arg_, multi_arg::spec_val special_)
		: tab(tab_), alt(alt_), arg(arg_), subarg(arg::none), path{}, 
		  special(special_) {}
	alt_arg(ntable tab_, int_t alt_, const alt_arg& other)
		: tab(tab_), alt(alt_), 
		  arg(other.arg), subarg(other.subarg), path{other.path} {}
	//alt_arg(const tbl_arg& other, int_t alt_ = -1) 
	//	: tab(other.tab), alt(alt_), arg(other.arg), subarg(other.subarg),
	//	  path{} {}
	// TODO: alt_arg needs no path?
	alt_arg(const multi_arg& other, int_t alt_) // = -1
		: tab(other.tab), alt(alt_), arg(other.arg), subarg(other.subarg),
		  path{other.path}, special{other.special} {}
	alt_arg(const vm_arg& other, int_t alt_ = -1)
		: tab(other.tab), alt(alt_), arg(other.arg), subarg(other.subarg),
		  path{other.path} {}

	explicit operator tbl_arg() const { return { tab, arg, subarg }; }
	explicit operator multi_arg() const { 
		return { tab, arg, subarg, path, special }; }
};
inline bool operator<(const alt_arg& l, const alt_arg& r) {
	if (l.tab != r.tab) return l.tab < r.tab;
	if (l.alt != r.alt) return l.alt < r.alt;
	if (l.arg != r.arg) return l.arg < r.arg;
	return l.subarg < r.subarg;
}
inline bool operator==(const alt_arg& l, const alt_arg& r) {
	return l.tab == r.tab &&
		l.alt == r.alt &&
		l.arg == r.arg &&
		l.subarg == r.subarg;
}

struct arg_info {
	int_t val; // , num
	arg_type type;
	tbl_arg arg;
	//arg_info(int_t val_, arg_type type_, tbl_arg arg_ = { -1,0 }) //, int_t num_
	arg_info(int_t val_, arg_type type_, tbl_arg arg_ = tbl_arg::get_empty())
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
