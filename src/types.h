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
	//static constexpr int_t none = -1;
	static constexpr size_t none = 0;
};

struct multi_arg {
	ntable tab;
	size_t arg;
	/* 
	 this is arg within arg, like for compounds (sequential id of a primitive)
	 - it's normally '0' for all, and shouldn't disrupt non-compounds, sort etc.
	*/
	size_t subarg;
	sizes path;
	multi_arg(ntable tab_, size_t arg_, size_t subarg_, sizes path_)
		: tab(tab_), arg(arg_), subarg(subarg_), path(path_) {}
	multi_arg(size_t arg_, size_t subarg_, sizes path_)
		: tab(-1), arg(arg_), subarg(subarg_), path(path_) {}
	explicit multi_arg(const alt_arg&);
	explicit multi_arg(const vm_arg&);
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

	inline bool isNone() const { return type == base_type::NONE; }
	int_t get_chars() const { return type == base_type::CHR ? 255 : 0; }
	int_t get_syms(size_t nsyms = 0) const 
	{ return type == base_type::STR ? nsyms : 0; }
	void set_bitness(size_t bits) { bitness = bits; }
	void set_num(int_t num_) { num = num_; }

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
	compound_type(vtypes types_) : types(types_) { // std::move
		//sumOfBits = calc_sum();
	}

	static size_t calc_sum(const vtypes& types);
	size_t get_bits() const { return calc_sum(types); }
	//size_t get_bits(size_t subarg) const;
	vtypes get_types() const { return types; }
	primtypes get_primitives() const;
	primtype_paths get_primitives(sizes path) const;
	//const type& get_sub_type(size_t idx) const;

	vtypes types;
	//size_t sumOfBits = 0;
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
			}
			// should we throw here actually? throw runtime_error("");
			return false; //return true;
		}
		return false;
	}

	static bool isCompatible(
		const std::vector<type>& l, const std::vector<type>& r);

	static bool isSigCompatible(const type& l, const type& r);

	bool isPrimitive() const { return kind == Primitive; }
	bool isCompound() const { return kind == Compound; }
	bool isRecord() const { return kind == Record; }
	bool isSub() const { return kind == Sub; }
	bool isUnion() const { return kind == Union; }

	int_t get_chars() const;
	int_t get_syms(size_t nsyms = 0) const;
	inline size_t get_bits() const { 
		switch (kind) {
			case Primitive: return primitive.bitness;
			case Compound: return compound.get_bits();
			default: throw 0;
		}
	}

	size_t get_start(const multi_arg& arg) const;
	size_t get_compound_start(size_t subarg) const;

	vtypes get_types() const;
	primtypes get_primitives() const;
	primtype_paths get_primitives(sizes path) const;
	size_t sizeof_primitives() const;
	void calc_primes_map();

	primitive_type& get_primitive(size_t idx);
	type& get_sub_type(size_t idx);
	const type& get_sub_type(size_t idx) const;
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

	struct iter {
		const ints& vals;
		bool is_multival;
		const primitive_type& type;
		int_t val;
		// usually a 'sub-argument' within the compound type
		size_t i;
		size_t startbit, bits;
		bool exit = false;
		sizes path{};
		iter(const ints& vals, bool ismulti, const primitive_type& type,
			 const sizes& path, int_t val, size_t i, size_t startbit, 
			 size_t bits) :
			vals(vals), is_multival(ismulti), type(type), val(val), i(i),
			startbit(startbit), bits(bits), path(path) {}
		iter(const ints& vals, const primitive_type& type, const sizes& path, 
			 size_t i, size_t startbit, size_t bits) : 
			vals(vals), is_multival(true), type(type), val(0), i(i),
			startbit(startbit), bits(bits), path(path) {}
	};
	
	/* 
	 poor men's iterator over all types within (mostly for compounds)... 
	 - predicate (lambda) should be (*)(type::iter) (or (iter&))
	*/
	template<typename _Predicate>
	void iterate(const ints& vals, _Predicate f, size_t tbits = 0) const {
		const primtype_paths& types = get_primitives(sizes{});
		for (size_t i = 0, startbit = 0; i != vals.size(); ++i) {
			const primitive_type& type = types[i].first;
			const sizes& path = types[i].second;
			// if we have just ?x for comp, treat it the same as primitives
			size_t bits = vals.size() > 1 ? 
				type.bitness :
				(tbits ? tbits : get_bits());
			bool is_multi = vals.size() > 1;
			size_t arg = i ? i : arg::none;
			f(iter{vals, is_multi, type, path, vals[i], arg, startbit, bits});
			startbit += bits;
		}
	}

	/*
	 poor men's iterator over all types within (mostly for compounds)...
	 - predicate (lambda) should be (*)(type::iter) (or (iter&))
	*/
	template<typename _Predicate>
	void iterate(_Predicate f) const {
		const primtype_paths& types = get_primitives(sizes{});
		for (size_t i = 0, startbit = 0; i != types.size(); ++i) {
			const primitive_type& type = types[i].first;
			const sizes& path = types[i].second;
			size_t bits = type.bitness;
			size_t arg = i ? i : arg::none;
			iter it{ ints{}, type, path, arg, startbit, bits };
			f(it);
			if (it.exit) break;
			startbit += it.bits; //startbit += bits;
		}
	}

	template<typename _Predicate>
	void r_iterate(_Predicate f) {
		size_t startbit = 0;
		size_t level = 0;
		sizes path{};
		size_t id = 0;
		iterate(startbit, level, path, id, f);
	}

	template<typename _Predicate>
	void iterate(
		size_t& startbit, size_t level, sizes path, size_t& id, _Predicate f){
		if (level != path.size()) throw std::runtime_error("iterate: level");
		path.push_back(0);
		switch (kind) {
			case Primitive: 
				path[level] = 0;
				f(primitive, startbit, path, id); // level, 
				startbit += primitive.bitness;
				id++;
				return;
				break;
			case Compound:
			{
				size_t start = startbit;
				for (size_t i = 0; i != compound.types.size(); ++i) {
					type& type = compound.types[i];
					path[level] = i;
					size_t istart = startbit;
					type.iterate(startbit, level + 1, path, id, f);
					if (startbit != istart + type.get_bits()) {
						startbit = istart + type.get_bits();
						o::dump() <<
							L"startbit != istart + get_bits()" << std::endl;
					}
				}
				if (startbit != start + compound.get_bits()) {
					startbit = start + compound.get_bits();
					o::dump() << L"startbit != start + get_bits()" << std::endl;
				}
				return;
				break;
			}
			default: throw 0;
		}
	}

	/*
	 poor men's iterator over all types within (mostly for compounds)...
	 - predicate (lambda) should be (*)(type::iter) (or (iter&))
	*/
	template<typename T, typename _Predicate>
	static void iterate(const T& type, const ints& vals, _Predicate&& f) {
		const primtype_paths& types = type.get_primitives(sizes{});
		for (size_t i = 0, startbit = 0; i != vals.size(); ++i) {
			const primitive_type& primitive = types[i].first;
			const sizes& path = types[i].second;
			// if we have just ?x for comp, treat it the same as primitives
			size_t bits = vals.size() > 1 ? primitive.bitness : type.get_bits();
			bool is_multi = vals.size() > 1;
			f(iter{
				vals, is_multi, primitive, path, vals[i], i, startbit, bits});
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

	sizes sig;
	std::vector<sizes> mprimes;
};

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
	size_t subarg;
	tbl_arg(ntable tab_, size_t arg_, size_t subarg_ = 0) 
		: tab(tab_), arg(arg_), subarg(subarg_) {}
	tbl_arg(size_t arg_, size_t subarg_)
		: tab(-1), arg(arg_), subarg(subarg_) {}
	explicit tbl_arg(const alt_arg&);
	//explicit tbl_arg(const vm_arg&);
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
	size_t subarg; // int_t subarg;
	sizes path;
	//vm_arg() {} // needed for varmap, work around it
	vm_arg(size_t id, ntable tab, size_t arg, size_t subarg, sizes path)
		: id(id), tab(tab), arg(arg), subarg(subarg), path(path) {}
	vm_arg(size_t arg, size_t subarg, sizes path)
		: id(0), tab(-1), arg(arg), subarg(subarg), path(path) {}
	vm_arg(const multi_arg& other, size_t id)
		: id(id), tab(other.tab), arg(other.arg), subarg(other.subarg), 
		path(other.path) {}

	explicit operator multi_arg() const { return { tab, arg, subarg, path }; }
	bool is_empty() { return tab == -1; }
	// to avoid empty .ctor
	static vm_arg get_empty() { 
		return { 0, ntable(-1), arg::none, arg::none, {} };
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
	size_t subarg;
	sizes path{};
	alt_arg(ntable tab_, int_t alt_, size_t arg_, 
			size_t subarg_ = 0, sizes path_ = {} ) 
		: tab(tab_), alt(alt_), arg(arg_), subarg(subarg_), path{path_} {}
	alt_arg(ntable tab_, int_t alt_, const alt_arg& other)
		: tab(tab_), alt(alt_), 
		  arg(other.arg), subarg(other.subarg), path{other.path} {}
	//alt_arg(const tbl_arg& other, int_t alt_ = -1) 
	//	: tab(other.tab), alt(alt_), arg(other.arg), subarg(other.subarg),
	//	  path{} {}
	// TODO: alt_arg needs no path?
	alt_arg(const multi_arg& other, int_t alt_) // = -1
		: tab(other.tab), alt(alt_), arg(other.arg), subarg(other.subarg),
		  path{other.path} {}
	alt_arg(const vm_arg& other, int_t alt_ = -1)
		: tab(other.tab), alt(alt_), arg(other.arg), subarg(other.subarg),
		  path{other.path} {}

	explicit operator tbl_arg() const { return { tab, arg, subarg }; }
	explicit operator multi_arg() const { return { tab, arg, subarg, path }; }
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