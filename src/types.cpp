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

//tbl_arg::tbl_arg(const vm_arg& other)
//	: tab(other.tab), arg(other.arg), subarg(other.subarg) {
//}

multi_arg::multi_arg(const alt_arg& other)
	: tab(other.tab), arg(other.arg), subarg(other.subarg), path{other.path} {
}
multi_arg::multi_arg(const vm_arg& other)
	: tab(other.tab), arg(other.arg), subarg(other.subarg), path(other.path) {
}

// not optimal, cache this somehow? (on init, no changes after?)
size_t compound_type::calc_sum(const vtypes& types) {
	size_t sum = 0;
	for (auto type : types) sum += type.get_bits();
	return sum;
}

//size_t compound_type::get_bits(size_t subarg) const {
//	if (subarg >= types.size()) throw 0;
//	return types[subarg].get_bits(); // .bitness;
//}

// TODO: we'll need some index or path returned w/ this to be usable
primtypes compound_type::get_primitives() const {
	primtypes primes;
	for (auto type : types) {
		switch (type.kind) {
			case type::Primitive:
				primes.push_back(type.primitive);
				break;
			case type::Compound:
			{
				primtypes cprimes = type.compound.get_primitives();
				primes.insert(primes.end(), cprimes.begin(), cprimes.end());
				break; 
			}
			default: throw 0;
		}
	}
	return primes;
}

primtype_paths compound_type::get_primitives(sizes path) const {
	primtype_paths primes;
	// this comes from type, path's already set up (in case if primitive)
	path.push_back(0);
	size_t i = 0;
	for (auto type : types) {
		path.back() = i++;
		switch (type.kind) {
			case type::Primitive:
				primes.push_back({ type.primitive, path });
				break;
			case type::Compound:
			{
				//path.push_back(0);
				primtype_paths cprimes = type.compound.get_primitives(path);
				primes.insert(primes.end(), cprimes.begin(), cprimes.end());
				break; 
			}
			default: throw 0;
		}
	}
	return primes;
}

// copy ctor, move, op=, dctor is only because of the union, nothing special
type::type(const type& other) { // noexcept
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
type::type(type&& other) noexcept {
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
type& type::operator=(const type& other) { // noexcept 
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
//type::~type() {}

// TODO: make a template for code deduplication or so
type& type::get_idx(sizes path, size_t level) {//, size_t subarg = 0
	//if (path.empty()) throw std::out_of_range("op[]: path");
	//type& type = operator[](idpath[0]); // [idx]
	//if (idpath.size() == 1) return type; // .primitive; // 1st is primitive?
	//return type.get_primitive(idpath[1]);
	if (path.empty()) throw std::out_of_range("type[]: path empty");
	if (level >= path.size()) throw std::out_of_range("type[]: level");
	size_t idx = path[level];
	switch (kind) {
		case Primitive: 
			if (idx > 0) throw std::out_of_range("type[]: id > 0");
			return *this; // eol, just ret this
		case Compound:
			if (idx >= compound.types.size())
				throw std::out_of_range("type[]<compound>: id >= size");
			// iffy, if path stops at compound return comp? might make sense
			if (level+1 >= path.size()) return compound.types[idx];
			return compound.types[idx].get_idx(path, level + 1);
		default: 
			throw std::runtime_error("type[]: type kind not implemented?");
	}
}

const type& type::get_idx(
	sizes path, size_t level) const {//, size_t subarg = 0
	if (path.empty()) throw std::out_of_range("type[]: path empty");
	if (level >= path.size()) throw std::out_of_range("type[]: level");
	size_t idx = path[level];
	switch (kind) {
		case Primitive: 
			if (idx > 0) throw std::out_of_range("type[]: id > 0");
			return *this; // eol, just ret this
		case Compound:
			if (idx >= compound.types.size())
				throw std::out_of_range("type[]<compound>: id >= size");
			// iffy, if path stops at compound return comp? might make sense
			if (level+1 >= path.size()) return compound.types[idx];
			return compound.types[idx].get_idx(path, level + 1);
		default: 
			throw std::runtime_error("type[]: type kind not implemented?");
	}
}

sizes type::normalize_sig(sizes sig) {
	for (size_t& el : sig)
		if (el != elem::etype::OPENP &&
			el != elem::etype::CLOSEP)
			el = elem::etype::NONE;
	return sig;
}

// not used but we'll need it to generate signatures properly
//sizes type::generate_sig() {
//	primtype_paths types = get_primitives(sizes{});
//	size_t isub = 0, iparenth = 0;
//	int_t level = -1, idx = -1;
//	sizes sig{};
//	for (size_t i = 0; i != types.size(); ++i) {
//		const primitive_type& type = types[i].first;
//		const sizes& path = types[i].second;
//		//int_t val = vals[i];
//		int_t newlevel = path.size()-1;
//		int_t newidx = path.size() > 1 ? path.rbegin()[1] : -1;
//		if (newlevel > level) {
//			if (level >= 0)
//				sig.push_back(elem::etype::OPENP), iparenth++;
//			level = newlevel;
//			idx = newidx;
//			isub = 0; // reset
//		} else if (newlevel == level) {
//			if (newidx > idx) { // it'll always increase only, or stay equal
//				// it's a sibling, new compound, close first then reset the isub
//				idx = newidx;
//				sig.push_back(elem::etype::CLOSEP), iparenth--;
//				isub = 0; // reset
//			} else { // same idx and level, same compound
//				if (++isub == 1) // when we come to 1st (after the 0- functor)
//					sig.push_back(elem::etype::OPENP), iparenth++;
//			}
//		} else {
//			// we're moving 'back, up', so close the parenthesis
//			sig.push_back(elem::etype::OPENP), iparenth--;
//		}
//		//if (val < 0) sig.push_back(elem::etype::VAR);
//		switch (type.type) {
//			case base_type::CHR:
//				sig.push_back(elem::etype::CHR);
//				break;
//			case base_type::INT:
//				sig.push_back(elem::etype::NUM);
//				break;
//			case base_type::STR:
//				sig.push_back(elem::etype::STR);
//				break;
//			case base_type::NONE:
//				sig.push_back(elem::etype::NONE);
//				break;
//			default: throw 0;
//		}
//	}
//	DBG(assert(size_t(level + 1) != iparenth););
//	for (int_t i = 0; i < level + 1; ++i)
//		sig.push_back(elem::etype::CLOSEP);
//	return sig;
//}

int_t type::get_chars() const {
	switch (kind) {
		case Primitive: return primitive.type == base_type::CHR ? 255 : 0;
		case Compound:
		default:
			throw 0;
	}
}

int_t type::get_syms(size_t nsyms) const {
	switch (kind) {
		case Primitive: return primitive.type == base_type::STR ? nsyms : 0;
		case Compound:
		default:
			throw 0;
	}
}

// this isn't right any more and thus removed, rework or don't use
//size_t type::get_bits(size_t subarg) const {
//	switch (kind) {
//	case Primitive:
//		if (subarg != arg::none) throw 0;
//		return primitive.bitness;
//	case Compound: return compound.get_bits(subarg);
//	default: throw 0;
//	}
//}

/*
	get_start of a sub-primitive
	- arg (multi_arg) has arg set to type, and subarg is what counts here
	(not optimal, normally use [arg] - but we do need to iterate all before?)
*/
size_t type::get_start(const multi_arg& arg) const {
	const primtypes& types = get_primitives();
	if (arg.subarg == arg::none) return 0;
	for (size_t i = 0, startbit = 0; i != types.size(); ++i) {
		if (i == arg.subarg) return startbit;
		startbit += types[i].bitness;
	}
	throw std::runtime_error("get_start, out of range?");
}

/*
	get_start of a sub-compound (sub-type), not sub-primitive (see below)
	TODO: this needs get_start(get_primitives)
*/
size_t type::get_compound_start(size_t subarg) const {
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
			// in case arg::none is -1 or so, handle it to ret full/0
			if (subarg == arg::none) return 0;
			for (size_t i = 0; i != compound.types.size(); ++i) {
				if (i == subarg) return startbit;
				const type& type = compound.types[i];
				startbit += type.get_bits();
			}
			throw 0;
			break;
		}
		default: throw 0;
	}
}

/* 
	get all primitive types regardless of the kind (for 'viewing' only) 
	(we need an interator for editing)
*/
vtypes type::get_types() const {
	switch (kind) {
	case Primitive: return { *this }; // { primitive };
		case Compound: return compound.get_types();
		default: throw 0;
	}
}

primtypes type::get_primitives() const {
	switch (kind) {
		case Primitive: return { primitive };
		case Compound: return compound.get_primitives();
		default: throw 0;
	}
}

primtype_paths type::get_primitives(sizes path) const {
	switch (kind) {
		case Primitive: 
			path.push_back(0);
			return { {primitive,path} };
		case Compound: 
			// let compound handle, set up the path
			return compound.get_primitives(path);
		default: throw 0;
	}
}

size_t type::sizeof_primitives() const {
	if (mprimes.empty())
		return get_primitives().size();
	return mprimes.size();
}

void type::calc_primes_map() {
	if (mprimes.empty()) {
		r_iterate([&](primitive_type&, size_t, sizes path, size_t i) {
			if (mprimes.size() != i) throw std::runtime_error("mprimes, i");
			mprimes.emplace_back(path); // mprimes[i] = path;
		});
	}
}

primitive_type& type::get_primitive(size_t idx) {
	if (isPrimitive()) { // should we calc_primes here too?
		if (idx > 0) throw std::out_of_range("get_primitive: primitive");
		return primitive;
	}
	calc_primes_map();
	if (mprimes.size() <= idx) throw std::out_of_range("get_primitive");
	sizes idpath = mprimes[idx];
	//return get_idx(idpath);
	if (idpath.empty()) throw std::out_of_range("get_primitive: idpath");
	type& type = get_idx({ idpath[0] });
	//type& type = operator[](sizes{idpath[0]});
	if (idpath.size() == 1) return type.primitive; // means 1st is primitive
	return type.get_primitive(idpath[1]);
}

type& type::get_sub_type(size_t idx) {
	if (isPrimitive()) {
		if (idx > 0) throw std::out_of_range("get_sub_type: primitive");
		return *this;
	}
	calc_primes_map();
	if (mprimes.size() <= idx) throw std::out_of_range("get_sub_type");
	sizes idpath = mprimes[idx]; //.at instead
	if (idpath.empty()) throw std::out_of_range("get_sub_type: idpath");
	type& type = get_idx({ idpath[0] }); //= operator[](sizes{idpath[0]});
	if (idpath.size() == 1) return type; // means 1st is primitive
	return type.get_sub_type(idpath[1]);
}

const type& type::get_sub_type(size_t idx) const {
	if (isPrimitive()) {
		if (idx > 0) throw std::out_of_range("get_sub_type: primitive");
		return *this;
	}
	if (!isCompound()) throw std::runtime_error("not implemented type");
	if (!mprimes.empty()) {
		if (mprimes.size() <= idx) throw std::out_of_range("get_sub_type");
		sizes idpath = mprimes.at(idx);
		if (idpath.empty()) throw std::out_of_range("get_sub_type: idpath");
		const type& type = get_idx({ idpath[0] }); //operator[]({idpath[0]});
		if (idpath.size() == 1) return type;
		return type.get_sub_type(idpath[1]);
	} else {
		for (size_t i = 0; i != compound.types.size(); ++i) {
			const type& type = compound.types[i];
			if (i == idx) return type;
			if (type.isPrimitive()) continue;
			if (!type.isCompound())
				throw std::runtime_error("not implemented type");
			return type.get_sub_type(idx - i);
		}
		throw std::runtime_error("get_sub_type: shouldn't happen?");
		//get_primitives(sizes path)
		//return compound.get_sub_type(idx);
	}
}

// called on bitsmeta init, when done syncing and all, to create mprimes
void type::init() {
	if (isCompound()) {
		calc_primes_map();
		// probably not needed but who knows if recursion takes off
		for (size_t i = 0; i != compound.types.size(); ++i)
			compound.types[i].init();
	}
}

// make sure conversion from multi_arg that strips path is ok
// some compound paths/combinations are not allowed in that context
// but we could always get the path from the subarg? not sure, needs example
bool type::can_discard_path(multi_arg) const {
	//if (isCompound()) {
	//	compound.types[arg.path[0]]
	//}
	return true;
}

bool type::check_arg_path(multi_arg arg) const {
	if (mprimes.empty() || (arg.subarg == arg::none && arg.path.empty()))
		return true;
	if (mprimes[arg.subarg] != arg.path) {
		// mprimes vs paths are created differently, mprimes has 0 as last
		const sizes& path = mprimes[arg.subarg];
		if (path.size() == arg.path.size() + 1 && path.back() == 0) {
			//sizes trimmed(path.begin(), path.begin() + (path.size() -1));
			sizes trimmed(path.begin(), path.end() - 1);
			if (trimmed == arg.path) return true;
		}
		throw std::runtime_error("op[] subarg, path mismatch?");
	}
	return true;
}

type& type::get_tail_type() {
	if (isCompound())
		compound.types.back().get_tail_type();
	return *this;
}

// should be called on comp only, not on primitives
type& type::get_tail_compound() {
	if (!isCompound()) throw std::runtime_error("compound expected!");
	if (compound.types.back().isPrimitive()) return *this;
	return compound.types.back().get_tail_compound();
}

// should be called on comp only, not on primitives
vtypes& type::get_tail_types() {
	if (isPrimitive()) throw std::runtime_error("primitive not expected!");
	// TODO: handle other types?
	if (!isCompound()) throw std::runtime_error("only compound expected!");
	if (compound.types.back().isPrimitive()) return compound.types;
	return compound.types.back().get_tail_types();
}

vtypes& type::get_tail_types(vtypes& types) {
	return types.back().isPrimitive() ?
		types : // means we're at top
		types.back().get_tail_types(); // we're deep, get tail...
}

vtypes& type::get_tail_types(vtypes& types, size_t level) {
	if (level == 0) return types;
	if (types.back().isPrimitive()) return types; // means we're at top
	if (!types.back().isCompound())
		throw std::runtime_error("only compound expected!");
	return get_tail_types(types.back().compound.types, level-1);
}

bool type::isCompatible(
	const std::vector<type>& l, const std::vector<type>& r) {
	if (l.size() != r.size()) return false;
	for (size_t i = 0; i != l.size(); ++i)
		if (!l[i].isCompatible(r[i])) return false;
	return true;
}

bool type::isSigCompatible(const type& l, const type& r) {
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
			const type& lsub = l.compound.types[i];
			const type& rsub = r.compound.types[i];
			if (lsub.isNone() || rsub.isNone()) continue;
			if (lsub.kind != rsub.kind) return false;
			if (lsub.isPrimitive()) {
				// we don't care about bitness?
				if (lsub.primitive.type == rsub.primitive.type) continue;
			}
			else if (isSigCompatible(lsub, rsub)) continue;
			// not sure if recursing here is right, we just want same type?
			return false;
		}
		if (normalize_sig(l.sig) == normalize_sig(r.sig))
			return true;
		// should we throw here actually? throw runtime_error("");
		return false;
	}
	return false;
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
		const primtypes& types = type.get_primitives(); // .compound.types;
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
			const primtypes& types = type.get_primitives(); // .compound.types;
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

//compound_type::compound_type(const compound_type& other) { // noexcept
//	types = other.types;
//	sumOfBits = other.sumOfBits;
//	//sumOfBits = calc_sum();
//}
//compound_type::compound_type(compound_type&& other) noexcept {
//	types = std::move(other.types); break;
//	sumOfBits = other.sumOfBits;
//	//sumOfBits = calc_sum();
//}
//compound_type& compound_type::operator=(const compound_type& other){//noexcept 
//	types = other.types;
//	sumOfBits = other.sumOfBits;
//	return *this;
//}
//base_type compound_type::get_type(size_t subarg) const {
//	if (subarg >= types.size()) throw 0;
//	return types[subarg].type;
//}
//const type& compound_type::get_sub_type(size_t idx) const {
//	size_t i = 0;
//	for (auto type : types) {
//		switch (type.kind) {
//			case type::Primitive:
//				primes.push_back({ type.primitive, path });
//				break;
//			case type::Compound:
//			{
//				//path.push_back(0);
//				primtype_paths cprimes = type.compound.get_primitives(path);
//				primes.insert(primes.end(), cprimes.begin(), cprimes.end());
//				break; 
//			}
//			default: throw 0;
//		}
//	}
//	return primes;
//}
//type& type::operator[](size_t idx) {
//	switch (kind) {
//		case Primitive: 
//			if (idx > 0) 
//				throw std::out_of_range("type[]<primitive>: id > 0");
//			// eol here, just ret this
//			return *this; // primitive;
//		case Compound:
//			if (idx >= compound.types.size())
//				throw std::out_of_range("type[]<compound>: id > 0");
//			return compound.types[idx];
//		default: 
//			throw std::runtime_error("type[]: type kind not implemented?");
//	}
//}
//const type& type::operator[](size_t idx) const {
//	switch (kind) {
//		case Primitive: 
//			if (idx > 0) throw std::out_of_range("type[]<primitive>: id > 0");
//			// eol here, just ret this
//			return *this; // primitive;
//		case Compound:
//			if (idx >= compound.types.size())
//				throw std::out_of_range("type[]<compound>: id > 0");
//			return compound.types[idx];
//		default: 
//			throw std::runtime_error("type[]: type kind not implemented?");
//	}
//}
//base_type type::get_type() const {
//	switch (kind) {
//		case Primitive: return primitive.type;
//		default: throw 0;
//	}
//}
//base_type type::get_type(size_t subarg) const {
//	switch (kind) {
//		case Primitive: 
//			if (subarg != arg::none) throw 0;
//			return primitive.type;
//		case Compound: return compound.get_type(subarg);
//		default: throw 0;
//	}
//}
//primitive_type::primitive_type(const primitive_type& other) {
//	type = other.type;
//	bitness = other.bitness;
//}
//primitive_type::primitive_type(primitive_type&& other) noexcept {
//	type = other.type;
//	bitness = other.bitness;
//}
//primitive_type& primitive_type::operator=(primitive_type&& other) {
//	type = other.type;
//	bitness = other.bitness;
//	//type(std::move(other.type));
//	//bitness(std::move(other.bitness));
//	return *this;
//}
//primitive_type& primitive_type::operator=(primitive_type other) {
//	using std::swap;
//	type = other.type;
//	bitness = other.bitness;
//	return *this;
//}
