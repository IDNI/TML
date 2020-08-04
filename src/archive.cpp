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
#include "archive.h"
#include "input.h"
#include "options.h"
#include "types.h"

using std::wstring;
using std::endl;

unsigned char archive::enc_bools(std::initializer_list<bool> list) {
	DBG(assert(list.size() <= 8);)
	unsigned char i = 0, r = 0;
	for (auto b : list) r |= (unsigned char) (b << i++);
	return r;
}
bool archive::dec_bool(unsigned char bls, int pos) {
	return (bls >> pos) & 1;
}

void archive::write(const char* data, size_t s) {
	// DBG(o::dbg() << L"write const char* data[0]: " << &data << L' ' << (int)data[0] << std::endl;)
	memcpy(((char*)data_) + pos_, data, s);
	pos_ += s;
}
void archive::read(char* data, size_t s) {
	// o::dbg() << L"read char* data: " << &data << std::endl;
	memcpy(data, ((char*)data_) + pos_, s);
	pos_ += s;
}

void archive::write(const void* data, size_t s) {
	// DBG(o::dbg() << L"write const void* data: " << &data << L' ' << data  << std::endl;)
	write(static_cast<const char*>(data), s);
}
void archive::read(void* data, size_t s) {
	// o::dbg() << L"read void* data: " << &data << std::endl;
	read(static_cast<char*>(data), s);
}

// vectors
template <typename T>
archive& archive::operator<<(const std::vector<T>& v) {
	return write_container(v);
}
template <typename T>
archive& archive::operator>>(std::vector<T>& v) {
	size_t s; *this >> s;
	v.resize(s);
	for (size_t i = 0; i != v.size(); ++i) *this >> v[i];
	return *this;
}
template <typename T>
size_t archive::vecsize(const std::vector<T>& v) {
	size_t s = sizeof(size_t);
	for (auto e : v) s += size(e);
	return s;
}

// sets
template <typename T, typename... U>
archive& archive::operator<<(const std::set<T, U...>& v) {
	return write_container(v);
}
template <typename T, typename... U>
archive& archive::operator>>(std::set<T, U...>& v) {
	size_t s; *this >> s;
	for (size_t i = 0; i != s; ++i) {
		T t;
		*this >> t, v.insert(t);
	}
	return *this;
}
archive& archive::operator>>(std::set<term> &st) {
	size_t s; *this >> s;
	for(size_t i = 0; i != s; ++i) {
		o::dbg() << L"i: " << i << L" ";
		term t(0, {}, {});
		*this >> t, st.insert(t);	
	};
	return *this;
}
archive& archive::operator>>(std::set<level> &levels) {
	size_t s; *this >> s;
	if (s) do {
		bdd_handles h; *this >> h;
		levels.insert(h);
	} while (s-- > 0);
	return *this;
}
template <typename T, typename... U>
size_t archive::setsize(const std::set<T, U...>& v) {
	size_t s = sizeof(size_t);
	for (auto e : v) s += size(e);
	return s;
}
template <typename T>
size_t archive::setsize(const std::set<T>& v) {
	size_t s = sizeof(size_t);
	for (auto e : v) s += size(e);
	return s;
}
//size_t archive::size(const std::set<lexeme>& lxms) {
//	size_t s = sizeof(size_t);
//	for (auto l : lxms) s += l.size() + sizeof(size_t);
//	return s;
//}
//size_t archive::size(const std::set<lexeme, lexcmp>& lxms) {
//	size_t s = sizeof(size_t);
//	for (auto l : lxms) s += l.size() + sizeof(size_t);
//	return s;
//}

// maps
template <typename Key, typename T>
archive& archive::operator<<(const std::map<Key, T>& m) {
	return write_map(m);
}
template <typename Key, typename T>
archive& archive::write_map(const std::map<Key, T>& m) {
	*this << m.size();
	for (auto p : m) *this << p;
	return *this;
}
template <typename Key, typename T>
archive& archive::write_unordered_map(const std::unordered_map<Key, T>& m) {
	*this << m.size();
	for (auto p : m) *this << p;
	return *this;
}
template <typename Key, typename T, typename C>
archive& archive::read_map(std::map<Key, T, C>& m) {
	Key k; T v;
	size_t nsize; *this >> nsize;
	if (nsize) do {
		*this >> k >> v;
		m.emplace(k, v);
	} while (--nsize > 0);
	return *this;
}
template <typename Key, typename T>
archive& archive::read_map(std::map<Key, T>& m) {
	size_t nsize; *this >> nsize;
	Key k; T v;
	if (nsize) do {
		*this >> k >> v;
		m.emplace(k, v);
	} while (--nsize > 0);
	return *this;
}
archive& archive::operator>>(std::map<ntable, std::set<ntable>>& deps) {
	ntable nt;
	std::set<ntable> snt;
	size_t nsize; *this >> nsize;
	if (nsize) do {
		*this >> nt >> snt;
		deps.emplace(nt, snt);
	} while (--nsize > 0);
	return *this;
}
archive& archive::operator>>(std::map<ntable, std::set<term>>& mhits) {
	ntable nt;
	std::set<term> st;
	size_t nsize, tsize;
	*this >> nsize;
	if (nsize) do {
		*this >> nt >> tsize;
		if (tsize) do {
			term t = {0, {}, {}};
			*this >> t;
			st.insert(t);			
		} while (tsize-- > 0);
		mhits.emplace(nt, st);
	} while (--nsize > 0);
	return *this;
}
archive& archive::operator>>(std::map<multi_arg, std::set<alt_arg>>& minvtyps) {
	size_t nsize, ssize;
	*this >> nsize;
	std::set<alt_arg> saa;
	if (nsize) do {
		multi_arg ma(0, 0, {});
		*this >> ma >> ssize;
		if (ssize) do {
			alt_arg aa(0, 0, 0, 0);
			*this >> aa;
			saa.insert(aa);
		} while (ssize-- > 0);
		minvtyps.emplace(ma, saa);
	} while (--nsize > 0);
	return *this;
}
archive& archive::operator>>(std::map<ntable, std::set<tbl_alt>>& tblbodies) {
	size_t nsize, ssize;
	ntable nt;
	*this >> nsize;
	std::set<tbl_alt> sta;
	if (nsize) do {
		*this >> nt >> ssize;
		if (ssize) do {
			tbl_alt ta = tbl_alt::get_empty();
			*this >> ta;
			sta.insert(ta);
		} while (ssize-- > 0);
		tblbodies.emplace(nt, sta);
	} while (--nsize > 0);
	return *this;
}

archive& archive::operator>>(std::map<alt_arg, multi_arg>& mtyps) {
	size_t nsize;
	*this >> nsize;
	if (nsize) do {
		alt_arg aa(0, 0, 0, 0);
		multi_arg ma(0, 0, {});
		*this >> aa >> ma;
		mtyps.emplace(aa, ma);
	} while (--nsize > 0);
	return *this;
}
archive& archive::operator>>(std::map<tbl_alt, tbl_alt>& altordermap) {
	size_t nsize;
	*this >> nsize;
	if (nsize) do {
		tbl_alt k = tbl_alt::get_empty();
		tbl_alt v = tbl_alt::get_empty();
		*this >> k >> v;
		altordermap.emplace(k, v);
	} while (--nsize > 0);
	return *this;
}
template <typename Key, typename T>
size_t archive::mapsize(const std::map<Key, T>& m) {
	size_t s = sizeof(size_t);
	for (auto p : m) s += size(p.first) + size(p.second);
	return s;
}
template <typename Key, typename T, typename C>
size_t archive::mapsize(const std::map<Key, T, C>& m) {
	return mapsize<Key, T>();
}

template <typename Key, typename T>
archive& archive::operator<<(const std::pair<Key, T>& p) {
	return *this << p.first << p.second;
}

archive& archive::write_header() {
	return *this << ((type_ == DRIVER)
		? int16_t(56765)  // 0xbddd
		: int16_t(53427)) // 0xbdd0
		<< latest_version;
}
archive& archive::read_header() {
	int16_t head; *this >> head;
	DBG(assert(head == ((type_ == DRIVER)
		? int16_t(56765)     // 0xbddd
		: int16_t(53427)));) // 0xbdd0
	return *this >> version_;
}
size_t archive::header_size() {
	return sizeof(int16_t) + sizeof(size_t);
}

archive& archive::operator<<(const int_t& val) {
	//DBG(o::dbg() << L"writing int_t: " << val << endl;)
	write((const char*)&val, sizeof(int_t));
	return *this;
}
archive& archive::operator>>(int_t& val) {
	read(&val, sizeof(int_t));
	//DBG(o::dbg() << L"reading int_t: " << val << endl;)
	return *this;
}

archive& archive::operator<<(const int16_t& val) {
	//DBG(o::dbg() << L"writing int16_t: " << val << endl;)
	write((const char*)&val, sizeof(int16_t));
	return *this;
}
archive& archive::operator>>(int16_t& val) {
	read(&val, sizeof(int16_t));
	//DBG(o::dbg() << L"reading int16_t: " << val << endl;)
	return *this;
}

archive& archive::operator<<(const size_t& val) {
	// DBG(o::dbg() << L"writing size_t: " << val << endl;)
	write((const char*)&val, sizeof(size_t));
	return *this;
}

archive& archive::operator>>(size_t& val) {
	read((char*)&val, sizeof(size_t));
	// DBG(o::dbg() << L"reading size_t: " << val << endl;)
	return *this;
}

archive& archive::operator<<(const unsigned int& val) {
	//DBG(o::dbg() << L"writing uint: " << val << endl;)
	write((const char*)&val, sizeof(unsigned int));
	return *this;
}
archive& archive::operator>>(unsigned int& val) {
	read(&val, sizeof(unsigned int));
	//DBG(o::dbg() << L"reading uint: " << val << endl;)
	return *this;
}

archive& archive::operator<<(const unsigned char& val) {
	// DBG(o::dbg() << L"writing char: " << val << endl;)
	write((const char*)(&val), sizeof(unsigned char));
	return *this;
}
archive& archive::operator>>(unsigned char& val) {
	read(&val, sizeof(unsigned char));
	// DBG(o::dbg() << L"reading char: " << val << endl;)
	return *this;
}

archive& archive::operator<<(const char& val) {
	// DBG(o::dbg() << L"writing char: " << val << endl;)
	write((const char*)(&val), sizeof(char));
	return *this;
}
archive& archive::operator>>(char& val) {
	read(&val, sizeof(char));
	// DBG(o::dbg() << L"reading char: " << val << endl;)
	return *this;
}

archive& archive::operator<<(const lexeme& val) {
	// DBG(o::dbg() << L"writing lexeme: " << lexeme2str(val) << endl;)
	return *this << std::wstring(val[0], val[1]-val[0]);
}
archive& archive::operator>>(lexeme& r) {
	std::wstring s;
	*this >> s;
	r = get_dict()->get_lexeme(s);
	return *this;
}
size_t archive::size(const lexeme& l) {
	return l[1] - l[0] + sizeof(size_t);
}

archive& archive::operator<<(const lexeme_range& r) {
	return *this << r[0] << r[1];
}
archive& archive::operator>>(lexeme_range& r) {
	return *this >> r[0] >> r[1];
}

archive& archive::operator<<(const std::wstring& val) {
	// DBG(o::dbg() << L"writing wstring: " << val << endl;)
	return *this << ws2s(val);
}
archive& archive::operator>>(std::wstring& val) {
	std::string s; *this >> s; val = s2ws(s);
	return *this;
}

archive& archive::operator<<(const std::string& val) {
	// DBG(o::dbg() << L"writing string: " << s2ws(val)
	// 	 << L" size: " << val.size() << endl;)
	*this << val.size();
	write((const char*)val.c_str(), val.size());
	return *this;
}
archive& archive::operator>>(std::string& val) {
	size_t s; *this >> s;
	//DBG(o::dbg() << L"reading string, size: " << s << endl;)
	if (s == 0) {
		val = "";
		return *this;
	}
	char* str = new char[s+1]; str[s] = 0x0; // ???
	read(str, s); 
	val = std::string(str);
	//DBG(o::dbg() << L"reading string, value: " << s2ws(val) << endl;)
	return *this;
}

archive& archive::operator<<(const spbdd_handle& val) {
	//DBG(o::dbg() << L"writing spbdd_handle: " << (val ? val->b : (int_t)0) << endl;)
	return *this << (val ? val->b : (int_t)0);
}
archive& archive::operator>>(spbdd_handle& val) {
	int_t b; *this >> b;
	val = bdd_handle::get(b);
	//DBG(o::dbg() << L"reading spbdd_handle: " << b << endl;)
	return *this;
}

archive& archive::operator<<(const dict_t& d) {
	std::wostringstream data;
	std::map<lexeme, lexeme_range> lmap{};
	std::vector<lexeme_range> lranges;
	size_t pos = 0;
	auto add_lexeme_and_map =
		[&data, &lmap, &lranges, &pos] (const lexeme& l) {
			lexeme_range r = { pos, pos };
			auto it = lmap.find(l);
			if (it == lmap.end()) { // not in map
				if (l[1]-l[0] > 0) // non-0
					for (cws c = l[0]; c != l[1]; ++c)
						data << *c, ++pos, r[1] = pos;
				lmap.insert({ l, r });
				lranges.push_back(r);
			} else lranges.push_back(it->second);
		};
	for (auto& v : {d.rels, d.syms, d.bltins})
		for (auto& l : v) add_lexeme_and_map(l);
	*this << ws2s(data.str()) << d.rels_dict.size() << d.syms_dict.size()
		<< d.bltins_dict.size();
	for (auto& r : lranges) *this << r;
	write_container(d.types);
	return *this;
}
archive& archive::operator>>(dict_t& d) {
	size_t nrels, nsyms, nbltins;
	// TODO: don't allocate. use mmap addresses (switch from wchar first?)
	std::string s; *this >> s; cws source = wcsdup(s2ws(s).c_str());
	*this >> nrels >> nsyms >> nbltins;
	lexeme_range r;
	for (size_t i = 0; i != nrels; ++i) *this >> r,
		d.get_rel(lexeme{ source+r[0], source+r[1] });
	for (size_t i = 0; i != nsyms; ++i) *this >> r,
		d.get_sym(lexeme{ source+r[0], source+r[1] });
	for (size_t i = 0; i != nbltins; ++i) *this >> r,
		d.get_bltin(lexeme{ source+r[0], source+r[1] });
	return *this >> d.types;
}
size_t archive::size(const dict_t& d) {
	size_t s = (4 * sizeof(size_t)) + size(d.types)
		+ (2 * sizeof(size_t)
			* (d.rels.size() + d.syms.size() + d.bltins.size()));
	std::set<lexeme> lexemes{};
	auto add_lexeme_size =
		[&lexemes, &s] (const lexeme& l) {
			if (lexemes.insert(l).second) s += l[1]-l[0];
		};
	for (auto& l : d.rels)   add_lexeme_size(l);
	for (auto& l : d.syms)   add_lexeme_size(l);
	for (auto& l : d.bltins) add_lexeme_size(l);
	return s;
}

archive& archive::operator<<(const term& t) {
	*this << t.tab << (unsigned char)t.extype;
	if (t.extype == term::ARITH) *this << (unsigned char) t.arith_op;
	*this << enc_bools({ t.neg, t.goal }) << t.size();
	for (int_t i : t) *this << i;
	return *this;
}
archive& archive::operator>>(term& t) {
	unsigned char val;
	size_t s;
	*this >> t.tab >> val;
	t.extype = (term::textype)val;
	if (t.extype == term::ARITH) *this >> val, t.arith_op = (t_arith_op)val;
	else t.arith_op = NOP;
	*this >> val >> s;
	t.neg = dec_bool(val), t.goal = dec_bool(val, 1);
	t.resize(s);
	for (size_t i = 0; i != s; ++i) *this >> t[i];
	return *this;
}
size_t archive::size(const term& t) {
	return (2 + (t.extype == term::ARITH)) * sizeof(unsigned char)
		+ sizeof(size_t) + (1 + t.size()) * sizeof(int_t);
}

archive& archive::operator<<(const rule& r) {
	*this << r.t << r.eq << r.rlast << r.h;
	return write_container(r.last);
}
archive& archive::operator>>(rule& r) {
	*this >> r.t >> r.eq >> r.rlast >> r.h >> r.last;
	r.tab = r.t.tab;
	r.neg = r.t.neg;
	r.len = r.t.size();
	return *this;
}
size_t archive::size(const rule& r) {
	return size(r.t) + (3 * sizeof(int_t)) + size(r.last);
}

archive& archive::operator<<(const sig& s) {
	return *this << s.first << s.second;
}
archive& archive::operator>>(sig& s) {
	return *this >> s.first >> s.second;
}
size_t archive::size(const sig& sign) {
	return (sign.second.size() + 1) * sizeof(int_t) + sizeof(size_t);
}

archive& archive::operator<<(const alt_arg& a) {
	return *this << a.tab << a.alt
		<< a.arg << a.subarg << a.path
		<< (unsigned char)a.special;
}
archive& archive::operator>>(alt_arg& a) {
	unsigned char tmp;
	*this
		>> a.tab
		>> a.alt
		>> a.arg
		>> a.subarg
		>> a.path
		>> tmp;
	a.special = (decltype(a.special)) tmp;
	return *this;
}
size_t archive::size(const alt_arg& a) {
	return 3 * sizeof(int_t) + ((a.path.size() + 2) * sizeof(size_t))
		+ sizeof(unsigned char);
}

archive& archive::operator<<(const tbl_arg& a) {
	return *this << a.tab << a.arg << a.subarg;
}
archive& archive::operator>>(tbl_arg& a) {
	return *this >> a.tab >> a.arg >> a.subarg;
}
size_t archive::size(const tbl_arg&) {
	return 2 * sizeof(int_t) + sizeof(size_t);
}

archive& archive::operator<<(const multi_arg& a) {
	return *this << a.tab << a.arg << a.subarg << a.path
		<< (unsigned char)a.special;
}
archive& archive::operator>>(multi_arg& a) {
	unsigned char tmp;
	*this >> a.tab >> a.arg >> a.subarg >> a.path >> tmp;
	a.special = (decltype(a.special)) tmp;
	return *this;
}
size_t archive::size(const multi_arg& a) {
	return 2 * sizeof(int_t) + ((a.path.size() + 2) * sizeof(size_t))
		+ sizeof(unsigned char);
}

archive& archive::operator<<(const infer_types& inf) {
	return *this
		<< inf.minvtyps
		<< inf.mtyps
		<< inf.altids4types
		<< inf.tblbodies
		<< inf.tblrules
		<< inf.altordermap
		//<< inf.altsmap
		;
}
archive& archive::operator>>(infer_types& inf) {
	return *this
		>> inf.minvtyps
		>> inf.mtyps
		>> inf.altids4types
		>> inf.tblbodies
		>> inf.tblrules
		>> inf.altordermap
		// >> inf.altsmap
		;
}
size_t archive::size(const infer_types& inf) {
	return size(inf.minvtyps) + size(inf.mtyps) + size(inf.altids4types)
		+ size(inf.tblbodies) + size(inf.tblrules)
		+ size(inf.altordermap) ;//+ size(inf.altsmap);
}

archive& archive::operator<<(const compound_type& ct) {
	*this
		<< enc_bools({ ct.isroot, ct.bitaligned })
		<< ct.alignment // only if bitaligned?
		<< ct.sumOfBits << ct.sumOfPrimitives // mutable
		;
	return write_container<vtypes>(ct.types);
		// static align_bits bool
}
archive& archive::operator>>(compound_type& ct) {
	unsigned char bls;
	*this >> bls >> ct.alignment >> ct.sumOfBits >> ct.sumOfPrimitives;
	ct.isroot = dec_bool(bls), ct.bitaligned = dec_bool(bls, 1);
	return *this >> ct.types;
}
size_t archive::size(const compound_type& ct) {
	return sizeof(unsigned char) + size(ct.alignment)
		+ 2 * sizeof(size_t) + size(ct.types);
}

archive& archive::operator<<(const primitive_type& pt) {
	return *this << (unsigned char) pt.type << pt.bitness << pt.num; 
}
archive& archive::operator>>(primitive_type& pt) {
	unsigned char t;
	*this >> t >> pt.bitness >> pt.num;
	pt.type = (base_type)t;
	return *this;
}
size_t archive::size(const primitive_type&) {
	return sizeof(unsigned char) + sizeof(size_t) + sizeof(int_t);
}

archive& archive::operator<<(const ::type& at) {
	*this
		<< at.sig
		<< at.mprimes
		<< (unsigned char) at.kind;
	if (at.isPrimitive()) *this << at.primitive;
	else if (at.isCompound()) *this << at.compound;
	return *this;
}
archive& archive::operator>>(::type& at) {
	unsigned char tmp;
	*this
		>> at.sig
		>> at.mprimes
		>> tmp;
	at.kind = static_cast<decltype(at.kind)>(tmp);
	if (at.isPrimitive()) *this >> at.primitive;
	else if (at.isCompound()) *this >> at.compound;
	return *this;
}
size_t archive::size(const ::type& at) {
	size_t s = size(at.sig) + size(at.mprimes) + sizeof(unsigned char);
	if (at.isPrimitive()) s += size(at.primitive);
	else if (at.isCompound()) s += size(at.compound);
	return s;
}

archive& archive::operator<<(const bitsmeta& bm) {
	write_container<std::vector<::type>>(bm.types)
		<< bm.vargs
		<< bm.vbits
		<< bm.nterms
		<< bm.args_bits
		<< bm.maxbits
		<< bm.mleftbits
		<< bm.mleftargs
		<< enc_bools({ bm.bitsfixed, bm.hasmultivals, bm.fromheader });
	return *this;
}
archive& archive::operator>>(bitsmeta& bm) {
	char bls;
	*this
		>> bm.types
		>> bm.vargs
		>> bm.vbits
		>> bm.nterms
		>> bm.args_bits
		>> bm.maxbits
		>> bm.mleftbits
		>> bm.mleftargs
		>> bls;
	bm.bitsfixed    = dec_bool(bls),
	bm.hasmultivals = dec_bool(bls, 1),
	bm.fromheader   = dec_bool(bls, 2);
	return *this;
}
size_t archive::size(const bitsmeta& bm) {
	size_t s = size(bm.types)
		+ 3 * sizeof(size_t)
		+ size(bm.vargs) + size(bm.vbits)
		+ size(bm.mleftbits)
		+ sizeof(unsigned char)
		+ sizeof(size_t);
	for (auto m : bm.mleftargs) s += sizeof(size_t) + size(m.second);
	return s;
}

archive& archive::operator<<(const elem& e) {
	*this << (unsigned char)e.type;
	switch (e.type) {
		case elem::ARITH: *this << (unsigned char)e.arith_op; break;
		case elem::NUM:   *this << e.num; break;
		case elem::CHR:   *this << (unsigned int)e.ch; break; // TODO save char as utf8 string?
		case elem::STR:
		case elem::VAR:   *this << e.e;
		default:;
	}
	return *this;
}
archive& archive::operator>>(elem& e) {
	wstring s;
	unsigned int ch;
	unsigned char tmp; *this >> tmp, e.type = (elem::etype)tmp;
	switch (e.type) {
		case elem::ARITH: *this>>tmp, e.arith_op=(t_arith_op)tmp; break;
		case elem::NUM:   *this >> e.num; break;
		case elem::CHR:   *this >> ch, e.ch = (wchar_t)ch; break;
		case elem::STR:
	 	case elem::VAR:   *this >> s, e.e = get_dict()->get_lexeme(s);
		                  break;
		default:;
	}
	return *this;
}
size_t archive::size(const elem& e) {
	size_t s = sizeof(unsigned char);
	switch (e.type) {
		case elem::ARITH: s += sizeof(unsigned char); break;
		case elem::NUM:   s += sizeof(int_t); break;
		case elem::CHR:   s += sizeof(unsigned int); break;
		case elem::STR:
	 	case elem::VAR:   s += size(e.e); break;
		default:;
	}
	return s;
}

archive& archive::operator<<(const raw_term& rt) {
	*this << (unsigned char)rt.extype;
	if (rt.extype == raw_term::ARITH) *this << (unsigned char)rt.arith_op;
	*this << enc_bools({ rt.neg });
	return *this << rt.e << rt.arity;
}
archive& archive::operator>>(raw_term& rt) {
	unsigned char tmp;
	*this >> tmp; rt.extype = (raw_term::rtextype)tmp;
	if (rt.extype == raw_term::ARITH)
		*this >> tmp, rt.arith_op = (t_arith_op)tmp;
	*this >> tmp;
	rt.neg = dec_bool(tmp);
	return *this >> rt.e >> rt.arity;
}
size_t archive::size(const raw_term& rt) {
	size_t s = (2 + (rt.extype == raw_term::ARITH)) * sizeof(unsigned char);
	s += size(rt.e) + size(rt.arity);
	return s;
}

archive& archive::operator<<(const directive& d) {
	return *this << d.rel << d.arg << d.t;
}
archive& archive::operator>>(directive& d) {
	*this >> d.rel;
	wstring s; *this >> s;
	d.arg = get_dict()->get_lexeme(s);
	return *this >> d.t;
}
size_t archive::size(const directive& d) {
	return size(d.rel) + size(d.arg) + size(d.t);
}

archive& archive::operator<<(const production& p) {
	return *this << p.p;
}
archive& archive::operator>>(production& p) {
	return *this >> p.p;
}
size_t archive::size(const production& p) {
	return size(p.p);
}

archive& archive::operator<<(const raw_rule& r) {
	return *this << (unsigned char)r.type << r.h << r.b;
}
archive& archive::operator>>(raw_rule& r) {
	unsigned char tmp; *this >> tmp; r.type = (raw_rule::etype)tmp;
	return *this >> r.h >> r.b;
}
size_t archive::size(const raw_rule& r) {
	size_t s = sizeof(unsigned char) + size(r.h) + sizeof(size_t);
	for (auto t : r.b) s += size(t);
	return s;
}
archive& archive::operator<<(const raw_prog& rp) {
	return *this << rp.d << rp.g << rp.r << rp.builtins;
}
archive& archive::operator>>(raw_prog& rp) {
	size_t nsize;
	wstring s;
	*this >> rp.d >> rp.g >> rp.r >> nsize;
	for (size_t i = 0; i != nsize; ++i)
		*this >> s, rp.builtins.insert(get_dict()->get_lexeme(s));
	return *this;
}
size_t archive::size(const raw_prog& rp) {
	return size(rp.d) + size(rp.g) + size(rp.r) + size(rp.builtins);
}

archive& archive::operator<<(const raw_progs& rps) {
	return *this << rps.p;
}
archive& archive::operator>>(raw_progs& rps) {
	return *this >> rps.p;
}
size_t archive::size(const raw_progs& rps) {
	return size(rps.p);
}
archive& archive::operator<<(const option& o) {
	*this << (unsigned char)o.t << o.n[0];
	switch (o.t) {
		case option::type::INT:    *this << o.v.v_i; break;
		case option::type::BOOL:   *this << enc_bools({ o.v.v_b }); break;
		case option::type::STRING: *this << o.v.v_s; break;
		default: ;
	}
	return *this;
}
size_t archive::size(const option& o) {
	size_t s = sizeof(unsigned char) + size(o.n[0]);
	switch (o.t) {
		case option::type::INT:    s += sizeof(int_t); break;
		case option::type::BOOL:   s += sizeof(unsigned char); break;
		case option::type::STRING: s += size(o.v.v_s); break;
		default: ;
	}
	return s;
}

archive& archive::operator<<(const options& o) {
	size_t n = 0;
	for (auto it : o.opts) if (!it.second.is_undefined()) n++;
	*this << n;
	for (auto it : o.opts) if (!it.second.is_undefined()) *this<<it.second;
	return *this;
}
archive& archive::operator>>(options& opts) {
	size_t nsize;
	*this >> nsize;
	for (size_t i = 0; i != nsize; ++i) {
		int_t val;
		wstring ws, n;
		unsigned char uch;
		*this >> uch >> n;
		// option o; opts.get(n, o);
		switch ((option::type) uch) {
			case option::type::INT:
				*this >> val; opts.set(n, val); break;
			case option::type::BOOL:
				*this >> uch; opts.set(n, dec_bool(uch));
				break;
			case option::type::STRING:
				*this >> ws;  opts.set(n, ws); break;
			default: throw 0;
		}
	}
	return *this;
}
size_t archive::size(const options& opts) {
	size_t s = sizeof(size_t);
	for (auto it : opts.opts) if (!it.second.is_undefined())
		s += size(it.second);
	return s;
}

archive& archive::operator<<(const prog_data& pd) {
	return *this
		<< pd.strs
		<< enc_bools({ pd.bwd })
		<< pd.n
		<< pd.start_step
		<< pd.elapsed_steps;
}
archive& archive::operator>>(prog_data& pd) {
	unsigned char bls;
	*this >> pd.strs >> bls;
	pd.bwd = dec_bool(bls);
	return *this >> pd.n >> pd.start_step >> pd.elapsed_steps;
}
size_t archive::size(const prog_data& pd) {
	return size(pd.strs) + sizeof(unsigned char) + 3 * sizeof(size_t);
}

archive& archive::operator<<(const strs_t& strs) {
	//return write_map(strs);
	*this << strs.size();
	for (auto p : strs) *this << p.first << p.second;
	return *this;
}
archive& archive::operator>>(strs_t& strs) { return read_map(strs); }
size_t archive::size(const strs_t& strs) {
	size_t s = sizeof(size_t);
	for (auto p : strs) s += size(p.first) + size(p.second);
	return s;
}

archive& archive::operator<<(const flat_prog& fp) {
	*this << fp.size();
	for (auto& v : fp) *this << v;
	return *this;
}
archive& archive::operator>>(flat_prog& fp) {
	size_t nsize, tsize;
	*this >> nsize;
	if (nsize) do {
		std::vector<term> vt{};
		*this >> tsize;
		if (tsize) do {
			term t = {0, {}, {}};
			*this >> t;
			vt.push_back(t);			
		} while (tsize-- > 0);
		fp.insert(vt);
	} while (--nsize > 0);
	return *this;
}
size_t archive::size(const flat_prog& fp) {
	size_t s = sizeof(size_t);
	for (auto v : fp) s += size(v);
	return s;
}

archive& archive::operator<<(const table& t) {
	*this
		<< t.sign
		<< t.bm
		<< t.tq
		<< t.len
		<< t.priority
		<< t.r
		<< enc_bools({ t.ext, t.unsat, t.tmp })
		<< t.idbltin
		<< t.bltinargs
		<< t.bltinsize;
	return *this;
}
archive& archive::read_table(tables& tbls) {
	char bls;
	sig s;
	bitsmeta bm;
	if (!dict) dict = &tbls.dict;
	*this
		>> s 
		>> bm;
	ntable nt = tbls.get_table(s, bm.types);
	table&  t = tbls.tbls[nt];
	t.bm = bm;
	*this
		>> t.tq
		>> t.len
		>> t.priority
		>> t.r
		>> bls
		>> t.idbltin
		>> t.bltinargs
		>> t.bltinsize
		;
	t.ext   = dec_bool(bls),
	t.unsat = dec_bool(bls, 1),
	t.tmp   = dec_bool(bls, 2);
	return *this;
}
size_t archive::size(const table& t) {
	size_t s = 0
		+ size(t.sign)
		+ size(t.bm)
		+ size(t.len)
		+ size(t.priority)
		+ size(t.tq)
		+ size(t.r)
		+ size(t.idbltin)
		+ size(t.bltinargs)
		+ size(t.bltinsize)
		+ sizeof(unsigned char);
	//DBG(o::dbg() << L"table size: " << t.sign.first << L'/' << t.sign.second[0] << L' ' << s
	//	<< L" size(bm): " << size(t.bm)
	//	<< L" (t.bltinargs.size(): " << t.bltinargs.size()
	//	<< L" (t.r.size(): " << t.r.size()
	//	<< std::endl;)
	return s;
}
archive& archive::operator<<(const tables& tbls) {
	*this
		<< tbls.dict
		<< tbls.rules
		<< tbls.fronts
		<< tbls.levels
		//<< bodies
		//<< alts
		<< tbls.nstep
		<< tbls.tmprels
		<< tbls.deps
		<< tbls.mhits
		<< tbls.altids
		<< tbls.pBin
		<< tbls.max_args
		<< tbls.range_compound_memo
		<< tbls.goals
		<< tbls.to_drop
		<< tbls.exts
		<< tbls.strs
		<< tbls.str_rels
		<< tbls.prog_after_fp
		<< tbls.infer
		//<< tbls.addBits
		<< enc_bools({ tbls.populate_tml_update, tbls.print_updates,
			tbls.print_steps, tbls.autotype })
		;
	*this << tbls.tbls.size();
	for (size_t  i = 0; i != tbls.tbls.size(); ++i)
		*this << tbls.tbls[i];
	return *this;
}
archive& archive::operator>>(tables& tbls) {
	unsigned char tmp;
	size_t nsize;
	*this >> tbls.dict >> nsize;
	for (size_t i = 0; i != nsize; ++i) {
		tbls.rules.push_back(rule(false, 0, term(0, {}, {})));
		*this >> tbls.rules.back();
	}
	*this
		>> tbls.fronts
		>> tbls.levels
		>> tbls.nstep
		>> tbls.tmprels
		>> tbls.deps
		>> tbls.mhits
		>> tbls.altids
		>> tbls.pBin
		>> tbls.max_args
		>> tbls.range_compound_memo
		>> tbls.goals
		>> tbls.to_drop
		>> tbls.exts
		>> tbls.strs
		>> tbls.str_rels
		>> tbls.prog_after_fp
		>> tbls.infer
		//>> tbls.addBits
		>> tmp
		>> nsize;
	for (size_t i = 0; i != nsize; ++i) read_table(tbls);
	tbls.populate_tml_update = dec_bool(tmp);
	tbls.print_updates       = dec_bool(tmp, 1);
	tbls.print_steps         = dec_bool(tmp, 2);
	tbls.autotype            = dec_bool(tmp, 3);
	return *this;
}
size_t archive::size(const tables& t) {
	size_t s = 0
		+ size(t.rules)
		+ size(t.fronts)
		+ size(t.levels)
		+ sizeof(nlevel)
		+ size(t.tmprels)
		+ size(t.deps)
		+ size(t.mhits)
		+ size(t.altids)
		+ size(t.pBin)
		+ size(t.dict)
		+ 2 * sizeof(size_t)
		+ size(t.goals)
		+ size(t.strs)
		+ size(t.prog_after_fp)
		+ size(t.infer)
		+ 3 * sizeof(size_t)
		+ sizeof(int_t)
			* (t.to_drop.size() + t.exts.size() + t.str_rels.size())
		+ sizeof(unsigned char)
		+ sizeof(size_t);
	for (auto p : t.range_compound_memo) s += size(p.first) + sizeof(int_t);
	for (size_t i = 0; i != t.tbls.size(); ++i) s += size(t.tbls[i]);
	return s;
}

archive& archive::operator<<(const driver& d) {
	write_header();
	write_bdd();
	*this
		<< d.pd
		<< d.nums
		<< d.chars
		<< d.syms
		<< d.builtin_rels
		<< d.transformed_strings
		<< d.strs_extra
		<< d.rels
		<< d.vars
		<< d.rp
		<< d.opts
		<< d.std_input
		<< enc_bools({ d.result, d.running })
		;
	write_tables(d);
	return *this << input::source << int16_t(0x8362);
}

archive& archive::operator>>(driver& d) {
	std::string source;
	//DBG(o::dbg() << L"loading driver\n";)
	size_t nsize;
	wstring s;
	char bls;
	dict_t& dict_r = d.tbl->dict;
	dict = &(dict_r);
	read_header();
	read_bdd();
	*this >> d.pd >> d.nums >> d.chars >> d.syms >> d.builtin_rels 
		>> d.transformed_strings >> nsize;
	for (size_t i = 0; i != nsize; ++i)
		*this >> s, d.strs_extra.insert(dict_r.get_lexeme(s));
	*this >> nsize;
	for (size_t i = 0; i != nsize; ++i)
		*this >> s, d.rels.insert(dict_r.get_lexeme(s));
	*this >> nsize;
	for (size_t i = 0; i != nsize; ++i)
		*this >> s, d.vars.insert(dict_r.get_lexeme(s));
	*this >> d.rp >> d.opts >> d.std_input >> bls;
	d.running = dec_bool(bls, 1), d.result = dec_bool(bls);
	*this >> *d.tbl >> source;
	input::source = dict_r.get_lexeme(s2ws(source));
	int16_t footer; *this >> footer;
	DBG(assert(footer == (int16_t)0x8362));
	return *this;
}
size_t archive::size(const driver& d) {
	size_t s = header_size()
		+ bdd_size()
		+ size(d.pd)
		+ 3 * sizeof(int_t)
		+ size(d.builtin_rels)
		+ size(d.transformed_strings)
		+ size(d.strs_extra)
		+ size(d.rels)
		+ size(d.vars)
		+ size(d.rp)
		+ size(d.opts)
		+ size(d.std_input)
		+ sizeof(unsigned char)
		+ tables_size(d)
		+ size(input::source)
		+ sizeof(int16_t);
	DBG(o::dbg() << L"driver size: " << s
		<< L" tbls: " << size(*(d.tbl))
		<< L" (includes dict: " << size(d.tbl->dict)
		<< L") bdd: " << bdd_size()
		<< L" (" << V->size() << L" nodes) input.size: "
		<< size(input::source)
		<< sizeof(int16_t)
		<< std::endl;)
	return s;
}

archive& archive::write_bdd() {
	*this << V->size();
	write(V->data(), V->size() * 3 * sizeof(int_t));
	return *this;
}
archive& archive::read_bdd() {
	size_t nsize;
	*this >> nsize;
	size_t s = nsize * 3 * sizeof(int_t);
	//DBG(o::dbg() << L"loading bdd size: " << s << endl;)
	V = std::make_unique<bdd_mmap>(nsize, bdd{0,0,0},
		memory_map_allocator<bdd>("", bdd_mmap_mode));
	read((char *)V->data(), s);
	//for (size_t i = 0; i != V->size(); ++i) {
	//	bdd& b = (*V)[i];
	//	DBG(o::dbg() << i << L" "
	//		<< b.v << L' '
	//		<< b.h << L' '
	//		<< b.l << L' ' << endl;)
	//}
	return *this;
}
size_t archive::bdd_size() {
	size_t s = V->size() * 3 * sizeof(int_t) + sizeof(size_t);
	return s;
}

archive& archive::operator<<(const std::tuple<int_t, int_t, int_t, size_t, size_t, size_t, uints>& rcm) {
	return *this
		<< std::get<0>(rcm)
		<< std::get<1>(rcm)
		<< std::get<2>(rcm)
		<< std::get<3>(rcm)
		<< std::get<4>(rcm)
		<< std::get<5>(rcm)
		<< std::get<6>(rcm);
}
archive& archive::operator>>(std::tuple<int_t, int_t, int_t, size_t, size_t, size_t, uints>& rcm) {
	return *this
		>> std::get<0>(rcm)
		>> std::get<1>(rcm)
		>> std::get<2>(rcm)
		>> std::get<3>(rcm)
		>> std::get<4>(rcm)
		>> std::get<5>(rcm)
		>> std::get<6>(rcm);
}
size_t archive::size(
	const std::tuple<int_t, int_t, int_t, size_t, size_t, size_t, uints>& t)
{
	return 3 * sizeof(int_t) + 3 * sizeof(size_t)
		+ size((uints)std::get<6>(t));
}
