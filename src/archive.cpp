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
#include "err.h"

using std::endl;

#ifdef DEBUG
//#define DEBUG_ARCHIVE_POS
#endif
#ifdef DEBUG_ARCHIVE_POS
#define POS(x)      pos(x);
#define SPOS(x, v)  spos((x), (v), s);
#define SPOS0(x)    spos((x), (char)0, s);
#define SPOSL(x, l) sposl((x), (l), s);
//#define SPOS(x)     spos((x), (size_t)-1, s);
#else
#define POS(x)
#define SPOS(x, v)
#define SPOS0(x)
#define SPOSL(x, l)
#endif

archive::archive(type typ, const std::string& filename, size_t s, bool mm_write)
	: type_(typ), mm_(filename, s, bool2mode(mm_write)), data_(mm_.data()),
	size_(s)
{
	if (mm_.error) error = true, throw_runtime_error(err_fnf, filename);
}

unsigned char archive::enc_bools(std::initializer_list<bool> list) {
	DBG(assert(list.size() <= 8);)
	unsigned char i = 0, r = 0;
	for (auto b : list) r |= (unsigned char) (b << i++);
	return r;
}

bool archive::dec_bool(unsigned char bls, int pos) {
	return (bls >> pos) & 1;
}

archive& archive::write(const char* data, size_t s) {
	// DBG(o::dbg() << "write const char* data[0]: " << &data << ' ' << (int)data[0] << std::endl;)
	memcpy(((char*)data_) + pos_, data, s);
	pos_ += s;
	return *this;
}
archive& archive::read(char* data, size_t s) {
	// o::dbg() << "read char* data: " << &data << std::endl;
	memcpy(data, ((char*)data_) + pos_, s);
	pos_ += s;
	return *this;
}

archive& archive::write(const void* data, size_t s) {
	// DBG(o::dbg() << "write const void* data: " << &data << ' ' << data  << std::endl;)
	return write(static_cast<const char*>(data), s);
}
archive& archive::read(void* data, size_t s) {
	// o::dbg() << "read void* data: " << &data << std::endl;
	return read(static_cast<char*>(data), s);
}

// arrays
template <typename T, size_t N>
archive& archive::operator<<(const std::array<T, N>& a) {
	for (auto m : a) *this << m;
	return *this;
}
template <typename T, size_t N>
archive& archive::operator>>(std::array<T, N>& a) {
	for (size_t i = 0; i != N; ++i) *this >> a[i];
	return *this;
}
template <typename T, size_t N>
size_t archive::size(const std::array<T, N>& a) {
	size_t s = sizeof(size_t);
	for (auto e : a) s += size(e);
	return s;
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
		//DBG(o::dbg() << "i: " << i << " ";)
		term t;
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
			term t;
			*this >> t;
			st.insert(t);			
		} while (tsize-- > 0);
		mhits.emplace(nt, st);
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
	return mapsize<Key, T>(m);
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
	//DBG(o::dbg() << "writing int_t: " << val << endl;)
	write((const char*)&val, sizeof(int_t));
	return *this;
}
archive& archive::operator>>(int_t& val) {
	read(&val, sizeof(int_t));
	//DBG(o::dbg() << "reading int_t: " << val << endl;)
	return *this;
}

archive& archive::operator<<(const int16_t& val) {
	//DBG(o::dbg() << "writing int16_t: " << val << endl;)
	write((const char*) &val, sizeof(int16_t));
	return *this;
}
archive& archive::operator>>(int16_t& val) {
	read(&val, sizeof(int16_t));
	//DBG(o::dbg() << "reading int16_t: " << val << endl;)
	return *this;
}

archive& archive::operator<<(const size_t& val) {
	// DBG(o::dbg() << "writing size_t: " << val << endl;)
	write((const char*) &val, sizeof(size_t));
	return *this;
}

archive& archive::operator>>(size_t& val) {
	read((char*) &val, sizeof(size_t));
	// DBG(o::dbg() << "reading size_t: " << val << endl;)
	return *this;
}

archive& archive::operator<<(const unsigned int& val) {
	//DBG(o::dbg() << "writing uint: " << val << endl;)
	write((const char*) &val, sizeof(unsigned int));
	return *this;
}
archive& archive::operator>>(unsigned int& val) {
	read(&val, sizeof(unsigned int));
	//DBG(o::dbg() << "reading uint: " << val << endl;)
	return *this;
}

archive& archive::operator<<(const unsigned char& val) {
	// DBG(o::dbg() << "writing char: " << val << endl;)
	write((const char*) &val, sizeof(unsigned char));
	return *this;
}
archive& archive::operator>>(unsigned char& val) {
	read(&val, sizeof(unsigned char));
	// DBG(o::dbg() << "reading char: " << val << endl;)
	return *this;
}

archive& archive::operator<<(const char& val) {
	// DBG(o::dbg() << "writing char: " << val << endl;)
	write((const char*) &val, sizeof(char));
	return *this;
}
archive& archive::operator>>(char& val) {
	read(&val, sizeof(char));
	// DBG(o::dbg() << "reading char: " << val << endl;)
	return *this;
}

archive& archive::operator<<(const lexeme& val) {
//	//DBG(o::dbg() << "writing lexeme: " << lexeme2str(val) << endl;)
	auto it = lmap_.find(val);
	DBG(if (it == lmap_.end()) assert(0);)
	return *this << it->second;
}
archive& archive::operator>>(lexeme& r) {
	size_t pos;
	*this >> pos; r[0] = (ccs) data_ + pos;
	*this >> pos; r[1] = (ccs) data_ + pos;
	return *this;
}
size_t archive::size(const lexeme& /*l*/) {
	return 2 * sizeof(size_t);
}

archive& archive::operator<<(const lexeme_range& r) {
	return *this << r[0] << r[1];
}
archive& archive::operator>>(lexeme_range& r) {
	return *this >> r[0] >> r[1];
}

archive& archive::operator<<(const string_t& val) {
	//COUT << "writing string: " << val
	// 	 << " size: " << val.size() << endl;
	//POS("string begin")
	*this << val.size();
	if (val.size() > 0) write((const char*)val.c_str(), val.size());
	*this << (char)0;
	//POS("string end")
	return *this;
}
archive& archive::operator>>(string_t& val) {
	//POS("string begin")
	size_t l; *this >> l;
	//DBG(o::dbg() << "reading string, size: " << l << endl;)
	if (l == 0) return (val = string_t(), ++pos_), *this;
	val = string_t(read_ccs(l));
	//POS("string end")
	return *this;
}

archive& archive::operator<<(const spbdd_handle& val) {
	//DBG(o::dbg() << "writing spbdd_handle: " << (val ? val->b : (int_t)0) << endl;)
	return *this << (val ? val->b : (int_t)0);
}
archive& archive::operator>>(spbdd_handle& val) {
	int_t b; *this >> b;
	val = bdd_handle::get(b);
	//DBG(o::dbg() << "reading spbdd_handle: " << b << endl;)
	return *this;
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

archive& archive::operator<<(const elem& e) {
	*this << (unsigned char)e.type;
	switch (e.type) {
		case elem::ARITH: *this << (unsigned char)e.arith_op; break;
		case elem::NUM:   *this << e.num; break;
		case elem::CHR:   *this << (uint32_t)e.ch; break;
		case elem::SYM:
		case elem::STR:
		case elem::VAR:   *this << e.e;
		default:;
	}
	return *this;
}
archive& archive::operator>>(elem& e) {
	unsigned int ch;
	unsigned char tmp; *this >> tmp, e.type = (elem::etype)tmp;
	switch (e.type) {
		case elem::ARITH: *this>>tmp, e.arith_op=(t_arith_op)tmp; break;
		case elem::NUM:   *this >> e.num; break;
		case elem::CHR:   *this >> ch, e.ch = (char32_t)ch; break;
		case elem::SYM:
		case elem::STR:
	 	case elem::VAR:   *this >> e.e;
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
		case elem::CHR:   s += sizeof(char32_t); break;
		case elem::SYM:
		case elem::STR:
	 	case elem::VAR:   s += 2 * sizeof(size_t); break;
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
	*this >> d.arg;
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
	//POS("rp.d")
	*this << rp.d;
	//POS("rp.g")
	*this << rp.g;
	//POS("rp.r")
	*this << rp.r;
	//POS("rp.builtins")
	*this << rp.builtins;
	//POS("rp end")
	return *this;
}
archive& archive::operator>>(raw_prog& rp) {
	size_t nsize;
	lexeme l;
	//POS("rp.d")
	*this >> rp.d;
	//POS("rp.g")
	*this >> rp.g;
	//POS("rp.r")
	*this >> rp.r;
	//POS("rp.builtins size")
	*this >> nsize;
	//POS("rp.builtins pairs")
	for (size_t i = 0; i != nsize; ++i)
		*this >> l, rp.builtins.insert(l);
	//POS("rp end")
	return *this;
}
size_t archive::size(const raw_prog& rp) {
	size_t s = 0;
	//SPOS("rp.d", rp.d)
	s += size(rp.d);
	//SPOS("rp.g", rp.g)
	s += size(rp.g);
	//SPOS("rp.r", rp.r)
	s += size(rp.r);
	//SPOS("rp.builtins", rp.builtins)
	s += size(rp.builtins);
	return s;
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

archive& archive::write_ccs(ccs s, size_t l) {
	*this << l; write(s, l);
	return *this;
}

archive& archive::write_ccs(ccs s) {
	size_t l = strlen(s);
	return write_ccs(s, l);
}

ccs archive::read_ccs(size_t l) {
	ccs s = (ccs)data_ + pos_;
	//POS("read_chars")
	pos_ += l * sizeof(char) + 1;
	//POS("chars read")
	return s;
}

archive& archive::operator<<(const input& in) {
	//POS("input bools")
	*this << enc_bools({ in.newseq });
	//POS("input data")
	//COUT << "writing in.beg_: " << (void*)in.beg_ << " " << in.beg_ << endl;
	write_ccs(in.beg_);
	*this << '\0';
	//POS("input end")
	return *this;
}
archive& archive::operator>>(input& in) {
	unsigned char tmp;
	//POS("input bools")
	*this >> tmp; in.newseq = dec_bool(tmp);
	in.allocated_ = false;
	//POS("input data")
	*this >> in.size_;
	in.beg_ = read_ccs(in.size_);
	//COUT << "loading in.size_: " << in.size_ << " in.beg_: " << (void*)in.beg_ << " " << in.beg_ << endl;
	in.data_ = in.beg_;
	//POS("input end")
	return *this;
}
size_t archive::size(const input& in) {
	return 2 * sizeof(unsigned char) +
		+ sizeof(size_t)
		+ strlen(in.beg_);
}

archive& archive::operator<<(const option& o) {
	//POS("option type")
	*this << (unsigned char)o.t;
	//POS("option name")
	*this << to_string_t(o.n[0]);
	//COUT << "option name written: " << o.n[0] << " type: " << (int_t) o.t << endl;
	//POS("option value")
	switch (o.t) {
		case option::type::INT:    *this << o.v.v_i; break;
		case option::type::BOOL:   *this << enc_bools({o.v.v_b}); break;
		case option::type::STRING: *this << to_string_t(o.v.v_s); break;
		default: ;
	}
	//POS("option end")
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
	//POS("options size")
	for (auto it : o.opts) if (!it.second.is_undefined()) n++;
	*this << n;
	//POS("option pairs")
	for (auto it : o.opts) if (!it.second.is_undefined()) *this<<it.second;
	//POS("options end")
	return *this;
}
archive& archive::operator>>(options& opts) {
	size_t nsize;
	//POS("options size")
	*this >> nsize;
	//POS("option pairs")
	for (size_t i = 0; i != nsize; ++i) {
		int_t val;
		string_t s, n;
		unsigned char uch;
		//POS("option start: type[1]")
		*this >> uch;
		//POS("option name");
		*this >> n;
		//COUT << "name: " << n << " type: " << (int_t)uch << endl;
		// option o; opts.get(n, o);
		//POS("option value")
		switch ((option::type) uch) {
			case option::type::INT:
				*this >> val;
				opts.set(to_string(n), val);
				//COUT << "int written: " << val << endl;
				break;
			case option::type::BOOL:
				*this >> uch;
				opts.set(to_string(n), dec_bool(uch));
				//COUT << "bool read: " << dec_bool(uch) << endl;
				break;
			case option::type::STRING:
				*this >> s;
				opts.set(to_string(n), to_string(s));
				//COUT << "string read: " << s << endl;
				break;
			default: DBGFAIL;
		}
		//POS("option end")
	}
	return *this;
}
size_t archive::size(const options& opts) {
	size_t s = 0;
	//SPOS("options size", s);
	s += sizeof(size_t);
	for (auto it : opts.opts) if (!it.second.is_undefined()) {
		//SPOS("option pair", it.second)
		s += size(it.second);
	}
	//SPOS0("options end")
	return s;
}

archive& archive::operator<<(const prog_data& pd) {
	//POS("std_input")
	*this << pd.std_input;
	//POS("pd.strs")
	*this << pd.strs;
	//POS("pd.bools (bwd)")
	*this << enc_bools({ pd.bwd });
	//POS("pd.n")
	*this << pd.n;
	//POS("pd.start_step")
	*this << pd.start_step;
	//POS("pd.elapsed_steps")
	*this << pd.elapsed_steps;
	//POS("pd end")
	return *this;
}
archive& archive::operator>>(prog_data& pd) {
	unsigned char bls;
	//POS("pd.std_input")
	*this >> pd.std_input;
	//POS("pd.strs")
	*this >> pd.strs;
	//POS("pd.bools (bwd)")
	*this >> bls;
	pd.bwd = dec_bool(bls);
	//POS("pd.n")
	*this >> pd.n;
	//POS("pd.start_step")
	*this >> pd.start_step;
	//POS("pd.elapsed_steps")
	*this >> pd.elapsed_steps;
	//POS("pd end")
	return *this;
}
size_t archive::size(const prog_data& pd) {
	return size(pd.strs) + size(pd.std_input)
		+ sizeof(unsigned char)
		+ 3 * sizeof(size_t);
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
			term t; *this >> t; vt.push_back(t);			
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
	//POS("table signature")
	*this << t.s;
	//POS("table t")
	*this << t.t;
	//POS("table len")
	*this << t.len;
	//POS("table priority")
	*this << t.priority;
	//POS("table r")
	*this << t.r;
	//POS("table bools(ext, unsat, tmp)")
	*this << enc_bools({ t.ext, t.unsat, t.tmp });
	//POS("table idbltin")
	*this << t.idbltin;
	//POS("table bltinargs")
	*this << t.bltinargs;
	//POS("table bltinsize")
	*this << t.bltinsize;
	//POS("table end")
	return *this;
}
archive& archive::read_table(tables& tbls) {
	char bls;
	sig s;
	if (!dict_) dict_ = &tbls.dict;
	//POS("table signature")
	*this >> s;
	//POS("table t")
	table&  t = tbls.tbls[tbls.get_table(s)];
	*this >> t.t;
	//POS("table len")
	*this >> t.len;
	//POS("table priority")
	*this >> t.priority;
	//POS("table r")
	*this >> t.r;
	//POS("table bools(ext, unsat, tmp)")
	*this >> bls;
	t.ext   = dec_bool(bls),
	t.unsat = dec_bool(bls, 1),
	t.tmp   = dec_bool(bls, 2);
	//POS("table idbltin")
	*this >> t.idbltin;
	//POS("table bltinargs")
	*this >> t.bltinargs;
	//POS("table bltinsize")
	*this >> t.bltinsize;
	//POS("table end")
	return *this;
}
size_t archive::size(const table& t) {
	size_t s = 0;
	//SPOS("t.s", t.s)
	s += size(t.s);
	//SPOS("table t", t.t)
	s += size(t.t);
	//SPOS("table len", t.len)
	s += size(t.len);
	//SPOS("table priority", t.priority)
	s += size(t.priority);
	//SPOS("table r", t.r)
	s += size(t.r);
	//SPOS0("table bools")
	s += sizeof(unsigned char);
	//SPOS("table idbltin", t.idbltin)
	s += size(t.idbltin);
	//SPOS("table bltinargs", t.bltinargs)
	s += size(t.bltinargs);
	//SPOS("table bltinsize", t.bltinsize)
	s += size(t.bltinsize);
	//DBG(o::dbg() << "table size: " << t.sign.first << '/' << t.sign.second[0] << ' ' << s
	//	<< " size(bm): " << size(t.bm)
	//	<< " (t.bltinargs.size(): " << t.bltinargs.size()
	//	<< " (t.r.size(): " << t.r.size()
	//	<< std::endl;)
	return s;
}
archive& archive::operator<<(const tables& tbls) {
	//POS("tables rules")
	*this << tbls.rules;
	//POS("tables fronts")
	*this << tbls.fronts;
	//POS("tables levels")
	*this << tbls.levels;
	//POS("tables nstep")
	*this << tbls.nstep;
	//POS("tables tmprels")
	*this << tbls.tmprels;
	//POS("tables deps")
	*this << tbls.deps;
	//POS("tables max_args")
	*this << tbls.max_args;
	//POS("tables range_memo")
	*this << tbls.range_memo;
	//POS("tables goals")
	*this << tbls.goals;
	//POS("tables to_drop")
	*this << tbls.to_drop;
	//POS("tables exts")
	//*this << tbls.exts;
	//POS("tables strs")
	*this << tbls.strs;
	//POS("tables str_rels")
	*this << tbls.str_rels;
	//POS("tables prog_after_fp")
	*this << tbls.prog_after_fp;
	//POS("tables bools(populate_tml_update, print_updates, print_steps)")
	*this << enc_bools({ tbls.populate_tml_update, tbls.print_updates,
			tbls.print_steps });
	//POS("tables tbls size")
	*this << tbls.tbls.size();
	//POS("tables tbls")
	for (size_t  i = 0; i != tbls.tbls.size(); ++i)
		*this << tbls.tbls[i];
	//POS("tables end")
	return *this;
}

archive& archive::operator>>(tables& tbls) {
	unsigned char tmp;
	size_t nsize;
	//POS("tables rules")
	*this >> tbls.rules;
	//POS("tables fronts")
	*this >> tbls.fronts;
	//POS("tables levels")
	*this >> tbls.levels;
	//POS("tables nstep")
	*this >> tbls.nstep;
	//POS("tables tmprels")
	*this >> tbls.tmprels;
	//POS("tables deps")
	*this >> tbls.deps;
	//POS("tables max_args")
	*this >> tbls.max_args;
	//POS("tables range_memo")
	*this >> tbls.range_memo;
	//POS("tables goals")
	*this >> tbls.goals;
	//POS("tables to_drop")
	*this >> tbls.to_drop;
	//POS("tables exts")
	//*this >> tbls.exts;
	//POS("tables strs")
	*this >> tbls.strs;
	//POS("tables str_rels")
	*this >> tbls.str_rels;
	//POS("tables prog_after_fp")
	*this >> tbls.prog_after_fp;
	//POS("tables bools(populate_tml_update, print_updates, print_steps)")
	*this >> tmp;
	tbls.populate_tml_update = dec_bool(tmp);
	tbls.print_updates       = dec_bool(tmp, 1);
	tbls.print_steps         = dec_bool(tmp, 2);
	//POS("tables tbls size")
	*this >> nsize;
	//POS("tables tbls")	
	for (size_t i = 0; i != nsize; ++i) read_table(tbls);
	//POS("tables end")
	//COUT << "dict after load: " << tbls.dict << endl;
	return *this;
}
size_t archive::size(const tables& t) {
	size_t s = 0;
	//SPOS("tables rules", t.rules)
	s += size(t.rules);
	//SPOS("tables fronts", t.fronts)
	s += size(t.fronts);
	//SPOS("tables levels", t.levels)
	s += size(t.levels);
	//SPOS("tables nstep", t.nstep)
	s += size(t.nstep);
	//SPOS("tables tmprels", t.tmprels)
	s += size(t.tmprels);
	//SPOS("tables deps", t.deps)
	s += size(t.deps);
	//SPOS("tables max_args", t.max_args)
	s += size(t.max_args);
	//SPOS("tables range_memo", t.range_memo)
	s += size(t.range_memo);
	//SPOS("tables goals", t.goals)
	s += size(t.goals);
	//SPOS("tables to_drop", t.to_drop)
	s += size(t.to_drop);
	//SPOS("tables exts", t.exts)
	//s += size(t.exts);
	//SPOS("tables strs", t.strs)
	s += size(t.strs);
	//SPOS("tables str_rels", t.str_rels)
	s += size(t.str_rels);
	//SPOS("tables prog_after_fp", t.prog_after_fp)
	s += size(t.prog_after_fp);
	//SPOS0("tables bools")
	s += sizeof(unsigned char);
	//SPOS("tables tbls size", t.tbls.size())
	s += size(t.tbls.size());
	//for (auto p : t.range_memo) s += size(p.first) + sizeof(int_t);
	//SPOS("tables tbls", t.tbls)
	for (size_t i = 0; i != t.tbls.size(); ++i) s += size(t.tbls[i]);
	//SPOS0("tables end")
	return s;
}


archive& archive::add_lexeme_and_map(const dict_t &d, const lexeme& l,bool add){
	//COUT << "add_lexeme_and_map: " << (add ? "" : "no add ") << l << endl;
	size_t inp = header_size() + sizeof(size_t) + sizeof(size_t);
	lexeme_range lr; input* in;
	if (d.ii && d.ii->lexeme_pos(inp, l, &in, lr)) {
		auto it = lmap_.find(l);
		if (it == lmap_.end()) lmap_.insert({ l, lr });
		if (add) lranges_.push_back({ lr, true });
	} else {
		lr = { lpos_, lpos_ };
		auto it = lmap_.find(l);
		if (it == lmap_.end()) { // not in map
			if (l[1]-l[0] > 0) // non-0
				for (ccs c = l[0]; c != l[1]; ++c)
					ldata_.put(*c), ++lpos_, lr[1] = lpos_;
			lmap_.insert({ l, lr });
			if (add) lranges_.push_back({ lr, false });
		} else if (add) lranges_.push_back({ it->second, false });
	}
	return *this;
}

template <typename T>
archive& archive::add_lexemes(const dict_t& d, const T& lxms) {
	for (const lexeme& l : lxms) add_lexeme_and_map(d, l);
	return *this;
}

archive& archive::add_dict_lexemes(const dict_t& d) {
	//POS("dict rels")
	add_lexemes(d, d.rels);
	//POS("dict syms")
	add_lexemes(d, d.syms);
	//POS("dict bltins")
	add_lexemes(d, d.bltins);
	//POS("dict strs_extra")
	add_lexemes(d, d.strs_extra);
	//POS("dict end")
	return *this;
}

archive& archive::write_lexemes() {
	write_ccs(ldata_.str().c_str());
	//POS("lexeme ranges")
	//*this << lranges_.size();
	for (auto& r : lranges_) {
		//POS("lexeme")
		if (r.second) *this << r.first; // points to input, no recount
		else *this<<lexeme_range{ r.first[0]+lpos_, r.first[1]+lpos_}; 
	}
	//POS("lexemes end")
	return *this;
}

archive& archive::operator<<(const driver& d) {
	write_header();
	POS("inputs")
	*this << d.ii->size();
	if (d.ii->size()) {
		*this << d.current_input_id;
		input *in = d.ii->first();
		while (in) {
			*this << *in;
			in = in->next();
		}
	}
	POS("dict")
	dict_t& dr = d.tbl->dict;
	dict_ = &dr;
	*this << dict_->rels.size();
	*this << dict_->syms.size();
	*this << dict_->bltins.size();
	*this << dict_->strs_extra.size();
	*this << d.strs_extra.size();
	*this << d.rels.size();
	*this << d.vars.size();
	lpos_ = pos_ + sizeof(size_t);
	POS("dict lexemes")
	add_dict_lexemes(*dict_);
	POS("strs_extra lexemes")
	add_lexemes(*dict_, d.strs_extra);
	add_lexemes(*dict_, d.rels);
	add_lexemes(*dict_, d.vars);
	//for (const raw_prog& p : d.rp.p) 
	{ // TODO
		const raw_prog& p = d.rp.p;
		for (const lexeme& l : p.builtins)
			add_lexeme_and_map(dr, l, false);
		for (const directive& dir : p.d)
			add_lexeme_and_map(dr, dir.arg, false);
		for (const raw_rule& r : p.r) {
			for (const raw_term& rt : r.h)
				for (const elem& e : rt.e)
					add_lexeme_and_map(dr, e.e, false);
			for (const std::vector<raw_term>& vrt : r.b)
				for (const raw_term& rt : vrt)
					for (const elem& e : rt.e)
					add_lexeme_and_map(dr, e.e, false);
		}
	}
	POS("lexemes data and lexemes")
	write_lexemes();
	POS("bdd")
	write_bdd();
	//POS("opts");
	*this << d.opts;
	//POS("pd")
	*this << d.pd;
	//POS("nums")
	*this << d.nums;
	//POS("chars")
	*this << d.chars;
	//POS("syms")
	*this << d.syms;
	//POS("builtin_rels")
	*this << d.builtin_rels;
	//POS("transformed_strings")
	*this << d.transformed_strings;
	//POS("rp")
	*this << d.rp;
	//POS("bools(result, running)")
	*this << enc_bools({ d.result, d.running });
	//POS("tables")
	write_tables(d);
	//POS("footer")
	*this << int16_t(0x8362);
	//POS("end")
	return *this;
}

archive& archive::operator>>(driver& d) {
	//DBG(o::dbg() << "loading driver\n";)
	size_t nsize;
	std::string s;
	char bls;
	dict_t& dct = d.tbl->dict;
	dict_ = &(dct);
	read_header();

	POS("inputs")
	*this >> nsize;
	if (nsize > 0) {
		*this >> d.current_input_id;
		do {
			d.ii->add(std::make_unique<input>((void*)0, (size_t)0));
			*this >> *(d.ii->last());
		} while (--nsize > 0);
		d.current_input = d.ii->first();
		for (size_t i = 0; i != d.current_input_id; ++i)
			d.current_input = d.current_input->next();
	}

	POS("dict")
	size_t nrels, nsyms, nbltins, ndse, nse, ndrels, nvars;
	*this >> nrels >> nsyms >> nbltins >> ndse >> nse >> ndrels >> nvars;
	POS("extra lexemes data")
	*this >> nsize; pos_ += nsize; // skip (strs) extra lexemes data
	lexeme_range r;
	#define LX (lexeme{ (ccs) data_ + r[0], (ccs) data_ + r[1] }) 
	//POS("rel lexemes")
	for (size_t i = 0; i != nrels; ++i) *this >> r,dct.get_rel(LX);
	//POS("sym lexemes")
	for (size_t i = 0; i != nsyms; ++i) *this >> r,dct.get_sym(LX);
	//POS("bltin lexemes")
	for (size_t i = 0; i !=nbltins;++i) *this >> r,dct.get_bltin(LX);
	//POS("strs_extra lexemes")
	for (size_t i = 0; i != ndse;  ++i) *this >>r,dct.strs_extra.insert(LX);
	//POS("dict strs_extra lexemes")
	for (size_t i = 0; i != nse;   ++i) *this >> r,d.strs_extra.insert(LX);
	//POS("dict rels lexemes")
	for (size_t i = 0; i != ndrels;++i) *this >> r, d.rels.insert(LX);
	//POS("dict vars lexemes")
	for (size_t i = 0; i != nvars; ++i) *this >> r, d.vars.insert(LX);
	#undef LX
	POS("bdd")
	read_bdd();
	//POS("opts")
	*this >> d.opts;
	//POS("pd");
	*this >> d.pd;
	//POS("nums")
	*this >> d.nums;
	//POS("chars")
	*this >> d.chars;
	//POS("syms")
	*this >> d.syms;
	//POS("buildtin_rels")
	*this >> d.builtin_rels;
	//POS("transformed_strings")
	*this >> d.transformed_strings;
	//POS("rp")
	*this >> d.rp;
	//POS("bools(running, result")
	*this >> bls;
	d.running = dec_bool(bls, 1), d.result = dec_bool(bls);
	//POS("tables")
	*this >> *d.tbl;
	//POS("footer")

	int16_t footer; *this >> footer;
	//POS("end")
	DBG(assert(footer == (int16_t)0x8362)); // TODO what to do if not true?
	return *this;
}

size_t archive::dict_and_lexemes_size(const driver& drv) {
	const dict_t& d = drv.tbl->dict;
	size_t beg = header_size() + sizeof(size_t) + sizeof(size_t);
	size_t s = 0;
	//SPOS0("dict_and_lexemes_size begin")
	s += 8 * sizeof(size_t) + (2 * sizeof(size_t) * (d.rels.size() +
		d.syms.size() + d.bltins.size() + d.strs_extra.size() +
		drv.strs_extra.size() + drv.rels.size() + drv.vars.size()));
	std::set<lexeme, lexcmp> lexemes{};
	auto add_lexeme_size =
		[&d, &lexemes, &beg, &s] (const lexeme& l) {
			input* in; lexeme_range lr;
			//COUT << "add lexeme size: " << l[1]-l[0] << " " << l << endl;
			//s += l[1]-l[0];
			if ((!d.ii->lexeme_pos(beg, l, &in, lr))
				&& (lexemes.insert(l).second)) {
					//COUT << "adding lexeme size: " << l[1]-l[0] << endl;
					s += l[1]-l[0];
				}
		};
	//SPOS0("dict rels")
	for (const lexeme& l : d.rels)             add_lexeme_size(l);
	//SPOS0("dict syms")
	for (const lexeme& l : d.syms)             add_lexeme_size(l);
	//SPOS0("dict bltins")
	for (const lexeme& l : d.bltins)           add_lexeme_size(l);
	//SPOS0("dict strs_extra")
	for (const lexeme& l : d.strs_extra)       add_lexeme_size(l);
	//SPOS0("driver strs_extra")
	for (const lexeme& l : drv.strs_extra)     add_lexeme_size(l);
	//SPOS0("driver rels")
	for (const lexeme& l : drv.rels)           add_lexeme_size(l);
	//SPOS0("driver varsd")
	for (const lexeme& l : drv.vars)           add_lexeme_size(l);
	//SPOS0("driver raw prog")
	//for (const raw_prog& p : drv.rp.p)
	{ // TODO
		const raw_prog& p = drv.rp.p;
		//SPOS0("rp builtins")
		for (const lexeme& l : p.builtins) add_lexeme_size(l);
		//SPOS0("rp directive args")
		for (const directive& dir : p.d)   add_lexeme_size(dir.arg);
		//SPOS0("rp raw rule")
		for (const raw_rule& r : p.r) {
			//SPOS0("rp h")
			for (const raw_term& rt : r.h)
				for (const elem& e : rt.e)
					           add_lexeme_size(e.e);
			//SPOS0("rp b")
			for (const std::vector<raw_term>& vrt : r.b)
				for (const raw_term& rt : vrt)
					for (const elem& e : rt.e)
						   add_lexeme_size(e.e);
		}
	}
	//SPOS0("driver_and_lexemes_size_end")
	return s;
}

size_t archive::size(const driver& d) {
	size_t s = header_size();
	//SPOS("inputs size", s);
	s += sizeof(size_t);
	if (d.ii->size()) {
		s += sizeof(size_t);
		input *in = d.ii->first();
		while (in) s += size(*in), in = in->next();
	}
	//SPOS0("dict")
	s += dict_and_lexemes_size(d);
	//SPOS("bdd", bdd_size())
	s += bdd_size();
	//SPOS("opts", d.opts);
	s += size(d.opts);
	//SPOS("pd", d.pd)
	s += size(d.pd);
	//SPOS("nums", (int_t)0)
	s += sizeof(int_t);
	//SPOS("chars", (int_t)0)
	s += sizeof(int_t);
	//SPOS("syms", (int_t)0)
	s += sizeof(int_t);
	//SPOS("builtin_rels", d.builtin_rels)
	s += size(d.builtin_rels);
	//SPOS("transformed_strings", d.transformed_strings)
	s += size(d.transformed_strings);
	//SPOS("rp", d.rp)
	s += size(d.rp);
	//SPOS0("bools(result, running)")
	s += sizeof(unsigned char);
	//SPOS("tables", (size_t)0)
	s += tables_size(d);
	//SPOS("footer", (int16_t)0)
	s += sizeof(int16_t);
	//SPOS0("end")
	//DBG(o::dbg() << "driver size: " << s
	//	<< " tbls: " << size(*(d.tbl))
	//	//<< " (includes dict: " << size(d.tbl->dict) << ")"
	//	<< " bdd: " << bdd_size()
	//	<< " (" << V.size() << " nodes)" << std::endl;)
	return s;
}

archive& archive::write_bdd() {
	*this << V.size();
	write(V.data(), V.size() * 3 * sizeof(int_t));
	return *this;
}
archive& archive::read_bdd() {
	size_t nsize;
	//POS("reading bdd size")
	*this >> nsize;
	//COUT << "nsize: " << nsize << endl;
	size_t s = nsize * 3 * sizeof(int_t);
	//COUT << "loading bdd size: " << nsize << " " << s << endl;
	V = bdd_mmap(nsize, bdd{0,0,0},
		memory_map_allocator<bdd>("", bdd_mmap_mode));
	read((char *)V.data(), s);
	//for (size_t i = 0; i != V.size(); ++i) {
	//	bdd& b = (*V)[i];
	//	DBG(COUT << i << " "
	//		<< b.v << ' '
	//		<< b.h << ' '
	//		<< b.l << ' ' << endl;)
	//}
	return *this;
}
size_t archive::bdd_size() {
	size_t s = V.size() * 3 * sizeof(int_t) + sizeof(size_t);
	return s;
}

