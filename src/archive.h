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
#ifndef __ARCHIVE_H__
#define __ARCHIVE_H__
#include <cstring>
#include "driver.h"
#include "memory_map.h"

using lexeme_range = std::array<size_t, 2>;

inline static mmap_mode bool2mode(bool write) {
	return write ? MMAP_WRITE : MMAP_READ;
}

class archive {
public:
	enum type { NONE, DRIVER, BDD };
	const size_t latest_version = 0;
private:
	type type_ = DRIVER;
	memory_map mm_;
	void* data_ = 0;
	size_t pos_ = 0;
	size_t size_ = 0;
	size_t version_ = 0;
	dict_t* dict = 0;
public:
	// archive with mmap
	archive(std::string filename, size_t s, bool mmap_writeable)
		: archive(NONE, filename, s, mmap_writeable) {}
	archive(type typ, std::string filename, size_t s, bool mmap_writeable)
		: type_(typ),
		mm_(filename.c_str(), s, bool2mode(mmap_writeable)),
		data_(mm_.data()), size_(s)
	{
		// DBG(o::dbg()<<
		// 	L"archive (mmap): " << s2ws(filename)
		// 	<< L" size: " << s << L" writeable: " << mmap_writeable
		// 	<< L" map size: " << mm_.size()
		// <<std::endl;)
	}
	// archive with provided data pointer
	archive(void* data, size_t s) : archive(NONE, data, s) {};
	archive(type typ, void* data, size_t s) : type_(typ), mm_(),
		data_(data), size_(s)
	{
		// DBG(o::dbg()<<
		// 	L"archive (ptr): " << (char*)data << L" " << &data
		// 	<< L" size: " << s
		// 	<< L" map size: " << mm_.size()
		// <<std::endl;)
	}
	virtual ~archive() { mm_.close(); }

	dict_t dict_fallback;
	dict_t* get_dict() { return dict ? dict : &dict_fallback; }
	
	unsigned char enc_bools(std::initializer_list<bool> list);
	bool dec_bool(unsigned char bls, int pos = 0);

	void write(const char* data, size_t s);
	void read(char* data, size_t s);

	void write(const void* data, size_t s);
	void read(void* data, size_t s);

	// common writer for vector/set/map
	template <typename T>
	archive& write_container(const T& v) {
		*this << (size_t) v.size();
		for (auto m : v) *this << m;
		return *this;
	}

	// vectors
	template <typename T>
	archive& operator<<(const std::vector<T>& v);
	template <typename T>
	archive& operator>>(std::vector<T>& v);
	template <typename T>
	static size_t vecsize(const std::vector<T>& v);
	template <typename T>
	static size_t size(const std::vector<T>& v) { return vecsize(v); }
	//template <typename V, typename T>
	//static size_t size(const std::vector<T>& v) {
	//	return sizeof(size_t) + v.size() * sizeof(T); }
	static size_t size(const std::vector<spbdd_handle>& v) {
		return vecsize(v); }

	// sets
	template <typename T, typename... U>
	archive& operator<<(const std::set<T, U...>& v);
	template <typename T, typename... U>
	archive& operator>>(std::set<T, U...>& v);
	archive& operator>>(std::set<term> &st);
	archive& operator>>(std::set<level> &levels);
	template <typename T, typename... U>
	static size_t setsize(const std::set<T, U...>& v);
	template <typename T>
	static size_t setsize(const std::set<T>& v);
	template <typename T>
	static size_t size(const std::set<T>& v) { return setsize(v); }
	template <typename T, typename... U>
	static size_t size(const std::set<T, U...>& v) { return setsize(v); }
	//static size_t size(const std::set<lexeme>& lxms);
	//static size_t size(const std::set<lexeme, lexcmp>& lxms);

	// maps
	template <typename Key, typename T>
	archive& operator<<(const std::map<Key, T>& m);
	template <typename Key, typename T>
	archive& write_map(const std::map<Key, T>& m);
	template <typename Key, typename T>
	archive& write_unordered_map(const std::unordered_map<Key, T>& m);
	template <typename Key, typename T>
	archive& operator>>(std::map<Key, T>& m) { return read_map<Key, T>(m); }
	template <typename Key, typename T, typename C>
	archive& read_map(std::map<Key, T, C>& m);
	template <typename Key, typename T>
	archive& read_map(std::map<Key, T>& m);
	archive& operator>>(std::map<ntable, std::set<ntable>>& deps);
	archive& operator>>(std::map<ntable, std::set<term>>& mhits);
	archive& operator>>(std::map<multi_arg, std::set<alt_arg>>& minvtyps);
	archive& operator>>(std::map<ntable, std::set<tbl_alt>>& tblbodies);
	archive& operator>>(std::map<alt_arg, multi_arg>& mtyps);
	archive& operator>>(std::map<tbl_alt, tbl_alt>& altordermap);
	template <typename Key, typename T>
	static size_t mapsize(const std::map<Key, T>& m);
	template <typename Key, typename T, typename C>
	static size_t mapsize(const std::map<Key, T, C>& m);
	template <typename Key, typename T>
	static size_t size(const std::map<Key, T>& m) {
		return mapsize<Key, T>(m); }

	template <typename Key, typename T>
	archive& operator<<(const std::pair<Key, T>& p);

	archive& write_header();
	archive& read_header();
	static size_t header_size();

	archive& operator<<(const int_t&);
	archive& operator>>(int_t&);
	static size_t size(int_t) { return sizeof(int_t); }

	archive& operator<<(const int16_t&);
	archive& operator>>(int16_t&);
	static size_t size(int16_t) { return sizeof(int16_t); }

	archive& operator<<(const size_t&);
	archive& operator>>(size_t&);
	static size_t size(size_t) { return sizeof(size_t); }

	archive& operator<<(const unsigned int&);
	archive& operator>>(unsigned int&);
	static size_t size(uint_t) { return sizeof(uint_t); }

	archive& operator<<(const unsigned char&);
	archive& operator>>(unsigned char&);
	static size_t size(unsigned char) { return 1; }

	archive& operator<<(const char&);
	archive& operator>>(char&);
	static size_t size(char) { return 1; }

	archive& operator<<(const lexeme&);
	archive& operator>>(lexeme&);
	static size_t size(const lexeme&);

	archive& operator<<(const lexeme_range&);
	archive& operator>>(lexeme_range&);

	archive& operator<<(const std::wstring&);
	archive& operator>>(std::wstring&);
	static size_t size(const std::wstring& s) { return size(ws2s(s)); }

	archive& operator<<(const std::string&);
	archive& operator>>(std::string&);
	static size_t size(const std::string& s) {
		return s.size() + sizeof(size_t); }

	archive& operator<<(const spbdd_handle&);
	archive& operator>>(spbdd_handle&);
	static size_t size(const spbdd_handle&) { return sizeof(int_t); }
	static size_t size(const bdd_handle&) { return sizeof(int_t); }

	archive& operator<<(const dict_t&);
	archive& operator>>(dict_t&);
	static size_t size(const dict_t&);

	archive& operator<<(const term&);
	archive& operator>>(term&);
	static size_t size(const term&);

	archive& operator<<(const rule&);
	archive& operator>>(rule&);
	static size_t size(const rule&);

	archive& operator<<(const sig&);
	archive& operator>>(sig&);
	static size_t size(const sig&);

	archive& operator<<(const alt_arg&);
	archive& operator>>(alt_arg&);
	static size_t size(const alt_arg&);

	archive& operator<<(const tbl_arg&);
	archive& operator>>(tbl_arg&);
	static size_t size(const tbl_arg&);

	archive& operator<<(const multi_arg&);
	archive& operator>>(multi_arg&);
	static size_t size(const multi_arg&);

	archive& operator<<(const infer_types&);
	archive& operator>>(infer_types&);
	static size_t size(const infer_types&);

	archive& operator<<(const union_type&);
	archive& operator>>(union_type&);

	archive& operator<<(const sub_type&);
	archive& operator>>(sub_type&);

	archive& operator<<(const record_type&);
	archive& operator>>(record_type&);

	archive& operator<<(const compound_type&);
	archive& operator>>(compound_type&);
	static size_t size(const compound_type&);

	archive& operator<<(const primitive_type&);
	archive& operator>>(primitive_type&);
	static size_t size(const primitive_type&);

	archive& operator<<(const ::type&);
	archive& operator>>(::type&);
	static size_t size(const ::type&);

	archive& operator<<(const argtypes&);

	archive& operator<<(const bitsmeta&);
	archive& operator>>(bitsmeta&);
	static size_t size(const bitsmeta&);

	archive& operator<<(const elem&);
	archive& operator>>(elem&);
	static size_t size(const elem&);

	archive& operator<<(const raw_term&);
	archive& operator>>(raw_term&);
	static size_t size(const raw_term&);

	archive& operator<<(const directive&);
	archive& operator>>(directive&);
	static size_t size(const directive&);

	archive& operator<<(const production&);
	archive& operator>>(production&);
	static size_t size(const production&);

	archive& operator<<(const raw_rule&);
	archive& operator>>(raw_rule&);
	static size_t size(const raw_rule&);

	archive& operator<<(const raw_prog&);
	archive& operator>>(raw_prog&);
	static size_t size(const raw_prog&);

	archive& operator<<(const raw_progs&);
	archive& operator>>(raw_progs&);
	static size_t size(const raw_progs&);

	archive& operator<<(const option&);
	static size_t size(const option&);

	archive& operator<<(const options&);
	archive& operator>>(options&);
	static size_t size(const options&);

	archive& operator<<(const prog_data&);
	archive& operator>>(prog_data&);
	static size_t size(const prog_data&);

	archive& operator<<(const strs_t&);
	archive& operator>>(strs_t&);
	static size_t size(const strs_t&);

	archive& operator<<(const flat_prog&);
	archive& operator>>(flat_prog&);
	static size_t size(const flat_prog&);

	archive& operator<<(const table&);
	archive& read_table(tables&);
	static size_t size(const table&);

	archive& operator<<(const tables&);
	archive& operator>>(tables&);
	static size_t size(const tables&);

	archive& write_tables(const driver& d) { return *this << *d.tbl; }
	static size_t tables_size(const driver& d) { return size(*(d.tbl)); }

	archive& operator<<(const driver&);
	archive& operator>>(driver&);
	static size_t size(const driver&);

	archive& write_bdd();
	archive& read_bdd();
	static size_t bdd_size();

	// range_compound_memo
	archive& operator<<(const std::tuple<
		int_t, int_t, int_t, size_t, size_t, size_t, uints>&);
	archive& operator>>(std::tuple<
		int_t, int_t, int_t, size_t, size_t, size_t, uints>&);
	static size_t size(const std::tuple<
		int_t, int_t, int_t, size_t, size_t, size_t, uints>&);
};

#endif
