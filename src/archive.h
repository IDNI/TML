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
	dict_t* dict_ = 0;
	std::basic_ostringstream<char_t> ldata_;
	size_t lpos_ = 0;
	std::map<lexeme, lexeme_range, lexcmp> lmap_;
	std::vector<std::pair<lexeme_range, bool>> lranges_;
	ccs lexemes_extra_ = 0;
public:
	bool error = false;
	// archive with mmap
	archive(const std::string& filename, size_t s, bool mm_write)
		: archive(NONE, filename, s, mm_write) {}
	archive(type typ, const std::string& filename, size_t s, bool mm_write);
	// archive with provided data pointer
	archive(void* data, size_t s) : archive(NONE, data, s) {}
	archive(type typ, void* data, size_t s) : type_(typ), mm_(),
		data_(data), size_(s) {}

	// pos and spos(l) are debugging methods. Use macros POS, SPOS, SPOS0
	// and SPOSL to use them and define DEBUG_ARCHIVE_POS.
	template <typename T>
	static void spos(const std::string& n, const T& v, size_t s) {
		sposl(n, archive::size(v), s);
	}
	static void sposl(const std::string& n, size_t l, size_t s) {
		COUT << "spos: \t" << s << " \t0x" << std::hex << s
			<< std::dec << " \t" << n << "\t size: " << l <<
			std::endl;
	}
	archive& pos(const std::string& n) {
		COUT << "pos: \t" << pos_ << " \t0x" << std::hex <<
			pos_ << std::dec << " \t" << n << std::endl;
		return *this;
	}

	dict_t dict_fallback_;
	dict_t* get_dict() { return dict_ ? dict_ : &dict_fallback_; }
	
	unsigned char enc_bools(std::initializer_list<bool> list);
	bool dec_bool(unsigned char bls, int pos = 0);

	const char* read_chars(size_t l);
	ccs read_ccs(size_t l);
	archive& write_ccs(ccs s, size_t l);
	archive& write_ccs(ccs s);
	archive& write(const char* data, size_t s);
	archive& read(char* data, size_t s);

	archive& write(const void* data, size_t s);
	archive& read(void* data, size_t s);

	// common writer for vector/set/map
	template <typename T>
	archive& write_container(const T& v) {
		*this << (size_t) v.size();
		for (auto m : v) *this << m;
		return *this;
	}

	// arrays
	template <typename T, size_t N>
	archive& operator<<(const std::array<T, N>& a);
	template <typename T, size_t N>
	archive& operator>>(std::array<T, N>& a);
	template <typename T, size_t N>
	static size_t size(const std::array<T, N>& a);

	// vectors
	template <typename T>
	archive& operator<<(const std::vector<T>& v);
	template <typename T>
	archive& operator>>(std::vector<T>& v);
	template <typename T>
	static size_t vecsize(const std::vector<T>& v);
	template <typename T>
	static size_t size(const std::vector<T>& v) { return vecsize(v); }
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
	inline static size_t header_size();

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

	archive& operator<<(const string_t&);
	archive& operator>>(string_t&);
	static size_t size(const string_t& s) {
		return sizeof(size_t) + s.size() + 1; }
	static size_t size(const std::string& s) {
		return sizeof(size_t) + s.size() + 1; }

	archive& operator<<(const spbdd_handle&);
	archive& operator>>(spbdd_handle&);
	static size_t size(const spbdd_handle&) { return sizeof(int_t); }
	static size_t size(const bdd_handle&) { return sizeof(int_t); }

	archive& add_lexeme_and_map(const dict_t& d,const lexeme& l,bool add=1);
	template <typename T>
	archive& add_lexemes(const dict_t& d, const T& lxms);
	archive& add_dict_lexemes(const dict_t&);
	archive& write_lexemes();

	static size_t dict_and_lexemes_size(const driver& drv);

	archive& operator<<(const term&);
	archive& operator>>(term&);
	static size_t size(const term&);

	archive& operator<<(const rule&);
	archive& operator>>(rule&);
	static size_t size(const rule&);

	archive& operator<<(const sig&);
	archive& operator>>(sig&);
	static size_t size(const sig&);

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

	archive& operator<<(const input&);
	archive& operator>>(input&);
	static size_t size(const input&);

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

};

#endif
