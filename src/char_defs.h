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
#include <array>
#include <vector>
#include <sstream>
#include <cstring>

extern std::wostream wcnull;
extern std::ostream cnull;

#define WITH_WCHAR
#ifdef WITH_WCHAR
typedef wchar_t syschar_t;
#define CIN   std::wcin
#define COUT  std::wcout
#define CERR  std::wcerr
#define CNULL wcnull
#define EMPTY_STRING L""
#else // WITH_WCHAR
typedef char syschar_t;
#define CIN   std::cin
#define COUT  std::cout
#define CERR  std::cerr
#define CNULL cnull
#define EMPTY_STRING ""
#endif // WITH_WCHAR

typedef std::basic_string<syschar_t>        sysstring_t;
typedef std::basic_istream<syschar_t>       istream_t;
typedef std::basic_ostream<syschar_t>       ostream_t;
typedef std::basic_ofstream<syschar_t>      ofstream_t;
typedef std::basic_ostringstream<syschar_t> ostringstream_t;
typedef std::basic_istringstream<syschar_t> istringstream_t;
typedef std::vector<std::string>            strings;
typedef std::vector<std::wstring>           wstrings;

typedef char char_t;                        // internal char representation
typedef std::basic_string<char_t> string_t; // internal string representation
typedef char32_t codepoint;                 // single unicode codepoint / symbol
typedef char_t* cstr;
typedef const char_t* ccs;
typedef ccs* pccs;
typedef std::array<ccs, 2> ccs_range;
typedef ccs_range lexeme;
typedef std::vector<lexeme> lexemes;
typedef std::array<size_t, 2> lexeme_range;

struct lexcmp { bool operator()(const lexeme& x, const lexeme& y) const; };
typedef std::map<lexeme, std::string, lexcmp> strs_t;

std::wstring s2ws(const std::string&);
std::wstring s2ws(const std::wstring&);
std::string  ws2s(const std::string&);
std::string  ws2s(const std::wstring&);

std::wostream& operator<<(std::wostream& os, const std::string& s);
std::ostream&  operator<<(std::ostream&  os, const char c);

std::string to_string_(int_t v);
