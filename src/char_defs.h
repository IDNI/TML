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

typedef unsigned char char_t;               // internal char representation
typedef std::basic_string<char_t> string_t; // internal string representation
typedef char_t* cstr;
typedef const char_t* ccs;
typedef ccs* pccs;
typedef std::array<ccs, 2> ccs_range;
typedef ccs_range lexeme;
const lexeme null_lexeme {0,0};
typedef std::vector<lexeme> lexemes;
typedef std::array<size_t, 2> lexeme_range;

struct lexcmp { bool operator()(const lexeme& x, const lexeme& y) const; };
bool operator==(const lexeme& l, std::string s);
bool operator==(const lexeme& l, const char* s);
template<> struct std::hash<lexeme> {size_t operator()(const lexeme&)const;};
bool operator<(const lexeme&, const lexeme&);
template<> struct std::less<lexeme> {bool operator()(const lexeme&, const lexeme&)const;};
bool operator==(const lexeme& x, const lexeme& y);
#define lexeme2str(l) string_t((l)[0], (l)[1]-(l)[0])
#define str2lexeme(s) { (unsigned char *) (s), (unsigned char *) (s) + sizeof(s) - 1 }

typedef std::map<lexeme, string_t, lexcmp> strs_t;

std::wstring s2ws(const std::string&);
std::wstring s2ws(const std::wstring&);
std::string  ws2s(const std::string&);
std::string  ws2s(const std::wstring&);

#ifndef NOOUTPUTS
std::wostream& operator<<(std::wostream& os, const std::string& s);
std::ostream&  operator<<(std::ostream&  os, const char c);
#endif

string_t unquote(string_t str);
std::string to_string_(int_t v);
string_t to_string_t(int_t v);
string_t to_string_t(const std::string& s);
string_t to_string_t(const char* s);
std::string to_string(const string_t& s);

string_t to_lower_first(string_t s);
string_t to_upper_first(string_t s);

unsigned char* strdup(const unsigned char* src);
size_t strlen(const unsigned char *src);
unsigned char* strcpy(unsigned char* dst, const unsigned char* src);
int strncmp(const unsigned char* str1, const unsigned char* str2, size_t num);

// only for comparing with const char* literals containing ASCII
int strncmp(const unsigned char* str1, const char* str2, size_t num);
int strcmp(const unsigned char* str1, const char* str2);

bool is_mb_codepoint(const char_t str);
size_t peek_codepoint(ccs s, size_t l, char32_t &ch);
size_t codepoint_size(char32_t ch);
size_t emit_codepoint(char32_t ch, char_t *s);
std::basic_ostream<char_t>& emit_codepoint(std::basic_ostream<char_t>& os,
	char32_t ch);
string_t to_string_t(char ch);
string_t to_string_t(char32_t ch);
string_t to_string_t(const std::u32string& str);
std::u32string to_u32string(const string_t& str);

bool is_alnum(ccs s, size_t n, size_t& l);
bool is_alpha(ccs s, size_t n, size_t& l);
bool is_printable(char32_t ch);

int_t hex_to_int_t(ccs str, size_t len = 2);
