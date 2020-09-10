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
#include <locale>
#include <codecvt>
#include <filesystem>
#ifdef _WIN32
#include <windows.h>
#endif
#include "defs.h"

using namespace std;

wstring s2ws(const string& s) {
	return wstring_convert<codecvt_utf8<wchar_t>>().from_bytes(s);
}
string ws2s(const wstring& s) {
	return wstring_convert<codecvt_utf8<wchar_t>>().to_bytes(s);
}
wstring s2ws(const wstring& s) { return s; }
string  ws2s(const string&  s) { return s; }

wostream& operator<<(wostream& os, const string& s){ return os << s2ws(s);}
ostream& operator<<(ostream& os, const char c) { return os.put(c); }

string to_string_(int_t v) { stringstream ss; ss << v; return ss.str(); }
string_t to_string_t(int_t v) {
	return to_string_t(to_string_(v));
}
string_t to_string_t(const std::string& s) {
	return string_t(s.begin(), s.end());
}
string_t to_string_t(const char* s) {
	return to_string_t(string(s));
}
string to_string(const string_t& s) {
	return string(s.begin(), s.end());
}

string_t to_lower_first(string_t s) {
	if (s[0] >= (unsigned char)'A' && s[0] <= (unsigned char)'Z')
		s[0] = s[0] - ((unsigned char)'A' - (unsigned char)'a');
	return s;
}

string_t to_upper_first(string_t s) {
	if (s[0] >= (unsigned char)'a' && s[0] <= (unsigned char)'z')
		s[0] = s[0] + ((unsigned char)'A' - (unsigned char)'a');
	return s;
}

string_t to_string_t(const char* s);
#ifdef _WIN32
string temp_filename() {
	TCHAR name[MAX_PATH], path[MAX_PATH];
	DWORD r = GetTempPath(MAX_PATH, path);
	if (r > MAX_PATH || !r ||
		!GetTempFileName(path, TEXT("TMLXXXX"), 0, name)) return "";
	return string(name);
}
#else
int temp_fileno() { return fileno(tmpfile()); }
string filename(int fd) {
        return std::filesystem::read_symlink(
                        std::filesystem::path("/proc/self/fd") /
                                to_string(fd));
}
#endif

unsigned char *strdup(const unsigned char *src) {
	return reinterpret_cast<unsigned char*>(
		strdup(reinterpret_cast<const char *>(src)));
}
size_t strlen(const unsigned char *src) {
	return strlen(reinterpret_cast<const char *>(src));
}
unsigned char* strcpy(unsigned char* dst, const unsigned char* src) {
	return reinterpret_cast<unsigned char *>(
		strcpy(reinterpret_cast<char *>(dst),
			reinterpret_cast<const char *>(src)));
}
int strncmp(const unsigned char* str1, const unsigned char* str2, size_t num) {
	return strncmp(reinterpret_cast<const char *>(str1),
		reinterpret_cast<const char *>(str2), num);
}
int strncmp(const unsigned char* str1, const char* str2, size_t num) {
	return strncmp(reinterpret_cast<const char*>(str1), str2, num);
}
int strcmp(const unsigned char* str1, const char* str2) {
	return strcmp(reinterpret_cast<const char *>(str1), str2);
}

/**
 * checks if character is a begining of a multibyte codepoint
 */
bool is_mb_codepoint(const char_t ch) {
	return ch >= 0x80;
}

/**
 * convert ccs sequence s of 1-4 utf8 code units into codepoint &ch
 * @param str string of unsigned chars containing utf8 text
 * @param l size of the str string
 * @param ch reference to a codepoint read from string 
 * @return size (0, 1 - 4 bytes) or (size_t) -1 if illegal UTF8 code unit
 */
#define utf_cont(ch) (((ch) & 0xc0) == 0x80)
size_t peek_codepoint(ccs str, size_t l, char32_t &ch) {
	ch = -1;
  	if (!l) return 0;
	ccs end = str + l;
	unsigned char s[4] = { str[0] };
	ch = s[0];
	if  (ch < 0x80) return 1;
	if ((ch - 0xc2) > (0xf4 - 0xc2)) return -1;
	s[1] = *(str + 1);
	if  (ch < 0xe0) {
		if ((size_t)(str + 1) >= (size_t)end || !utf_cont(s[1]))
			return -1;
		ch = ((ch & 0x1f) << 6) | (s[1] & 0x3f);
		return 2;
	}
	s[2] = *(str + 2);
	if (ch < 0xf0) {
		if ((str + 2 >= end) || !utf_cont(s[1]) || !utf_cont(s[2]))
			return -1;
		if (ch == 0xed && s[1] > 0x9f) return -1;
		ch = ((ch & 0xf) << 12) | ((s[1] & 0x3f) << 6) | (s[2] &0x3f);
		if (ch < 0x800) return -1;
		return 3;
	}
	s[3] = *(str + 3);
	if ((str + 3 >= end) ||
		!utf_cont(s[1]) || !utf_cont(s[2]) || !utf_cont(s[3]))
			return -1;
	if      (ch == 0xf0) { if (s[1] < 0x90) return -1; }
	else if (ch == 0xf4) { if (s[1] > 0x8f) return -1; }
	ch = ((ch&7)<<18) | ((s[1]&0x3f)<<12) | ((s[2]&0x3f)<<6) | (s[3]&0x3f);
	return 4;
}

/**
 * Returns size of a unicode codepoint in bytes
 * @return size (0-4)
 */
size_t codepoint_size(char32_t ch) {
	if      (ch < 0x80)     return 1;
	else if (ch < 0x800)    return 2;
	else if (ch < 0x10000)  return 3;
	else if (ch < 0x110000) return 4;
	else return 0;
}

/**
 * Converts char32_t to a unsigned char *
 * @param ch unicode codepoint
 * @param s pointer to a char_t (of size 4+ bytes) where the result is stored
 * @return byte size of the codepoint
 */
size_t emit_codepoint(char32_t ch, char_t *s) {
	if (ch < 0x80) {
		s[0] = (char_t) ch;
		return 1;
	} else if (ch < 0x800) {
		s[0] = (char_t) (0xC0 + (ch >> 6));
		s[1] = (char_t) (0x80 + (ch & 0x3F));
		return 2;
	} else if (ch < 0x10000) {
		s[0] = (char_t) (0xE0 + (ch >> 12));
		s[1] = (char_t) (0x80 + ((ch >> 6) & 0x3F));
		s[2] = (char_t) (0x80 + (ch & 0x3F));
		return 3;
	} else if (ch < 0x110000) {
		s[0] = (char_t) (0xF0 + (ch >> 18));
		s[1] = (char_t) (0x80 + ((ch >> 12) & 0x3F));
		s[2] = (char_t) (0x80 + ((ch >> 6) & 0x3F));
		s[3] = (char_t) (0x80 + (ch & 0x3F));
		return 4;
	} else return 0;
}

string_t to_string_t(char32_t ch) {
	char_t s[4];
	size_t l = emit_codepoint(ch, s);
	if (l == (size_t) -1) return string_t();
	return string_t(s, l);
}

string_t to_string_t(const u32string& str) {
	basic_ostringstream<char_t> ss;
	auto it = str.begin();
	while (it != str.end()) {
		char_t s[5] = "\0\0\0\0";
		emit_codepoint(*(it++), s);
		ss << s;
		it++;
	}
	return ss.str();
}

u32string to_u32string(const string_t& str) {
	basic_ostringstream<char32_t> ss;
	char32_t ch;
	ccs s = str.c_str();
	size_t chl, sl = str.size();
	while ((chl = peek_codepoint(s, sl, ch)) > 0) {
		sl -= chl;
		s += chl;
		ss << ch;
	}
	// if (chl == (size_t) -1) return U""; // throw invalid UTF-8?
	return ss.str();
}

bool is_alnum(ccs s, size_t n, size_t& l) {
	char32_t ch;
	l = peek_codepoint(s, n, ch);
	if (l == 1) return isalnum(s[0]);
	return l >= 2 && l <= n; // all unicode symbols above ascii are alnum
}

bool is_alpha(ccs s, size_t n, size_t& l) {
	char32_t ch;
	l = peek_codepoint(s, n, ch);
	if (l == 1) return isalpha(s[0]);
	return l >= 2 && l <= n; // all unicode symbols above ascii are alnum
}

bool is_printable(char32_t ch) {
	return (uint32_t) ch > 31;
}
