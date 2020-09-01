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
        return filesystem::read_symlink(
                        filesystem::path("/proc/self/fd") /
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
