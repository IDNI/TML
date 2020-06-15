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

wstring s2ws(const std::string& s) {
	return wstring_convert<codecvt_utf8<wchar_t>>().from_bytes(s);
}

string ws2s(const wstring& s) {
	return wstring_convert<codecvt_utf8<wchar_t>>().to_bytes(s);
}

#ifdef _WIN32

// to_string and to_wstring is not available under mingw gcc compiler
std::string to_string_(int_t v) {
        std::stringstream ss; ss << v; return ss.str();
}

std::wstring to_wstring_(int_t v) {
        std::wstringstream ss; ss << v; return ss.str();
}

std::string temp_filename() {
	TCHAR name[MAX_PATH], path[MAX_PATH];
	DWORD r = GetTempPath(MAX_PATH, path);
	if (r > MAX_PATH || !r ||
		!GetTempFileName(path, TEXT("TMLXXXX"), 0, name)) return "";
	return std::string(name);
}

#else

std::string to_string_(int_t v) { return to_string(v); }

std::wstring to_wstring_(int_t v) { return to_wstring(v); }

int temp_fileno() { return fileno(std::tmpfile()); }

std::string filename(int fd) {
        return std::filesystem::read_symlink(
                        std::filesystem::path("/proc/self/fd") /
                                std::to_string(fd));
}

#endif
