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
#include <iostream>
#include <sstream>
#include <locale>
#include "printing.h"

using namespace std;

namespace idni {
	
basic_ostream<char>& operator<<(basic_ostream<char>& os, const lexeme& l) {
	return os << to_string(lexeme2str(l));
}
basic_ostream<wchar_t>& operator<<(basic_ostream<wchar_t>& os, const lexeme& l){
	return os << s2ws(to_string(lexeme2str(l)));
}

bool isprint(const char32_t& ch) {
	return ch < 256 ? ::isprint(ch) : true;// TODO is_printable for ch > 255
}

std::string quote_sym(const elem& e) {
	ostringstream_t os;
	basic_ostringstream<char_t> ss;
	if (e.type == elem::SYM) {
		bool q{false};
		for (ccs s = e.e[0]; s < e.e[1]; ) {
			if (is_mb_codepoint(*s)) {
				char32_t ch;
				size_t chl = peek_codepoint(s, e.e[1] - s, ch);
				if (!chl || chl > 4) {
					DBGFAIL;
					return "";
				}
				for (size_t i = 0; i != chl; ++i) ss.put(*s++);
			} else {
				if (!q && !::isalnum(*s) && *s != '_')
					os.put('"'), q = true;
				if (q && (*s=='"'|| *s=='\\')) ss.put('\\');
				ss.put(*s);
				++s;
			}
		}
		os << to_string(ss.str());
		if (q) os.put('"');
		else if (e.e[0] == e.e[1]) os << "\"\"";
	} else if (e.type == elem::CHR) switch (e.ch) {
		case U'\r': os <<  "'\\r'"; break;
		case U'\n': os <<  "'\\n'"; break;
		case U'\t': os <<  "'\\t'"; break;
		case U'\\': os << "'\\\\'"; break;
		case U'\'': os <<  "'\\''"; break;
		default: if (isprint(e.ch)) os << e;
			else os << "'\\" << (e.ch < 256?'x':'u') << hex
				<< setfill('0') << setw(e.ch<256?2:4)
				<< (unsigned int) e.ch << "'";
	} else os << e; // OPENP, CLOSEP or NUM = no quotes
	return ws2s(os.str());
}

std::string to_string(const raw_term& rt, std::string delim, int_t skip) {
	ostringstream ss;
	ss << tuple{ rt, delim, skip };
	return ss.str();
}

ostream_t& print_to_delimited(const raw_term& rt, bool& error, bool to,
	bool delimited)
{
	if (rt.e.size() < 3 || (delimited && rt.e.size() == 3))
		o::err() << "print: Too few arguments." << endl;
	else {
		size_t s = 0; // skip args
		string ou = "output", delimiter = "";
		ostringstream ss;
		if (to)	       s++, ss << pair<elem,bool>{rt.e[1+s],true},
				ou        = ss.str(), ss.str({});
		if (delimited) s++, ss << pair<elem,bool>{rt.e[1+s],true},
				delimiter = ss.str();
		//COUT << "printing " << to << delimited << endl;
		if (!outputs::exists(ou)) o::err() << "print_to: Output '" <<
			ou << "' does not exist." << endl;
		else return o::to(ou)
			<< tuple<raw_term,string,int_t>{ rt, delimiter, s };
	}
	error = true;
	return CNULL;
}

} // idni namespace
