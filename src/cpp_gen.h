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
#include "input.h"

namespace idni {

class cpp_gen {
	uint_t id{0};
	std::map<elem, std::string> elem_cache;
public:
	std::string dict_name{"dict"};
	ostream_t& gen(ostream_t& os, std::string& name, const elem& e);
	ostream_t& gen(ostream_t& os, std::string& name, const raw_term& rt);
	ostream_t& gen(ostream_t& os, std::string& name, const raw_form_tree&t);
	ostream_t& gen(ostream_t& os, std::string& name, const raw_rule& rr);
	ostream_t& gen(ostream_t& os, std::string& name, const directive& dir);
	ostream_t& gen(ostream_t& os, std::string& name, const production& q);
	ostream_t& gen(ostream_t& os, std::string& name, const raw_prog& rp);
	ostream_t& gen(ostream_t& os, std::string& name, const raw_progs& rps);
	ostream_t& gen(ostream_t& os, const lexeme& lex);
};

} // idni namespace
