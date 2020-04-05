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
#include "driver.h"
#include <iostream>
#include <sstream>
using namespace std;

wostream wcnull(0);
map<std::wstring, output> output::outputs = {};
wstring output::named = L"";

wostream& operator<<(wostream& os, const pair<cws, size_t>& p) {
	for (size_t n = 0; n != p.second; ++n) os << p.first[n];
	return os;
}

wostream& operator<<(wostream& os, const lexeme& l) {
	for (cws s = l[0]; s != l[1]; ++s) os << *s;
	return os;
}

#ifdef DEBUG
/*wostream& bdd_out_ite(wostream& os, spbdd x, size_t dep) {
	for (size_t n = 0; n != dep; ++n) os << '\t';
	if (x->leaf()) return os << (x->trueleaf() ? 'T' : 'F') << endl;
	bdd_out_ite(os << "if " << x->v() << endl, x->h(), dep+1);
	for (size_t n = 0; n != dep; ++n) os << '\t';
	return bdd_out_ite(os << "else" << endl, x->l(), dep+1);
}

wostream& operator<<(wostream& os, spbdd x) {
	if (x->leaf()) return os << (x->trueleaf() ? 'T' : 'F');
	return os << x->v() << " ? " << x->h() << " : " << x->l();
}*/

wostream& operator<<(wostream& os, const bools& x) {
	for (auto y:x) os << (y?1:0);
	return os;
}

wostream& operator<<(wostream& os, const vbools& x) {
	for (auto y:x) os << y << endl;
	return os;
}

wostream& operator<<(wostream& os, const term& t) {
	os << t.tab << L' ';
	if (t.neg) os << L'~';
	for (size_t n = 0; n != t.size(); ++n) {
		os << t[n];
		if (n != t.size()-1) os << L' ';
	}
	return os;
}

/*wostream& operator<<(wostream& os, const matrix& m) {
	for (const term& t : m) os << t << ',';
	return os;
}

wostream& operator<<(wostream& os, const matrices& m) {
	for (const matrix& x : m) os << x << endl;
	return os;
}*/
#endif

/*wostream& driver::print_term(wostream& os, const term& t) const {
	if (xsb) return print_term_xsb(os, t);
	if (t.neg()) os << L'~';
	os << dict.get_rel(t.rel()) << L'(';
	for (size_t ar = 0, n = 0; ar != t.arity().size();) {
		while (t.arity()[ar] == -1) ++ar, os << L'(';
		for (int_t k = 0; k != t.arity()[ar]; ++k) {
			if (t.arg(n) < 0) throw 0;//os<<dict.get_var(t.args[n]);
			else if (t.arg(n) & 1) {
				wchar_t c = t.arg(n)>>2;
				if (c == L'\r') os << "'\\r'";
				else if (c == L'\n') os << "'\\n'";
				else if (c == L'\t') os << "'\\t'";
				else os << L'\'' << c << L'\'';
			} else if (t.arg(n) & 2) os << (int_t)(t.arg(n)>>2);
			else if ((size_t)(t.arg(n)>>2) < dict.nsyms())
				os << dict.get_sym(t.arg(n));
			else os << L'[' << (t.arg(n)>>2) << L']';
			if (++n != t.nargs()) os << L' ';
		}
		++ar;
		while (ar<t.arity().size()&&t.arity()[ar] == -2) ++ar, os<<L')';
	}
	return os << L").";
}

wostream& driver::printmat(wostream& os, const matrix& t) const {
	set<wstring> s;
	for (auto v : t) {
		wstringstream ss;
		print_term(ss, v);
		s.emplace(ss.str());
	}
	for (auto& x : s) os << x << endl;
	return os;
}

#ifdef DEBUG
driver* drv;
wostream& printdb(wostream& os, lp *p) { return drv->printdb(os, p); }

wostream& printbdd(wostream& os, spbdd t, size_t bits, const prefix& p) {
	//bdd_out(os<<allsat(t, arlen(ar)*drv->bits), t)<<endl;
	return drv->printbdd(os, t, bits, p);
}

wostream& printbdd_one(wostream& os, spbdd t, size_t bits, const prefix& p) {
	return drv->printbdd_one(os, t, bits, p);
}

wostream& driver::printbdd(wostream& os, spbdd t, size_t bits, const prefix&p)
	const {
	from_bits(t,bits,p,[&os,this](const term&t){
			print_term(os, t)<<endl;});
	return os;
}

wostream& driver::printbdd_one(wostream& os, spbdd t, size_t bits,
	const prefix& p) const {
//	os << "one of " << bdd_count(t, bits * arlen(ar)) << " results: ";
	return print_term(os, one_from_bits(t, bits, p));
}
#endif

wostream& driver::printdb(wostream& os, lp *p) const {
	return printdb(os, p->db, p->rng.bits);
}

wostream& driver::printdb(wostream& os, const db_t& db, size_t bits) const {
	for (auto x : db)
		if (builtin_rels.find(x.first.rel) == builtin_rels.end()) {
			from_bits(x.second,bits,x.first,
				[&os,this](const term&t){
				print_term(os, t)<<endl; });
		}
	return os;
}*/

wostream& operator<<(wostream& os, const directive& d) {
	os << L'@';
	if (d.type == directive::BWD) return os << L"bwd.";
	if (d.type == directive::TRACE) return os << L"trace." << endl;
	if (d.type == directive::STDOUT) os << L"stdout ";
	else os << L"string ";
	if (d.type == directive::TREE) return os << d.t << L'.';
	return os << d.rel << L' ' << d.arg << L'.';
}

wostream& operator<<(wostream& os, const elem& e) {
	switch (e.type) {
		case elem::CHR: return os << '\'' <<
			(e.ch=='\'' || e.ch=='\\' ? L"\\" : L"") << e.ch<<'\'';
		case elem::OPENP:
		case elem::CLOSEP: return os<<*e.e[0];
		case elem::NUM: return os << e.num;
		default: return os << e.e;
	}
}

wostream& operator<<(wostream& os, const production& p) {
	os << p.p[0] << L" => ";
	for (size_t n = 1; n < p.p.size(); ++n) os << p.p[n] << L' ';
	return os << L'.';
}

wstring quote_sym(const elem& e) {
	std::wstringstream os, ss;
	if (e.type == elem::SYM) {
		bool q{false};
		for (cws s = e.e[0]; s != e.e[1]; ++s) {
			if (!q && !iswalnum(*s) && *s != L'_') {
				q = true;
				os << L'"';
			}
			if (q && (*s==L'"'|| *s==L'\\')) ss << L"\\";
			ss << *s;
		}
		os << ss.str();
		if (q) os << L'"';
		else if (e.e[0] == e.e[1]) os << L"\"\"";
	} else
		os << e; // CHR, OPENP, CLOSEP or NUM = no quotes
	if (e.bitype.bitness != size_t(-1)) {
		os << e.bitype;
		//switch (e.bitype.type) {
		//	case base_type::CHR: os << L":chr"; break;
		//	case base_type::STR: os << L":str"; break;
		//	case base_type::INT: os << L":int"; break;
		//	case base_type::NONE: os << L":none"; break;
		//}
		//os << L"[" << e.bitype.bitness << L"]";
	}
	return os.str();
}

wostream& operator<<(wostream& os, const raw_term& t) {
	if (t.neg) os << L'~';
	os << t.e[0];
	os << L'(';
	for (size_t ar = 0, n = 1; ar != t.arity.size();) {
		while (t.arity[ar] == -1) ++ar, os << L'(';
		if (n >= t.e.size()) break;
		while (t.e[n].type == elem::OPENP) ++n;
		for (int_t k = 0; k != t.arity[ar];)
			if ((os << quote_sym(t.e[n++])), ++k != t.arity[ar])
				os << L' ';
		while (n < t.e.size() && t.e[n].type == elem::CLOSEP) ++n;
		++ar;
		while (ar < t.arity.size() && t.arity[ar] == -2) ++ar, os<<L')';
	}
	return os << L')';
}

wostream& operator<<(wostream& os, const std::pair<raw_term, wstring>& p) {
	const raw_term& t = p.first;
	//if (t.neg) os << L'~';
	//os << t.e[0];
	//os << L'(';
	for (size_t ar = 0, n = 1; ar != t.arity.size();) {
		while (t.arity[ar] == -1) ++ar, os << L'(';
		if (n >= t.e.size()) break;
		while (t.e[n].type == elem::OPENP) ++n;
		for (int_t k = 0; k != t.arity[ar];)
			if ((os << quote_sym(t.e[n++])), ++k != t.arity[ar])
				os << L' ';
		while (n < t.e.size() && t.e[n].type == elem::CLOSEP) ++n;
		++ar;
		while (ar < t.arity.size() && t.arity[ar] == -2) ++ar, os << L')';
	}
	return os; // << L')';
}

wostream& operator<<(wostream& os, const raw_rule& r) {
	switch (r.type) {
		case raw_rule::GOAL: os << L'!'; break;
		case raw_rule::TREE: os << L"!!"; break;
		default: ;
	}
	for (size_t n = 0; n < r.h.size(); ++n)
		if ((os << r.h[n]), n != r.h.size() - 1) os << L',';
	if (!r.b.size()) return os << L'.';
	os << L" :- " << endl;
	for (size_t n = 0; n < r.b.size(); ++n) {
		for (size_t k = 0; k < r.b[n].size(); ++k)
			if ((os << '\t' << r.b[n][k]), k != r.b[n].size() - 1)
				os << L',' << endl;
		if (n != r.b.size() - 1) os << L';' << endl;
	}
	return os << L'.';
}

wostream& operator<<(wostream& os, const raw_prog& p) {
	for (auto x : p.d) os << x << endl;
	for (auto x : p.g) os << x << endl;
	for (auto x : p.r) os << x << endl;
	return os;
}

wostream& operator<<(wostream& os, const raw_progs& p) {
	if (p.p.size() == 1) os << p.p[0];
	else for (auto x : p.p) os << L'{' << endl << x << L'}' << endl;
	return os;
}

wostream& operator<<(wostream& os, const output& o) {
	return os << o.target();
}

wostream& operator<<(wostream& os, const option& o) {
	if (o.is_undefined()) return os;
	os << L"--" << o.name() << L' ';
	switch (o.get_type()) {
		case option::type::INT: {
			int i = o.get_int();
			return os << (i < 0 ? L"--":L"") << i;
		}
		case option::type::BOOL:
			return os << (o.get_bool() ?L"":L"false");
		case option::type::STRING: {
			wstring s = o.get_string();
			if (s != L"-" && s.rfind(L"-", 0) == 0) os << L"--";
			os << L'"';
			for (auto it = s.begin(); it < s.end(); ++it)
				os << (*it == '\\' || *it == '"' ? L"\\" : L""),
				os << *it;
			return os << L'"';
		} break;
		default: ;
	}
	return os;
}

wostream& operator<<(wostream& os, const std::map<std::wstring,option>& opts) {
	bool t = false;
	for (auto it : opts) {
		if (!it.second.is_undefined())
			os << (t ? L" " : L"") << it.second, t = true;
	}
	return os;
}

wostream& operator<<(wostream& os, const options& o) { return os << o.opts; }

void tables::print(wostream& os, const tables::proof_elem& e) {
	if (e.rl != (size_t)-1) os << L'[' << e.rl << L',' << e.al << L"] ";
	for (const auto& b : e.b)
		os << b.first << L' ' << to_raw_term(b.second) << L' ';
	os << endl;
}

void tables::print(wostream& os, const tables::proof& p) {
	for (size_t n = 0; n != p.size(); ++n)
		for (const auto& x : p[n]) {
			for (const auto& y : x.second)
				(os<<n<<L' '<<to_raw_term(x.first)<<L" :- "),
				print(os, y);
		}
}

#ifdef DEBUG
void tables::print(wostream& os, const tables::witness& w) {
	os << L'[' << w.rl << L',' << w.al << L"] ";
	for (const term& t : w.b) os << to_raw_term(t) << L", ";
	os << L'.';
}
#endif

/*void tables::print_env(const env& e) const {
	for (auto x : e) {
		int_t arg = r[n - 1];
		if (arg & 1) rt.e[n]=elem((wchar_t)(arg>>2));
		else if (arg & 2) rt.e[n]=elem((int_t)(arg>>2));
		else rt.e[n]=elem(elem::SYM, dict.get_sym(arg));
		o::out() << x.first << " = " << x.second << endl;
	}
	return os;
}*/

// rule printer for --print_updates
wostream& tables::print(wostream& os, const rule& r) const {
	os << to_raw_term(r.t) << L" :- ";
	for (auto it = r.begin(); it != r.end(); ++it)
		for (size_t n = 0; n != (*it)->t.size(); ++n)
			os << to_raw_term((*it)->t[n]) << (n==(*it)->t.size()-1
				? it == r.end()-1 ? L"." : L"; "
				: L", ");
	return os;
}

wostream& operator<<(wostream& os, const dict_t& d) {
	os <<   L"# nrels:   " << d.nrels() << L'\t';
	for (size_t i = 0; i != d.nrels(); ++i)
		os << i << L":" << d.get_rel(i)
			<< (i != d.nrels() - 1 ? L", " : L"");
	os << L"\n# nsyms:   " << d.nsyms() << L'\t' << std::flush;
	for (size_t i = 0; i != d.nsyms(); ++i)
		os << i << L":" << d.get_sym(i<<2)
			<< (i != d.nsyms() - 1 ? L", " : L"");
	os << L"\n# nvars:   " << d.nvars() << L'\t';
	os << L"\n# nbltins: " << d.nbltins() << L'\t';
	for (size_t i = 0; i != d.nbltins(); ++i)
		os << i << L":" << d.get_bltin(i)
			<< (i != d.nbltins() - 1 ? L", " : L"");
	return os << endl;
}
