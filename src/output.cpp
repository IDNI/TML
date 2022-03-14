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

#include "input.h"
#include "output.h"
#include "options.h"
#include "tables.h"

using namespace std;

wostream wcnull(0);
ostream cnull(0);

const map<output::type_t, string> output::type_names_ = {
	{ NONE,   "@null"   },
	{ STDOUT, "@stdout" },
	{ STDERR, "@stderr" },
	{ BUFFER, "@buffer" },
	{ NAME,   "@name"   }
};
outputs* outputs::o_ = 0;

namespace o {
	void init_defaults(outputs* oo) { oo->init_defaults(); }
	void use          (outputs* oo) { oo->use(); }
	ostream_t& to(const string& n) { return outputs::to(n); }
	ostream_t& out()  { return outputs::out();  }
	ostream_t& err()  { return outputs::err();  }
	ostream_t& inf()  { return outputs::inf();  }
	ostream_t& dbg()  { return outputs::dbg();  }
#ifdef WITH_THREADS
	ostream_t& repl() { return outputs::repl(); }
#endif
	ostream_t& ms()   { return outputs::ms();   }
	ostream_t& dump() { return outputs::dump(); }
	ostream_t& transformed() { return outputs::transformed(); }
}

output::type_t output::get_type(string t) {
	t = t == "" ? "@stdout" : t;
	for (auto& it : output::type_names_)
		if (it.second == t) return it.first;
	return FILE;
}

output::type_t output::target(const string t) {
	type_ = t == "" ? STDOUT : get_type(t);
	bool open_path_before_finish = false;
	switch (type_) {
		case NONE:                os(&CNULL);     break;
		case STDOUT:              os(&COUT); break;
		case STDERR:              os(&CERR); break;
		case BUFFER:
			buffer_.str(EMPTY_STRING); os(&buffer_); break;
		case NAME:
			{
				string name = outputs::named();
				if (!name.size())
					return o::err() << "output '"
					<< name_ << "' targeting @name without "
					"setting name" << endl,
					os(&CNULL), NONE;
				ostringstream ss; ss << name << ext_;
				path_ = ss.str();
			}
			open_path_before_finish = true;
			break;
		case FILE:
			path_ = t, open_path_before_finish = true;
			break;
		default: DBGFAIL;
	}
	if (open_path_before_finish)
		file_.open(path_, ofstream::binary | ofstream::app),
		file_.imbue(locale("")),
		os(&file_);
	return type_;
}

void outputs::update_pointers(const string& n, output* out) {
	if      (n == "output")      out_  = out;
	else if (n == "error")       err_  = out;
	else if (n == "info")        inf_  = out;
	else if (n == "debug")       dbg_  = out;
#ifdef WITH_THREADS
	else if (n == "repl-output") repl_ = out;
#endif
	else if (n == "benchmarks")  ms_   = out;
	else if (n == "dump")        dump_ = out;
	else if (n == "transformed") trns_ = out;
}

bool outputs::add(sp_output out) {
	string n = out->name();
	auto it = find(n);
	if (it != end()) {
		//CERR << "already exists: " << n << " target: "
		//	<< out->target() << endl;
		it->second->target(out->target());
		out = it->second;
	} else emplace(n, out);
	o_->update_pointers(n, out.get());
	return true;
}

ostream_t& outputs::to(const string& n) {
	output* o = get(n);
	if (o) return o->os();
	DBGFAIL;
	return CNULL;
}

void outputs::target(const string& n, const string& t) {
	output* o = get(n);
	if (o) o->target(t);
	else {
		CERR << "target does not exist: " << n << endl;
		DBGFAIL;
	}
}

template <typename T>
basic_ostream<T>& operator<<(basic_ostream<T>& os, const pair<ccs, size_t>& p) {
	for (size_t n = 0; n != p.second; ++n) os << p.first[n];
	return os;
}
template basic_ostream<char>& operator<<(basic_ostream<char>&, const pair<ccs, size_t>&);
template basic_ostream<wchar_t>& operator<<(basic_ostream<wchar_t>&, const pair<ccs, size_t>&);


basic_ostream<char>& operator<<(basic_ostream<char>& os, const lexeme& l) {
	return os << to_string(lexeme2str(l));
}
basic_ostream<wchar_t>& operator<<(basic_ostream<wchar_t>& os, const lexeme& l){
	return os << s2ws(to_string(lexeme2str(l)));
}
//template <typename T>
//basic_ostream<T>& operator<<(basic_ostream<T>& os, const lexeme& l) {
//	os << (l[0], l[1], l[1]-l[0]);
//	//for (ccs s = l[0]; s != l[1]; ++s) os << *s;
//	//DBG(os << " (" << (void*)l[0] << " " << (void*)l[1] << ")";)
//	return os;
//}
//template basic_ostream<char>& operator<<(basic_ostream<char>&, const lexeme&);
//template basic_ostream<wchar_t>& operator<<(basic_ostream<wchar_t>&, const lexeme&);

#ifdef DEBUG
/*template <typename T>
basic_ostream<T>& bdd_out_ite(basic_ostream<T>& os, spbdd x, size_t dep) {
	for (size_t n = 0; n != dep; ++n) os << '\t';
	if (x->leaf()) return os << (x->trueleaf() ? 'T' : 'F') << endl;
	bdd_out_ite(os << "if " << x->v() << endl, x->h(), dep+1);
	for (size_t n = 0; n != dep; ++n) os << '\t';
	return bdd_out_ite(os << "else" << endl, x->l(), dep+1);
}

template <typename T>
basic_ostream<T>& operator<<(basic_ostream<T>& os, spbdd x) {
	if (x->leaf()) return os << (x->trueleaf() ? 'T' : 'F');
	return os << x->v() << " ? " << x->h() << " : " << x->l();
}*/

template <typename T>
basic_ostream<T>& operator<<(basic_ostream<T>& os, const bools& x) {
	for (auto y:x) os << (y?1:0);
	return os;
}
template basic_ostream<char>& operator<<(basic_ostream<char>&, const bools&);
template basic_ostream<wchar_t>& operator<<(basic_ostream<wchar_t>&, const bools&);

template <typename T>
basic_ostream<T>& operator<<(basic_ostream<T>& os, const vbools& x) {
	for (auto y:x) os << y << endl;
	return os;
}
template basic_ostream<char>& operator<<(basic_ostream<char>&, const vbools&);
template basic_ostream<wchar_t>& operator<<(basic_ostream<wchar_t>&, const vbools&);

template <typename T>
basic_ostream<T>& operator<<(basic_ostream<T>& os, const term& t) {
	os << '[' << t.tab << "] ";
	if (t.neg) os << "~ ";
	for (size_t n = 0; n != t.size(); ++n) {
		os << t[n];
		if (n != t.size()-1) os << ' ';
	}
	return os;
}
template basic_ostream<char>& operator<<(basic_ostream<char>&, const term&);
template basic_ostream<wchar_t>& operator<<(basic_ostream<wchar_t>&, const term&);

/*template <typename T>
basic_ostream<T>& operator<<(basic_ostream<T>& os, const matrix& m) {
	for (const term& t : m) os << t << ',';
	return os;
}

template <typename T>
basic_ostream<T>& operator<<(basic_ostream<T>& os, const matrices& m) {
	for (const matrix& x : m) os << x << endl;
	return os;
}*/
#endif

/*template <typename T>
basic_ostream<T>& driver::print_term(basic_ostream<T>& os, const term& t) const {
	if (xsb) return print_term_xsb(os, t);
	if (t.neg()) os << '~';
	os << dict.get_rel(t.rel()) << '(';
	for (size_t ar = 0, n = 0; ar != t.arity().size();) {
		while (t.arity()[ar] == -1) ++ar, os << '(';
		for (int_t k = 0; k != t.arity()[ar]; ++k) {
			if (t.arg(n) < 0) DBGFAIL;//os<<dict.get_var(t.args[n]);
			else if (t.arg(n) & 1) {
				char_t c = t.arg(n)>>2;
				if (c == '\r') os << "'\\r'";
				else if (c == '\n') os << "'\\n'";
				else if (c == '\t') os << "'\\t'";
				else os << '\'' << c << '\'';
			} else if (t.arg(n) & 2) os << (int_t)(t.arg(n)>>2);
			else if ((size_t)(t.arg(n)>>2) < dict.nsyms())
				os << dict.get_sym(t.arg(n));
			else os << '[' << (t.arg(n)>>2) << ']';
			if (++n != t.nargs()) os << ' ';
		}
		++ar;
		while (ar<t.arity().size()&&t.arity()[ar] == -2) ++ar, os<<')';
	}
	return os << ").";
}

template <typename T>
basic_ostream<T>& driver::printmat(basic_ostream<T>& os, const matrix& t) const {
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

template <typename T>
basic_ostream<T>& printdb(basic_ostream<T>& os, lp *p) { return drv->printdb(os, p); }

template <typename T>
basic_ostream<T>& printbdd(basic_ostream<T>& os, spbdd t, size_t bits, const prefix& p) {
	//bdd_out(os<<allsat(t, arlen(ar)*drv->bits), t)<<endl;
	return drv->printbdd(os, t, bits, p);
}

template <typename T>
basic_ostream<T>& printbdd_one(basic_ostream<T>& os, spbdd t, size_t bits, const prefix& p) {
	return drv->printbdd_one(os, t, bits, p);
}

template <typename T>
basic_ostream<T>& driver::printbdd(basic_ostream<T>& os, spbdd t, size_t bits, const prefix&p)
	const {
	from_bits(t,bits,p,[&os,this](const term&t){
			print_term(os, t)<<endl;});
	return os;
}

template <typename T>
basic_ostream<T>& driver::printbdd_one(basic_ostream<T>& os, spbdd t, size_t bits,
	const prefix& p) const {
//	os << "one of " << bdd_count(t, bits * arlen(ar)) << " results: ";
	return print_term(os, one_from_bits(t, bits, p));
}
#endif

template <typename T>
basic_ostream<T>& driver::printdb(basic_ostream<T>& os, lp *p) const {
	return printdb(os, p->db, p->rng.bits);
}

template <typename T>
basic_ostream<T>& driver::printdb(basic_ostream<T>& os, const db_t& db, size_t bits) const {
	for (auto x : db)
		if (builtin_rels.find(x.first.rel) == builtin_rels.end()) {
			from_bits(x.second,bits,x.first,
				[&os,this](const term&t){
				print_term(os, t)<<endl; });
		}
	return os;
}*/

template <typename T>
basic_ostream<T>& operator<<(basic_ostream<T>& os, const directive& d) {
	os << '@';
	if (d.type == directive::BWD) return os << "bwd.";
	if (d.type == directive::TRACE) return os << "trace." << endl;
	if (d.type == directive::EDOMAIN)
		return os << "domain " << d.domain_sym << ' ' << d.limit_num << ' '
			<< d.arity_num << '.';
	if (d.type == directive::EVAL)
		return os << "eval " << d.eval_sym << ' ' << d.domain_sym << ' '
			<< d.quote_sym << ' ' << d.timeout_num << '.';
	if (d.type == directive::QUOTE)
		return os << "quote " << d.quote_sym << ' ' << d.domain_sym << ' '
			<< d.quote_str << '.';
	if (d.type == directive::CODEC)
		return os << "codec " << d.codec_sym << ' ' << d.domain_sym << ' '
			<< d.quote_sym << ' ' << d.arity_num << '.';
	if (d.type == directive::INTERNAL)
		return os << "internal " << d.internal_term << '.';
	if (d.type == directive::STDOUT) os << "stdout ";
	else os << "string ";
	if (d.type == directive::TREE) return os << d.t << '.';
	return os << d.rel << ' ' << d.arg << '.';
}
template
basic_ostream<char>& operator<<(basic_ostream<char>&, const directive&);
template
basic_ostream<wchar_t>& operator<<(basic_ostream<wchar_t>&, const directive&);

template <typename T>
basic_ostream<T>& operator<<(basic_ostream<T>& os, const elem& e) {
	switch (e.type) {
		case elem::CHR: return os << '\'' <<
			(e.ch == U'\'' || e.ch == U'\\' ? "\\":"") <<
			to_string(to_string_t(e.ch)) << '\'';
		case elem::OPENP:
		case elem::CLOSEP: return os << *e.e[0];
		case elem::NUM:    return os << e.num;
		case elem::BLTIN: if (e.num) {
				if (e.num & 2) os << "renew ";
				if (e.num & 1) os << "forget ";
			}
			return os << e.e;
		default: return os << e.e;
	}
}
template basic_ostream<char>& operator<<(basic_ostream<char>&, const elem&);
template
basic_ostream<wchar_t>& operator<<(basic_ostream<wchar_t>&, const elem&);

template <typename T>
basic_ostream<T>& operator<<(basic_ostream<T>& os, const production& p) {
	os << p.p[0] << " => ";
	for (size_t n = 1; n < p.p.size(); ++n) os << p.p[n] << ' ';
	return os << '.';
}
template
basic_ostream<char>& operator<<(basic_ostream<char>&, const production&);
template
basic_ostream<wchar_t>& operator<<(basic_ostream<wchar_t>&, const production&);

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
				if (!q && !isalnum(*s) && *s != '_')
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
		default: if (is_printable(e.ch)) os << e;
			else os << "'\\" << (e.ch < 256?'x':'u') << hex
				<< setfill('0') << setw(e.ch<256?2:4)
				<< (unsigned int) e.ch << "'";
	} else os << e; // OPENP, CLOSEP or NUM = no quotes
	return ws2s(os.str());
}

template <typename T>
basic_ostream<T>& operator<<(basic_ostream<T>& os, const raw_form_tree &t) {
	switch(t.type) {
		case elem::IMPLIES:
			os << "{" << *t.l << " -> " << *t.r << "}";
			break;
		case elem::COIMPLIES:
			os << "{" << *t.l << " <-> " << *t.r << "}";
			break;
		case elem::AND:
			os << "{" << *t.l << " && " << *t.r << "}";
			break;
		case elem::ALT:
			os << "{" << *t.l << " || " << *t.r << "}";
			break;
		case elem::NOT:
			os << "~{" << *t.l << "}";
			break;
		case elem::EXISTS:
			os << "exists " << *t.l << " { " << *t.r << " }";
			break;
		case elem::UNIQUE:
			os << "unique " << *t.l << " { " << *t.r << " }";
			break;
		case elem::NONE:
			os << *t.rt;
			break;
		case elem::FORALL:
			os << "forall " << *t.l << " { " << *t.r << " }";
			break;
		case elem::SYM: case elem::VAR:
			os << *t.el;
			break;
		default:
			assert(false); //should never reach here
	}
	return os;
}
template basic_ostream<char>& operator<<(basic_ostream<char>&, const raw_form_tree &);
template
basic_ostream<wchar_t>& operator<<(basic_ostream<wchar_t>&, const raw_form_tree &);

template <typename T>
basic_ostream<T>& operator<<(basic_ostream<T>& os, const raw_term& t) {
	if (t.neg) os << '~';
	
	if( t.extype == raw_term::ARITH) {
		if (t.neg) os << '{';
		for ( elem el : t.e) 
			os << el;
		if (t.neg) os << '}';
		return os;
	}
	if (t.extype == raw_term::EQ ||
		t.extype == raw_term::LEQ) {
		if (t.neg) os << '{';
		os << t.e[0];
		t.e[1].type == elem::EQ ? os << "=" : t.e[1].type == elem::LEQ ? os << "<=" :
						t.e[1].type == elem::LT ? os << "<" : t.e[1].type == elem::GEQ ?
						os << ">=": t.e[1].type == elem::GT ? os << ">": os <<"";
		os << t.e[2];
		if (t.neg) os << '}';
		return os;
	}
	if (t.extype == raw_term::VAR) {
		os << t.e[0];
		return os;
	}

	os << t.e[0];
	os << '(';
	for (size_t ar = 0, n = 1; ar != t.arity.size();) {
		while (t.arity[ar] == -1) ++ar, os << '(';
		if (n >= t.e.size()) break;
		while (t.e[n].type == elem::OPENP) ++n;
		for (int_t k = 0; k != t.arity[ar];)
			if ((os << quote_sym(t.e[n++])), ++k != t.arity[ar])
				os << ' ';
		while (n < t.e.size() && t.e[n].type == elem::CLOSEP) ++n;
		++ar;
		while (ar < t.arity.size() && t.arity[ar] == -2) ++ar, os<<')';
	}
	return os << ')';
}
template basic_ostream<char>& operator<<(basic_ostream<char>&, const raw_term&);
template
basic_ostream<wchar_t>& operator<<(basic_ostream<wchar_t>&, const raw_term&);

template <typename T>
basic_ostream<T>& operator<<(basic_ostream<T>& os, const pair<elem, bool>& p) {
	const elem& e  = p.first;
	return p.second && e.type == elem::CHR
		? os << to_string(to_string_t(e.ch))
		: os << e;
}
template basic_ostream<char>& operator<<(basic_ostream<char>& os,
	const pair<elem, bool>&);
template basic_ostream<wchar_t>& operator<<(basic_ostream<wchar_t>& os,
	const pair<elem, bool>&);

template <typename T>
basic_ostream<T>& operator<<(basic_ostream<T>& os,
	// raw_term, delimiter, skip n args
	const tuple<raw_term, string, int_t>& p)
{
	const raw_term& t   = get<0>(p);
	const string& delim = get<1>(p);
	const int_t& skip   = get<2>(p);
	for (size_t ar = 0, n = 1; ar != t.arity.size();) {
		while (t.arity[ar] == -1) ++ar, os << '(';
		if (n >= t.e.size()) break;
		while (t.e[n].type == elem::OPENP) ++n;
		n += skip;
		for (int_t k = skip; k != t.arity[ar];) {
			if (n > 1) os << pair{ t.e[n++], true };
			if (++k != t.arity[ar] && n > 1 && delim.length())
				os << delim;
		}
		while (n < t.e.size() && t.e[n].type == elem::CLOSEP) ++n;
		++ar;
		while (ar < t.arity.size() && t.arity[ar] == -2) ++ar, os << ')';
	}
	return os;
}
template <typename T>
basic_ostream<T>& operator<<(basic_ostream<T>& os, const raw_rule& r) {
	return print_raw_rule(os, r, 0);
}
template basic_ostream<char>& operator<<(basic_ostream<char>&, const raw_rule&);
template
basic_ostream<wchar_t>& operator<<(basic_ostream<wchar_t>&, const raw_rule&);

template <typename T>
basic_ostream<T>& operator<<(basic_ostream<T>& os, const std::set<raw_term>& rts) {
	os << '{';
	for(std::set<raw_term>::iterator it = rts.begin(); it != rts.end();
			it++) {
		if(it != rts.begin()) {
			os << ", ";
		}
		os << *it;
	}
	return os << '}';
}
template basic_ostream<char>& operator<<(basic_ostream<char>&, const std::set<raw_term>&);
template
basic_ostream<wchar_t>& operator<<(basic_ostream<wchar_t>&, const std::set<raw_term>&);

template <typename T>
basic_ostream<T>& operator<<(basic_ostream<T>& os, const std::vector<raw_term>& rts) {
	os << '[';
	for(size_t i = 0; i < rts.size(); i++) {
		if(i != 0) {
			os << ", ";
		}
		os << rts[i];
	}
	return os << ']';
}
template basic_ostream<char>& operator<<(basic_ostream<char>&, const std::vector<raw_term>&);
template
basic_ostream<wchar_t>& operator<<(basic_ostream<wchar_t>&, const std::vector<raw_term>&);

template <typename T>
basic_ostream<T>& print_raw_rule(basic_ostream<T>& os, const raw_rule& r,
	size_t level)
{
	bool compact = true;
	basic_string<T>indent(level, '\t');
	os << indent;
	switch (r.type) {
		case raw_rule::GOAL: os << '!'; break;
		case raw_rule::TREE: os << "!!"; break;
		default: ;
	}
	for (size_t n = 0; n < r.h.size(); ++n)
		if ((os << r.h[n]), n != r.h.size() - 1) os << ',';
	if (!r.b.size() && !r.prft) return os << '.';
	os << " :- ";
	bool uni = r.b.size() == 1 && r.b[0].size() == 1;
	bool noendl = !r.b.size() || uni;
	if (!compact && !noendl) os << endl;
	if (r.prft) os << *r.prft;
	for (size_t n = 0; n < r.b.size(); ++n) {
		for (size_t k = 0; k < r.b[n].size(); ++k)
			if (((compact||uni?os<<"":os<<indent<<'\t')<<r.b[n][k]),
				k != r.b[n].size() - 1)
					os << ',' << (compact ? " " : "\n");
		if (n != r.b.size() - 1) os << ';' << endl;
	}
	return os << '.';
}
template basic_ostream<char>& print_raw_rule(basic_ostream<char>&,
	const raw_rule&, size_t level);
template basic_ostream<wchar_t>& print_raw_rule(basic_ostream<wchar_t>&,
	const raw_rule&, size_t level);

// TODO this is just a draft printer for raw form tree - not completly correct
template <typename T>
basic_ostream<T>& operator<<(basic_ostream<T>& os, const sprawformtree prft) {
	lexeme guard_lx = prft->guard_lx;
	auto is_quantifier = [](const sprawformtree prft) -> bool {
		return prft->type == elem::EXISTS ||
			prft->type == elem::FORALL ||
			prft->type == elem::UNIQUE;
	};
	const sprawformtree node = prft;
	//if (guard_lx != lexeme{ 0, 0 }) // find first node after quantifiers
	//	while (node && is_quantifier(node)) node = node->r;
	function<basic_ostream<T>&(const sprawformtree)> print_node;
	print_node = [&os, &print_node, &guard_lx, &node, &is_quantifier]
		(const sprawformtree prft) -> basic_ostream<T>&
	{
		basic_ostringstream<T> op;
		bool wrap = prft->type != elem::VAR &&
			prft->type != elem::SYM &&
			prft->type != elem::NOT;
		bool prefop = prft->el && is_quantifier(prft);
		bool prefix = (prft->rt || prefop);
		bool is_guarded = prft == node && guard_lx != lexeme{ 0, 0 };
		if (is_guarded) os<<"{ "<<guard_lx<<" && ";
		if (prft->neg) os << "~ ";
		if (prft->type == elem::NOT) os << "~ ";
		else prft->rt ? op << *prft->rt
			: (prft->el ? op << *prft->el << " " : op << "");
		os << (wrap ? "{ " : "");
		if (prefix) os << op.str();
		if (prft->l) print_node(prft->l);
		if (!prefix) os << " " << op.str();
		if (prft->r) print_node(prft->r);
		os << (wrap ? " }": " ");
		if (is_guarded) os << " }";
		return os;
	};
	return print_node(prft);
}
template basic_ostream<char>& operator<<(basic_ostream<char>&,
	const sprawformtree prft);
template basic_ostream<wchar_t>& operator<<(basic_ostream<wchar_t>&,
	const sprawformtree prft);

template <typename T>
basic_ostream<T>& print_state_block(basic_ostream<T>& os, const state_block& sb,
	size_t level)
{
	basic_string<T> indent(level, '\t');
	return print_raw_prog_tree(os << indent << '[' << sb.label
		<< (sb.flip ? "~" : "") << ":\n",
		sb.p, level+1) << indent << "]";
}
template
basic_ostream<char>& print_state_block(basic_ostream<char>& os,
	const state_block& sb, size_t level);
template
basic_ostream<wchar_t>& print_state_block(basic_ostream<wchar_t>& s,
	const state_block& sb, size_t level);

template <typename T>
basic_ostream<T>& operator<<(basic_ostream<T>& os, const state_block& sb) {
	return print_state_block(os, sb, 0);
}
template
basic_ostream<char>& operator<<(basic_ostream<char>& os, const state_block& sb);
template
basic_ostream<wchar_t>& operator<<(basic_ostream<wchar_t>& s,
	const state_block& sb);

template <typename T>
basic_ostream<T>& operator<<(basic_ostream<T>& os, const raw_prog& p) {
	return print_raw_prog_tree<T>(os, p, 0);
}
template
basic_ostream<char>& operator<<(basic_ostream<char>& os, const raw_prog& p);
template
basic_ostream<wchar_t>& operator<<(basic_ostream<wchar_t>& s,const raw_prog& p);

template <typename T>
basic_ostream<T>& print_raw_prog_tree(basic_ostream<T>& os, const raw_prog& p,
	size_t level)
{
	basic_string<T> indent(level, '\t');
	if (p.type != raw_prog::PFP) os << indent << "# "<< (int_t)p.type<<"\n";
	for (auto x : p.d) os << indent << x << "\n";
	for (auto x : p.g) os << indent << x << "\n";
	for (auto x : p.r) print_raw_rule(os, x, level) << "\n";
	for (auto x : p.sbs) print_state_block(os, x, level) << "\n";
	for (auto x : p.nps) print_raw_prog_tree(os << indent << "{\n",
		x, level+1) << indent << "}\n";
	return os;
}
template basic_ostream<char>& print_raw_prog_tree(basic_ostream<char>& os,
	const raw_prog& p, size_t level);
template basic_ostream<wchar_t>& print_raw_prog_tree(basic_ostream<wchar_t>& s,
	const raw_prog& p, size_t level);

template <typename T>
basic_ostream<T>& operator<<(basic_ostream<T>& os, const raw_progs& p) {
	return os << p.p;
}
template
basic_ostream<char>& operator<<(basic_ostream<char>& os, const raw_progs& p);
template
basic_ostream<wchar_t>& operator<<(basic_ostream<wchar_t>& s,const raw_progs&p);

template <typename T>
basic_ostream<T>& operator<<(basic_ostream<T>& os, const output& o) {
	return os << o.target();
}
template basic_ostream<char>& operator<<(basic_ostream<char>&, const output&);
template
basic_ostream<wchar_t>& operator<<(basic_ostream<wchar_t>&, const output&);

template <typename T>
basic_ostream<T>& operator<<(basic_ostream<T>& os, const option& o) {
	if (o.is_undefined()) return os;
	os << "--" << o.name() << ' ';
	switch (o.get_type()) {
		case option::type::INT: {
			int i = o.get_int();
			return os << (i < 0 ? "--":"") << i;
		}
		case option::type::BOOL:
			return os << (o.get_bool() ?"":"false");
		case option::type::STRING: {
			string s = o.get_string();
			if (s != "-" && s.rfind("-", 0) == 0) os << "--";
			os << '"';
			for (auto it = s.begin(); it < s.end(); ++it)
				os << (*it == '\\' || *it == '"' ? "\\" : ""),
				os << *it;
			return os << '"';
		} break;
		default: ;
	}
	return os;
}
template basic_ostream<char>& operator<<(basic_ostream<char>&, const option&);
template basic_ostream<wchar_t>& operator<<(basic_ostream<wchar_t>&, const option&);

template <typename T>
basic_ostream<T>& operator<<(basic_ostream<T>& os, const map<string,option>& opts) {
	bool t = false;
	for (auto it : opts) {
		if (!it.second.is_undefined())
			os << (t ? " " : "") << it.second, t = true;
	}
	return os;
}
template basic_ostream<char>& operator<<(basic_ostream<char>&,
	const map<string,option>&);
template basic_ostream<wchar_t>& operator<<(basic_ostream<wchar_t>&,
	const map<string,option>&);

template <typename T>
basic_ostream<T>& operator<<(basic_ostream<T>& os, const options& o) {
	return os << o.opts; }
template basic_ostream<char>& operator<<(basic_ostream<char>&, const options&);
template
basic_ostream<wchar_t>& operator<<(basic_ostream<wchar_t>&, const options&);

template <typename T>
void tables::print(basic_ostream<T>& os, const tables::proof_elem& e) {
	if (e.rl != (size_t)-1) os << '[' << e.rl << ',' << e.al << "] ";
	for (const auto& b : e.b)
		os << b.first << ' ' << ir_handler->to_raw_term(b.second) << ' ';
	os << endl;
}
template
void tables::print<char>(basic_ostream<char>&, const tables::proof_elem&);
template
void tables::print<wchar_t>(basic_ostream<wchar_t>&, const tables::proof_elem&);

template <typename T>
void tables::print(basic_ostream<T>& os, const tables::proof& p) {
	for (size_t n = 0; n != p.size(); ++n)
		for (const auto& x : p[n]) {
			for (const auto& y : x.second)
				(os<<n<<' '<<ir_handler->to_raw_term(x.first)<<" :- "),
				print(os, y);
		}
}
template void tables::print<char>(basic_ostream<char>&, const tables::proof&);
template
void tables::print<wchar_t>(basic_ostream<wchar_t>&, const tables::proof&);

#ifdef DEBUG
template <typename T>
void tables::print(basic_ostream<T>& os, const tables::witness& w) {
	os << '[' << w.rl << ',' << w.al << "] ";
	for (const term& t : w.b) os << ir_handler->to_raw_term(t) << ", ";
	os << '.';
}

template void tables::print<char>(basic_ostream<char>&, const tables::witness&);
template
void tables::print<wchar_t>(basic_ostream<wchar_t>&, const tables::witness&);
#endif

/*void tables::print_env(const env& e) const {
	for (auto x : e) {
		int_t arg = r[n - 1];
		if (arg & 1) rt.e[n]=elem((char_t)(arg>>2));
		else if (arg & 2) rt.e[n]=elem((int_t)(arg>>2));
		else rt.e[n]=elem(elem::SYM, dict.get_sym(arg));
		o::out() << x.first << " = " << x.second << endl;
	}
	return os;
}*/

template <typename T>
basic_ostream<T>& tables::print(basic_ostream<T>& os, const vector<term>& v) const {
	os << ir_handler->to_raw_term(v[0]);
	if (v.size() == 1) return os << '.';
	os << " :- ";
	for (size_t n = 1; n != v.size(); ++n) {
		if (v[n].goal) os << '!';
		os << ir_handler->to_raw_term(v[n]) << (n == v.size() - 1 ? "." : ", ");
	}
	return os;
}
template basic_ostream<char>& tables::print(basic_ostream<char>&, const vector<term>&) const;
template basic_ostream<wchar_t>& tables::print(basic_ostream<wchar_t>&, const vector<term>&) const;

template <typename T>
basic_ostream<T>& tables::print(basic_ostream<T>& os, const flat_prog& p) const{
	for (const auto& x : p)
		print(os << (x[0].tab == -1 ? 0 : tbls[x[0].tab].priority) <<
			'\t', x) << endl;
/*	map<size_t, flat_prog> m;
	for (const auto& x : p) m[tbls[x[0].tab].priority].insert(x);
	size_t n = m.rbegin()->first;
	vector<flat_prog> v(n);
	for (const auto& x : m) v[n--] = move(x.second);
	for (n = 0; n != v.size(); ++n)
		for (const vector<term>& y : v[n])
			print(os << n << '\t', y) << endl;*/
	return os;
}
template basic_ostream<char>& tables::print(basic_ostream<char>&, const flat_prog&) const;
template basic_ostream<wchar_t>& tables::print(basic_ostream<wchar_t>&, const flat_prog&) const;

template <typename T>
basic_ostream<T>& tables::print_dict(basic_ostream<T>& os) const {
	return os << dict;
}
template basic_ostream<char>& tables::print_dict(basic_ostream<char>&) const;
template basic_ostream<wchar_t>& tables::print_dict(basic_ostream<wchar_t>&) const;

// rule printer for --print_updates
template <typename T>
basic_ostream<T>& tables::print(basic_ostream<T>& os, const rule& r) const {
	os << ir_handler->to_raw_term(r.t) << " :- ";
	//if (r.f) os << "(form printing not supported yet)"; // TODO fix transform_bin
	for (auto it = r.begin(); it != r.end(); ++it) {
		for (size_t n = 0; n != (*it)->bltins.size(); ++n) {
			os << ir_handler->to_raw_term((*it)->bltins[n]) <<
				(n == (*it)->bltins.size() - 1
					? it == r.end() - 1 ? "" : "; "
					: ", ");
		}
		if ((*it)->bltins.size())
			os << ((*it)->t.size() ? ", " : ".");
		for (size_t n = 0; n != (*it)->t.size(); ++n) {
			os << ir_handler->to_raw_term((*it)->t[n]) <<
				(n == (*it)->t.size() - 1
					? it == r.end()-1 ? "." : "; "
					: ", ");
		}
	}
	return os;
}
template
basic_ostream<char>& tables::print(basic_ostream<char>&, const rule&) const;
template basic_ostream<wchar_t>& tables::print(basic_ostream<wchar_t>&,
	const rule&) const;

template <typename T>
basic_ostream<T>& tables::print(basic_ostream<T>& os, const sig& s) const {
	bool sep = false;
	os << dict.get_rel(s.first) << "/";
	for (auto i : s.second) os << (sep?",":(sep=true,"")) << i;
	return os;
}
template basic_ostream<char>& tables::print(basic_ostream<char>&, const sig&)
	const;
template basic_ostream<wchar_t>& tables::print(basic_ostream<wchar_t>&,
	const sig&) const;

template <typename T>
basic_ostream<T>& tables::print(basic_ostream<T>& os, const table& t) const {
	print(os << "#\t", t.s) << (t.hidden ? "@":"")
		<< (t.idbltin > -1 ? " builtin" : "")
		<< endl;
	for (auto r : t.r) print(os << "#\t\t", rules[r]) << endl;
	return os;
}
template basic_ostream<char>& tables::print(basic_ostream<char>&, const table&)
	const;
template basic_ostream<wchar_t>& tables::print(basic_ostream<wchar_t>&,
	const table&) const;

template <typename T>
basic_ostream<T>& tables::print(basic_ostream<T>& os) const {
	os << "# " << tbls.size() << " tables:\n";
	for (size_t n = 0; n != tbls.size(); ++n)
		print(os << "# " << n << " ", tbls[n]);
	return os << "# -" << endl;
}
template basic_ostream<char>& tables::print(basic_ostream<char>&) const;
template basic_ostream<wchar_t>& tables::print(basic_ostream<wchar_t>&) const;

template <typename T>
basic_ostream<T>& operator<<(basic_ostream<T>& os, const dict_t& d) {
	os <<   "# nrels:   " << d.nrels() << '\t' << flush;
	for (size_t i = 0; i != d.nrels(); ++i)
		os << i << ":" << d.get_rel(i)
			<< (i != d.nrels() - 1 ? ", " : "");
	os << "\n# nsyms:   " << d.nsyms() << '\t' << flush;
	for (size_t i = 0; i != d.nsyms(); ++i)
		os << i << ":" << d.get_sym(i<<2)
			<< (i != d.nsyms() - 1 ? ", " : "");
	os << "\n# nvars:   " << d.nvars() << '\t';
	os << "\n# nbltins: " << d.nbltins() << '\t' << flush;
	for (size_t i = 0; i != d.nbltins(); ++i)
		os << i << ":" << d.get_bltin(i)
			<< (i != d.nbltins() - 1 ? ", " : "");
	return os << "\n# -" << endl;
}
template basic_ostream<char>& operator<<(basic_ostream<char>&, const dict_t&);
template
basic_ostream<wchar_t>& operator<<(basic_ostream<wchar_t>&, const dict_t&);

template <typename T, typename VT>
basic_ostream<T>& operator<<(basic_ostream<T>& os, const std::vector<VT>& hs) {
	os << "[ ";
	for(size_t i = 0; i < hs.size(); i++) {
		if(i != 0) os << ", ";
		os << hs[i];
	}
	return os << " ]";
}
template basic_ostream<char>& operator<<(basic_ostream<char>&, const bdd_handles&);
template
basic_ostream<wchar_t>& operator<<(basic_ostream<wchar_t>&, const bdd_handles&);
template basic_ostream<char>& operator<<(basic_ostream<char>&, const ints&);
template
basic_ostream<wchar_t>& operator<<(basic_ostream<wchar_t>&, const ints&);
template basic_ostream<char>& operator<<(basic_ostream<char>&, const uints&);
template
basic_ostream<wchar_t>& operator<<(basic_ostream<wchar_t>&, const uints&);

template <typename T, typename T1, typename T2>
basic_ostream<T>& operator<<(basic_ostream<T>& os, const std::map<T1,T2>& m) {
	os << "{\n";
	for (auto it : m) os << "\t" << it.first << ": " << it.second << endl;
	return os << " }";
}

template basic_ostream<char>& operator<<(basic_ostream<char>&, const varmap&);
template
basic_ostream<wchar_t>& operator<<(basic_ostream<wchar_t>&, const varmap&);

template basic_ostream<char>& operator<<(basic_ostream<char>&,
	const std::map<size_t, int_t>&);
template basic_ostream<wchar_t>& operator<<(basic_ostream<wchar_t>&,
	const std::map<size_t, int_t>&);

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
