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
}

bool outputs::add(sp_output out) {
	string n = out->name();
	auto it = find(n);
	if (it != end()) {
		CERR << "already exists: " << n << " target: "
			<< out->target() << endl;
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
	os << t.tab << ' ';
	if (t.neg) os << '~';
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
		case elem::NUM: return os << e.num;
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
	} else {
		os << e; // CHR, OPENP, CLOSEP or NUM = no quotes
	}
	return ws2s(os.str());
}

template <typename T>
basic_ostream<T>& operator<<(basic_ostream<T>& os, const raw_term& t) {
	if (t.neg) os << '~';
	
	if( t.extype == raw_term::ARITH || 
		t.extype == raw_term::EQ 	|| 
		t.extype == raw_term::LEQ 	) {
		for ( elem el : t.e) 
			os << el;
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
basic_ostream<T>& operator<<(basic_ostream<T>& os,
	const pair<raw_term, string>& p)
{
	const raw_term& t = p.first;
	//if (t.neg) os << '~';
	//os << t.e[0];
	//os << '(';
	for (size_t ar = 0, n = 1; ar != t.arity.size();) {
		while (t.arity[ar] == -1) ++ar, os << '(';
		if (n >= t.e.size()) break;
		while (t.e[n].type == elem::OPENP) ++n;
		for (int_t k = 0; k != t.arity[ar];)
			if ((os << quote_sym(t.e[n++])), ++k != t.arity[ar])
				os << ' ';
		while (n < t.e.size() && t.e[n].type == elem::CLOSEP) ++n;
		++ar;
		while (ar < t.arity.size() && t.arity[ar] == -2) ++ar, os << ')';
	}
	return os; // << ')';
}
template basic_ostream<char>& operator<<(basic_ostream<char>&,
	const pair<raw_term, string>&);
template basic_ostream<wchar_t>& operator<<(basic_ostream<wchar_t>&,
	const pair<raw_term, string>&);

template <typename T>
basic_ostream<T>& operator<<(basic_ostream<T>& os, const raw_rule& r) {
	return print_raw_rule(os, r, 0);
}
template basic_ostream<char>& operator<<(basic_ostream<char>&, const raw_rule&);
template
basic_ostream<wchar_t>& operator<<(basic_ostream<wchar_t>&, const raw_rule&);

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
	if (!r.b.size() && !r.prft.get()) return os << '.';
	os << " :- ";
	bool uni = r.b.size() == 1 && r.b[0].size() == 1;
	bool noendl = !r.b.size() || uni;
	if (!compact && !noendl) os << endl;
	if (r.prft.get()) os << r.prft.get();
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
basic_ostream<T>& operator<<(basic_ostream<T>& os, const raw_form_tree* prft) {
	lexeme guard_lx = prft->guard_lx;
	auto is_quantifier = [](const raw_form_tree* prft) -> bool {
		return prft->type == elem::EXISTS ||
			prft->type == elem::FORALL ||
			prft->type == elem::UNIQUE;
	};
	const raw_form_tree *node = prft;
	//if (guard_lx != lexeme{ 0, 0 }) // find first node after quantifiers
	//	while (node && is_quantifier(node)) node = node->r;
	function<basic_ostream<T>&(const raw_form_tree*)> print_node;
	print_node = [&os, &print_node, &guard_lx, &node, &is_quantifier]
		(const raw_form_tree* prft) -> basic_ostream<T>&
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
	const raw_form_tree* prft);
template basic_ostream<wchar_t>& operator<<(basic_ostream<wchar_t>&,
	const raw_form_tree* prft);

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
template
basic_ostream<wchar_t>& operator<<(basic_ostream<wchar_t>&, const option&);

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
		os << b.first << ' ' << to_raw_term(b.second) << ' ';
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
				(os<<n<<' '<<to_raw_term(x.first)<<" :- "),
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
	for (const term& t : w.b) os << to_raw_term(t) << ", ";
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

// rule printer for --print_updates
template <typename T>
basic_ostream<T>& tables::print(basic_ostream<T>& os, const rule& r) const {
	os << to_raw_term(r.t) << " :- ";
	//if (r.f) os << "(form printing not supported yet)"; // TODO fix transform_bin
	for (auto it = r.begin(); it != r.end(); ++it)
		for (size_t n = 0; n != (*it)->t.size(); ++n)
			os << to_raw_term((*it)->t[n]) << (n==(*it)->t.size()-1
				? it == r.end()-1 ? "." : "; "
				: ", ");
	return os;
}
template
basic_ostream<char>& tables::print(basic_ostream<char>&, const rule&) const;
template basic_ostream<wchar_t>& tables::print(basic_ostream<wchar_t>&,
	const rule&) const;

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
	return os << endl;
}
template basic_ostream<char>& operator<<(basic_ostream<char>&, const dict_t&);
template
basic_ostream<wchar_t>& operator<<(basic_ostream<wchar_t>&, const dict_t&);
