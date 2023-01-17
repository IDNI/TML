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
#ifndef __PRINTING_H__
#define __PRINTING_H__
#include "defs.h"
#include "input.h"
#include "output.h"
#include "options.h"
#include "tables.h"

namespace idni {

template <typename T, typename T1, typename T2>
std::basic_ostream<T>& operator<<(std::basic_ostream<T>& os,
	const std::map<T1,T2>& m);

template<typename T>
std::basic_ostream<T>& operator<<(std::basic_ostream<T>& os, const env& e);

template <typename T>
std::basic_ostream<T>& operator<<(std::basic_ostream<T>& os, const vbools& x);

struct elem;

std::string quote_sym(const elem& e);

template <typename T>
std::basic_ostream<T>& operator<<(std::basic_ostream<T>& os,
	const std::pair<ccs, size_t>& p)
{
	for (size_t n = 0; n != p.second; ++n) os << p.first[n];
	return os;
}

#ifdef DEBUG
template <typename T>
std::basic_ostream<T>& operator<<(std::basic_ostream<T>& os, const bools& x) {
	for (auto y : x) os << (y?1:0);
	return os;
}
template <typename T>
std::basic_ostream<T>& operator<<(std::basic_ostream<T>& os, const vbools& x) {
	for (auto y : x) os << y << "\n";
	return os;
}
template <typename T>
std::basic_ostream<T>& operator<<(std::basic_ostream<T>& os, const term& t) {
	os << "[" << t.tab << "] ";
	if (t.neg) os << "~ ";
	for (size_t n = 0; n != t.size(); ++n) {
		os << t[n];
		if (n != t.size()-1) os << " ";
	}
	return os;
}
#endif

template <typename T>
std::basic_ostream<T>& operator<<(std::basic_ostream<T>& os,
	const directive& d)
{
	os << '@';
	if (d.type == directive::BWD) return os << "bwd.";
	if (d.type == directive::TRACE) return os << "trace.\n";
	if (d.type == directive::EDOMAIN)
		return os << "domain " << d.domain_sym <<' '<< d.limit_num <<' '
			<< d.arity_num << '.';
	if (d.type == directive::EVAL)
		return os << "eval " << d.eval_sym << ' ' << d.domain_sym << ' '
			<< d.quote_sym << ' ' << d.timeout_num << '.';
	if (d.type == directive::QUOTE)
		return os << "quote " << d.quote_sym <<' ' << d.domain_sym <<' '
			<< d.quote_str << '.';
	if (d.type == directive::CODEC)
		return os << "codec " << d.codec_sym <<' ' << d.domain_sym <<' '
			<< d.quote_sym << ' ' << d.arity_num << '.';
	if (d.type == directive::INTERNAL)
		return os << "internal " << d.internal_term << '.';
	if (d.type == directive::STDOUT) os << "stdout ";
	else os << "string ";
	if (d.type == directive::TREE) return os << d.t << '.';
	return os << d.rel << ' ' << d.arg << '.';
}

template <typename T>
std::basic_ostream<T>& operator<<(std::basic_ostream<T>& os, const elem& e) {
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


template <typename T>
std::basic_ostream<T>& operator<<(std::basic_ostream<T>& os,
	const production& p)
{
	os << p.p[0] << " => ";
	for (size_t n = 1; n  < p.p.size(); ++n) os << p.p[n] << ' ';
	for (size_t n = 0; n != p.c.size(); ++n) os << ", " << p.c[n];
	return os << '.';
}

template <typename T>
std::basic_ostream<T>& operator<<(std::basic_ostream<T>& os,
	const raw_form_tree &t)
{
	if (t.guard_lx != lexeme{ 0, 0 }) os << t.guard_lx << "() && { ";
	if (t.neg) os << "~ { ";
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
	if (t.neg) os << " }";
	if (t.guard_lx != lexeme{ 0, 0 }) os << " }";
	return os;
}

#ifdef DEBUG
template <typename T>
std::basic_ostream<T>& print_raw_form_tree(std::basic_ostream<T>& os,
	const raw_form_tree &t, bool root)
{
	if (root) os << "@";
	os << "[" << t.type << "]";
	if (root) os << "@";
	switch(t.type) {
		case elem::IMPLIES:
			os << "{";
			if (!t.l) os << "NULL";
			else print_raw_form_tree(os, *t.l, false);
			os << " -> ";
			if (!t.r) os << "NULL";
			else print_raw_form_tree(os, *t.r, false);
			os << "}";
			break;
		case elem::COIMPLIES:
			os << "{";
			if (!t.l) os << "NULL";
			else print_raw_form_tree(os, *t.l, false);
			os << " <-> ";
			if (!t.r) os << "NULL";
			else print_raw_form_tree(os, *t.r, false);
			os << "}";
			break;
		case elem::AND:
			os << "{";
			if (!t.l) os << "NULL";
			else print_raw_form_tree(os, *t.l, false);
			os << " && ";
			if (!t.r) os << "NULL";
			else print_raw_form_tree(os, *t.r, false);
			os << "}";
			break;
		case elem::ALT:
			os << "{";
			if (!t.l) os << "NULL";
			else print_raw_form_tree(os, *t.l, false);
			os << " || ";
			if (!t.r) os << "NULL";
			else print_raw_form_tree(os, *t.r, false);
			os << "}";
			break;
		case elem::NOT:
			os << "~{";
			if (!t.l) os << "NULL";
			else print_raw_form_tree(os, *t.l, false);
			os << "}";
			break;
		case elem::EXISTS:
			os << "exists ";
			if (!t.l) os << "NULL";
			else print_raw_form_tree(os, *t.l, false);
			os << " { ";
			if (!t.r) os << "NULL";
			else print_raw_form_tree(os, *t.r, false);
			os << " }";
			break;
		case elem::UNIQUE:
			os << "unique ";
			if (!t.l) os << "NULL";
			else print_raw_form_tree(os, *t.l, false);
			os << " { ";
			if (!t.r) os << "NULL";
			else print_raw_form_tree(os, *t.r, false);
			os << " }";
			break;
		case elem::FORALL:
			os << "forall ";
			if (!t.l) os << "NULL";
			else print_raw_form_tree(os, *t.l, false);
			os << " { ";
			if (!t.r) os << "NULL";
			else print_raw_form_tree(os, *t.r, false);
			os << " }";
			break;
		case elem::NONE:
			os << "#" << *t.rt << "#";
			break;
		case elem::SYM: case elem::VAR:
			os << "%" << *t.el << "%";
			break;
		default:
			assert(false); //should never reach here
	}
	return os;
}
#endif // DEBUG

template <typename T>
std::basic_ostream<T>& operator<<(std::basic_ostream<T>& os, const raw_term& t){
	if (t.neg) os << '~';
	if (t.extype == raw_term::ARITH || t.extype == raw_term::CONSTRAINT) {
		if (t.neg) os << '{';
		for ( elem el : t.e) os << el;
		if (t.neg) os << '}';
		return os;
	}
	//understand raw_term::parse before touching this
	if (t.extype == raw_term::EQ)  {
		if (t.neg) os << '{';
		os << t.e[0] << "=" << t.e[2];
		if (t.neg) os << '}';
		return os;
	}
	//understand raw_term::parse before touching this
	if (t.extype == raw_term::LEQ) {
		if (t.neg) os << '{';
		if (t.e[1].type == elem::GT || t.e[1].type == elem::LEQ)
			os << t.e[0] << "<=" << t.e[2];
		else if (t.e[1].type == elem::LT || t.e[1].type == elem::GEQ)
			os << t.e[2] << "<=" << t.e[0];
		else
			assert(false);
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
template <typename T>
std::basic_ostream<T>& operator<<(std::basic_ostream<T>& os,
	const std::pair<elem, bool>& p)
{
	const elem& e  = p.first;
	return p.second && e.type == elem::CHR
		? os << to_string(to_string_t(e.ch))
		: os << e;
}

template <typename T>
std::basic_ostream<T>& operator<<(std::basic_ostream<T>& os,
	// raw_term, delimiter, skip n args
	const std::tuple<raw_term, std::string, int_t>& p)
{
	const raw_term& t   = get<0>(p);
	const std::string& delim = get<1>(p);
	const int_t& skip   = get<2>(p);
	for (size_t ar = 0, n = 1; ar != t.arity.size();) {
		while (t.arity[ar] == -1) ++ar, os << '(';
		if (n >= t.e.size()) break;
		while (t.e[n].type == elem::OPENP) ++n;
		n += skip;
		for (int_t k = skip; k != t.arity[ar];) {
			if (n > 1) os << std::pair{ t.e[n++], true };
			if (++k != t.arity[ar] && n > 1 && delim.length())
				os << delim;
		}
		while (n < t.e.size() && t.e[n].type == elem::CLOSEP) ++n;
		++ar;
		while (ar < t.arity.size() && t.arity[ar] == -2) ++ar, os <<')';
	}
	return os;
}

template <typename T>
std::basic_ostream<T>& operator<<(std::basic_ostream<T>& os, const raw_rule& r){
	return print_raw_rule(os, r, 0);
}

template <typename T>
std::basic_ostream<T>& operator<<(std::basic_ostream<T>& os, const macro& m) {
	os << m.def << " := ";
	for (size_t k = 0; k != m.b.size(); ++k)
		os << m.b[k] << (k != m.b.size()-1 ? ", " : "");
	return os << ".";
}

template <typename T>
std::basic_ostream<T>& print_typedecl(std::basic_ostream<T>& os,
	const struct typedecl& td, bool comma = false)
{
	switch (td.pty.ty) {
		case primtype::UCHAR: os << "char"; break;
		case primtype::SYMB:  os << "sym"; break;
		case primtype::UINT:  os << "int";
			if (td.pty.bsz > 0) os << ':' << td.pty.bsz;
			break;
		case primtype::NOP:   os << td.structname; break;
		default: assert(false);
	}
	os << " ";
	std::string sep = comma ? ", " : " ";
	for (size_t k = 0; k != td.vars.size(); ++k)
		os << td.vars[k] << (k != td.vars.size()-1 ? sep : "");
	return os;
}

template <typename T>
std::basic_ostream<T>& operator<<(std::basic_ostream<T>& os,
	const struct typestmt& ts)
{
	if (ts.is_predicate()) {
		os << "predtype " << ts.reln << "(";
		for (size_t k = 0; k != ts.typeargs.size(); ++k)
			print_typedecl(os, ts.typeargs[k]) <<
				(k != ts.typeargs.size()-1 ? ", " : "");
		os << ").";
	} else {
		os << "struct " << ts.rty.structname << " {\n";
		for (size_t k = 0; k != ts.rty.membdecl.size(); ++k)
			print_typedecl(os << "\t", ts.rty.membdecl[k], true) <<
			".\n";
		os << "}";
	}
	return os;
}

template <typename T>
std::basic_ostream<T>& operator<<(std::basic_ostream<T>& os,
	const std::set<raw_term>& rts)
{
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

template <typename T>
std::basic_ostream<T>& operator<<(std::basic_ostream<T>& os,
	const std::vector<raw_term>& rts)
{
	os << '[';
	for(size_t i = 0; i < rts.size(); i++) {
		if(i != 0) {
			os << ", ";
		}
		os << rts[i];
	}
	return os << ']';
}

template <typename T>
std::basic_ostream<T>& print_raw_rule(std::basic_ostream<T>& os,
	const raw_rule& r, size_t level)
{
	bool compact = true;
	std::basic_string<T>indent(level, '\t');
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
	if (!compact && !noendl) os << "\n";
	if (r.prft) os << *r.prft;
	for (size_t n = 0; n < r.b.size(); ++n) {
		for (size_t k = 0; k < r.b[n].size(); ++k)
			if (((compact||uni?os<<"":os<<indent<<'\t')<<r.b[n][k]),
				k != r.b[n].size() - 1)
					os << ',' << (compact ? " " : "\n");
		if (n != r.b.size() - 1) os << ';' << "\n";
	}
	return os << '.';
}

// TODO this is just a draft printer for raw form tree - not completly correct
template <typename T>
std::basic_ostream<T>& operator<<(std::basic_ostream<T>& os,
	const sprawformtree prft)
{
	lexeme guard_lx = prft->guard_lx;
	auto is_quantifier = [](const sprawformtree prft) -> bool {
		return prft->type == elem::EXISTS ||
			prft->type == elem::FORALL ||
			prft->type == elem::UNIQUE;
	};
	const sprawformtree node = prft;
	//if (guard_lx != lexeme{ 0, 0 }) // find first node after quantifiers
	//	while (node && is_quantifier(node)) node = node->r;
	std::function<std::basic_ostream<T>&(const sprawformtree)> print_node;
	print_node = [&os, &print_node, &guard_lx, &node, &is_quantifier]
		(const sprawformtree prft) -> std::basic_ostream<T>&
	{
		std::basic_ostringstream<T> op;
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

template <typename T>
std::basic_ostream<T>& print_state_block(std::basic_ostream<T>& os,
	const state_block& sb, size_t level)
{
	std::basic_string<T> indent(level, '\t');
	return print_raw_prog_tree(os << indent << '[' << sb.label
		<< (sb.flip ? "~" : "") << ":\n",
		sb.p, level+1) << indent << "]";
}

template <typename T>
std::basic_ostream<T>& operator<<(std::basic_ostream<T>& os,
	const state_block& sb) { return print_state_block(os, sb, 0); }

template <typename T>
std::basic_ostream<T>& operator<<(std::basic_ostream<T>& os, const raw_prog& p){
	return print_raw_prog_tree<T>(os, p, 0);
}

template <typename T>
std::basic_ostream<T>& print_raw_prog_tree(std::basic_ostream<T>& os,
	const raw_prog& p, size_t level)
{
	std::basic_string<T> indent(level, '\t');
	if (p.type != raw_prog::PFP) os << indent << "# "<< (int_t)p.type<<"\n";
	for (auto x : p.vts) os << indent << x << "\n";
	for (auto x : p.d) os << indent << x << "\n";
	for (auto x : p.g) os << indent << x << "\n";
	for (auto x : p.r) print_raw_rule(os, x, level) << "\n";
	for (auto x : p.sbs) print_state_block(os, x, level) << "\n";
	for (auto x : p.nps) print_raw_prog_tree(os << indent << "{\n",
		x, level+1) << indent << "}\n";
	return os;
}

template <typename T>
std::basic_ostream<T>& operator<<(std::basic_ostream<T>& os,const raw_progs& p){
	return os << p.p;
}

template <typename T>
std::basic_ostream<T>& operator<<(std::basic_ostream<T>& os, const output& o) {
	return os << o.target();
}

template <typename T>
std::basic_ostream<T>& operator<<(std::basic_ostream<T>& os, const option& o) {
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
			std::string s = o.get_string();
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

template <typename T>
std::basic_ostream<T>& operator<<(std::basic_ostream<T>& os,
	const std::map<std::string, option>& opts)
{
	bool t = false;
	for (auto it : opts) {
		if (!it.second.is_undefined())
			os << (t ? " " : "") << it.second, t = true;
	}
	return os;
}

template <typename T>
std::basic_ostream<T>& operator<<(std::basic_ostream<T>& os, const options& o) {
	return os << o.opts;
}

template <typename T>
void tables::print(std::basic_ostream<T>& os, const tables::proof_elem& e) {
	if (e.rl != (size_t)-1) os << '[' << e.rl << ',' << e.al << "] ";
	for (const auto& b : e.b)
		os << b.first << ' ' << ir_handler->to_raw_term(b.second) << ' ';
	os << "\n";
}

template <typename T>
void tables::print(std::basic_ostream<T>& os, const tables::proof& p) {
	for (size_t n = 0; n != p.size(); ++n)
		for (const auto& x : p[n]) {
			for (const auto& y : x.second)
				(os<<n<<' '<<ir_handler->to_raw_term(x.first)<<" :- "),
				print(os, y);
		}
}

#ifdef DEBUG
template <typename T>
void tables::print(std::basic_ostream<T>& os, const tables::witness& w) {
	os << '[' << w.rl << ',' << w.al << "] ";
	for (const term& t : w.b) os << ir_handler->to_raw_term(t) << ", ";
	os << '.';
}
#endif

template <typename T>
std::basic_ostream<T>& tables::print(std::basic_ostream<T>& os,
	const std::vector<term>& v) const
{
	os << ir_handler->to_raw_term(v[0]);
	if (v.size() == 1) return os << '.';
	os << " :- ";
	for (size_t n = 1; n != v.size(); ++n) {
		if (v[n].goal) os << '!';
		os << ir_handler->to_raw_term(v[n]) << (n == v.size() - 1 ? "." : ", ");
	}
	return os;
}

template <typename T>
std::basic_ostream<T>& tables::print(std::basic_ostream<T>& os,
	const flat_prog& p) const
{
	for (const auto& x : p)
		print(os << (x[0].tab == -1 ? 0 : tbls[x[0].tab].priority) <<
			'\t', x) << "\n";
	return os;
}

template <typename T>
std::basic_ostream<T>& tables::print_dict(std::basic_ostream<T>& os) const {
	return os << dict;
}

// rule printer for --print_updates
template <typename T>
std::basic_ostream<T>& tables::print(std::basic_ostream<T>& os, const rule& r)
	const
{
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

template <typename T>
std::basic_ostream<T>& tables::print(std::basic_ostream<T>& os, const table& t)
	const
{
	//print(os << "#\t", "UNDEF" /*t.s*/)
	os	<< (t.hidden ? "@":"")
		<< (t.idbltin > -1 ? " builtin" : "")
		<< "\n";
	for (auto r : t.r) print(os << "#\t\t", rules[r]) << "\n";
	return os;
}

template <typename T>
std::basic_ostream<T>& tables::print(std::basic_ostream<T>& os) const {
	os << "# " << tbls.size() << " tables:\n";
	for (size_t n = 0; n != tbls.size(); ++n)
		print(os << "# " << n << " ", tbls[n]);
	return os << "# -\n";
}

template <typename T>
std::basic_ostream<T>& operator<<(std::basic_ostream<T>& os, const dict_t& d) {
	os <<   "# nrels:   " << d.nrels() << '\t';
	for (size_t i = 0; i != d.nrels(); ++i)
		os << i << ":" << d.get_rel_lexeme(i)
			<< (i != d.nrels() - 1 ? ", " : "");
	os << "\n# nsyms:   " << d.nsyms() << '\t';
	for (size_t i = 0; i != d.nsyms(); ++i)
		os << i << ":" << d.get_sym_lexeme(i)
			<< (i != d.nsyms() - 1 ? ", " : "");
	os << "\n# nvars:   " << d.nvars() << '\t';
	os << "\n# nbltins: " << d.nbltins() << '\t';
	for (size_t i = 0; i != d.nbltins(); ++i)
		os << i << ":" << d.get_bltin_lexeme(i)
			<< (i != d.nbltins() - 1 ? ", " : "");
	return os << "\n# -" << std::endl;
}

template <typename T, typename VT>
std::basic_ostream<T>& operator<<(std::basic_ostream<T>& os,
	const std::vector<VT>& hs)
{
	os << "[ ";
	for(size_t i = 0; i < hs.size(); i++) {
		if(i != 0) os << ", ";
		os << hs[i];
	}
	return os << " ]";
}

template <typename T, typename T1, typename T2>
std::basic_ostream<T>& operator<<(std::basic_ostream<T>& os,
	const std::map<T1,T2>& m)
{
	os << "{\n";
	for (auto it : m) os << "\t" << it.first << ": " << it.second << "\n";
	return os << " }";
}

} // idni namespace
#endif
