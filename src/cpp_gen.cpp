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

/* It is sometimes desirable to embed a large amount of TML code into
 * this C++ codebase. Unfortunately, manually writing C++ code to
 * generate a certain TML fragment can be tedious. This pseudo-
 * transformation takes TML code and automatically produces the C++ code
 * necessary to generate the TML code. This transformation is used to
 * embed TML interpreter written in TML into this codebase. */

#include "cpp_gen.h"

using std::string;
using std::stringstream;
using std::vector;

// Generate C++ code to generate the given elem
ostream_t& cpp_gen::gen(ostream_t& os, std::string& name, const elem &e) {
	if (elem_cache.find(e) != elem_cache.end())return name=elem_cache[e],os;
	stringstream ss; ss << "e" << id++; name = ss.str();
	elem_cache[e] = name;
	if(e.type == elem::CHR) {
		os << "elem " << name;
		os << "(char32_t(" << ((uint32_t) e.ch) << "));\n";
	} else if(e.type == elem::NUM) {
		os << "elem " << name;
		os << "(int_t(" << e.num << "));\n";
	} else {
		os << "elem " << name;
		os << "(" << (
		e.type == elem::NONE      ? "elem::NONE" :
		e.type == elem::SYM       ? "elem::SYM" :
		e.type == elem::NUM       ? "elem::NUM" :
		e.type == elem::CHR       ? "elem::CHR" :
		e.type == elem::VAR       ? "elem::VAR" :
		e.type == elem::OPENP     ? "elem::OPENP" :
		e.type == elem::CLOSEP    ? "elem::CLOSEP" :
		e.type == elem::ALT       ? "elem::ALT" :
		e.type == elem::STR       ? "elem::STR" :
		e.type == elem::EQ        ? "elem::EQ" :
		e.type == elem::NEQ       ? "elem::NEQ" :
		e.type == elem::LEQ       ? "elem::LEQ" :
		e.type == elem::GT        ? "elem::GT" :
		e.type == elem::LT        ? "elem::LT" :
		e.type == elem::GEQ       ? "elem::GEQ" :
		e.type == elem::BLTIN     ? "elem::BLTIN" :
		e.type == elem::NOT       ? "elem::NOT" :
		e.type == elem::AND       ? "elem::AND" :
		e.type == elem::OR        ? "elem::OR" :
		e.type == elem::FORALL    ? "elem::FORALL" :
		e.type == elem::EXISTS    ? "elem::EXISTS" :
		e.type == elem::UNIQUE    ? "elem::UNIQUE" :
		e.type == elem::IMPLIES   ? "elem::IMPLIES" :
		e.type == elem::COIMPLIES ? "elem::COIMPLIES" :
		e.type == elem::ARITH     ? "elem::ARITH" :
		e.type == elem::OPENB     ? "elem::OPENB" :
		e.type == elem::CLOSEB    ? "elem::CLOSEB" :
		e.type == elem::OPENSB    ? "elem::OPENSB" :
		e.type == elem::CLOSESB   ? "elem::CLOSESB" : "")
		<< ", " << (
		e.arith_op == t_arith_op::NOP     ? "t_arith_op::NOP" :
		e.arith_op == t_arith_op::ADD     ? "t_arith_op::ADD" :
		e.arith_op == t_arith_op::SUB     ? "t_arith_op::SUB" :
		e.arith_op == t_arith_op::MULT    ? "t_arith_op::MULT" :
		e.arith_op == t_arith_op::BITWAND ? "t_arith_op::BITWAND" :
		e.arith_op == t_arith_op::BITWOR  ? "t_arith_op::BITWOR" :
		e.arith_op == t_arith_op::BITWXOR ? "t_arith_op::BITWXOR" :
		e.arith_op == t_arith_op::BITWNOT ? "t_arith_op::BITWNOT" :
		e.arith_op == t_arith_op::SHR     ? "t_arith_op::SHR" :
		e.arith_op == t_arith_op::SHL     ? "t_arith_op::SHL" : "")
		<< ", " << dict_name << ".get_lexeme(" <<
		std::quoted(to_string(lexeme2str(e.e))) << "));\n";
	}
	return os;
}

// Generate the C++ code to generate the given raw_term
ostream_t& cpp_gen::gen(ostream_t& os, std::string& name, const raw_term &rt) {
	vector<string> elem_names;
	for (const elem &e : rt.e)
		elem_names.emplace_back(), gen(os, elem_names.back(), e);
	stringstream ss; ss << "rt" + id++; name = ss.str();
	os << "raw_term " << name << "(" << (
		rt.extype == raw_term::REL        ? "raw_term::REL" :
		rt.extype == raw_term::EQ         ? "raw_term::EQ" :
		rt.extype == raw_term::LEQ        ? "raw_term::LEQ" :
		rt.extype == raw_term::BLTIN      ? "raw_term::BLTIN" :
		rt.extype == raw_term::ARITH      ? "raw_term::ARITH" :
		rt.extype == raw_term::CONSTRAINT ? "raw_term::CONSTRAINT" : "")
		<< ", " << (
		rt.arith_op == t_arith_op::NOP     ? "t_arith_op::NOP" :
		rt.arith_op == t_arith_op::ADD     ? "t_arith_op::ADD" :
		rt.arith_op == t_arith_op::SUB     ? "t_arith_op::SUB" :
		rt.arith_op == t_arith_op::MULT    ? "t_arith_op::MULT" :
		rt.arith_op == t_arith_op::BITWAND ? "t_arith_op::BITWAND" :
		rt.arith_op == t_arith_op::BITWOR  ? "t_arith_op::BITWOR" :
		rt.arith_op == t_arith_op::BITWXOR ? "t_arith_op::BITWXOR" :
		rt.arith_op == t_arith_op::BITWNOT ? "t_arith_op::BITWNOT" :
		rt.arith_op == t_arith_op::SHR     ? "t_arith_op::SHR" :
		rt.arith_op == t_arith_op::SHL     ? "t_arith_op::SHL" : "")
		<< ", {";
	for (const string &en : elem_names) os << en << ", ";
	return os << "});\n" << name << ".neg = " <<
		(rt.neg ? "true" : "false") <<";\n";
}

// Generate the C++ code to generate the raw_form_tree
ostream_t& cpp_gen::gen(ostream_t& os,std::string& name,const raw_form_tree &t){
	stringstream ss; ss << "ft" << id++; name = ss.str(); ss.str("");
	ss << "sprawformtree " << name << " = std::make_shared<raw_form_tree>(";
	string ename;
	switch (t.type) {
		case elem::IMPLIES:
		case elem::COIMPLIES:
		case elem::AND:
		case elem::ALT:
		case elem::EXISTS:
		case elem::UNIQUE:
		case elem::FORALL: {
			string lft_name, rft_name;
			gen(os, lft_name, *t.l);
			gen(os, rft_name, *t.r);
			os << ss.str() << "elem::" << (
				t.type == elem::IMPLIES   ? "IMPLIES" :
				t.type == elem::COIMPLIES ? "COIMPLIES" :
				t.type == elem::AND       ? "AND" :
				t.type == elem::ALT       ? "ALT" :
				t.type == elem::EXISTS    ? "EXISTS" :
				t.type == elem::UNIQUE    ? "UNIQUE" :
				t.type == elem::FORALL    ? "FORALL" : "")
				<< ", " << lft_name << ", " << rft_name
				<< ");\n";
			break;
		}
		case elem::NOT:
			gen(os, ename, *t.l);
			os << ss.str() << "elem::NOT, "	<< ename << ");\n";
			break;
		case elem::NONE:
			gen(os, ename, *t.rt);
			os << ss.str() << ename << ");\n";
			break;
		case elem::VAR:
			gen(os, ename, *t.el);
			os << ss.str() << "elem::VAR, "	<< ename << ");\n";
			break;
		default:
			assert(false); //should never reach here
	}
	return os;
}

// Generate the C++ code to generate the given TML rule
ostream_t& cpp_gen::gen(ostream_t& os, std::string& name, const raw_rule &rr) {
	vector<string> term_names;
	for (const raw_term &rt : rr.h)
		term_names.emplace_back(), gen(os, term_names.back(), rt);
	string prft_name;
	gen(os, prft_name, *rr.get_prft());
	stringstream ss; ss << "rr" << id++; name = ss.str();
	os << "raw_rule " << name << "({";
	for (const string &tn : term_names) os << tn << ", ";
	os << "}, ";
	if (rr.is_fact() || rr.is_goal()) os << "std::vector<raw_term> {}";
	else os << prft_name;
	return os << ");\n";
}

// Generate the C++ code to generate the given TML production rule
ostream_t& cpp_gen::gen(ostream_t& os, std::string& name, const production &g) {
	vector<string> elem_names;
	for (const elem &e : g.p)
		elem_names.emplace_back(), gen(os, elem_names.back(), e);
	vector<string> cnstr_names;
	for (const raw_term &c : g.c)
		cnstr_names.emplace_back(), gen(os, cnstr_names.back(), c);
	stringstream ss; ss << "gp" << id++; name = ss.str();
	os << "production " << name << "{{";
	for (const string &pn : elem_names) os << pn << ", ";
	os << "}, {";
	for (const string &cn : cnstr_names) os << cn << ", ";
	return os << "}, };\n";
}


// Generate the C++ code to generate the given TML lexeme
ostream_t& cpp_gen::gen(ostream_t& os, const lexeme &lex) {
	return os << "str2lexeme(" << to_string(lexeme2str(lex)) << ")";
}

// Generate the C++ code to generate the given TML directive
ostream_t& cpp_gen::gen(ostream_t& os, std::string& name, const directive &dir){
	stringstream ss; ss << "dir" << id++; name = ss.str();
	os << "directive " << name << ";\n";
	string ename;
	switch (dir.type) {
		case directive::STR: {
			os << name << ".type = directive::STR;\n";
			gen(os, ename, dir.rel);
			os << name << ".rel = " << ename << ";\n";
			os << name << ".arg = "; gen(os, dir.arg) << ";\n";
			break;
		}
		case directive::FNAME:
			os << name << ".type = directive::FNAME;\n";
			gen(os, ename, dir.rel);
			os << name << ".rel = " << ename << ";\n";
			os << name << ".arg = "; gen(os, dir.arg) << ";\n";
			break;
		case directive::CMDLINE:
			os << name << ".type = directive::CMDLINE;\n";
			gen(os, ename, dir.rel);
			os << name << ".rel = " << ename << ";\n";
			os << name << ".n = " << dir.n << ";\n";
			break;
		case directive::CMDLINEFILE:
			os << name << ".type = directive::CMDLINEFILE;\n";
			gen(os, ename, dir.rel);
			os << name << ".rel = " << ename << ";\n";
			os << name << ".n = " << dir.n << ";\n";
			break;
		case directive::STDIN:
			os << name << ".type = directive::STDIN;\n";
			gen(os, ename, dir.rel);
			os << name << ".rel = " << ename << ";\n";
			break;
		case directive::STDOUT:
			os << name << ".type = directive::STDOUT;\n";
			gen(os, ename, dir.t);
			os << name << ".t = " << ename << ";\n";
			break;
		case directive::TREE:
			os << name << ".type = directive::TREE;\n";
			gen(os, ename, dir.t);
			os << name << ".t = " << ename << ";\n";
			break;
		case directive::TRACE:
			os << name << ".type = directive::TRACE;\n";
			gen(os, ename, dir.rel);
			os << name << ".rel = " << ename << ";\n";
			break;
		case directive::BWD:
			os << name << ".type = directive::BWD;\n";
			break;
		case directive::EVAL:
			os << name << ".type = directive::EVAL;\n";
			gen(os, ename, dir.eval_sym);
			os << name << ".eval_sym = " << ename << ";\n";
			gen(os, ename, dir.domain_sym);
			os << name << ".domain_sym = " << ename << ";\n";
			gen(os, ename, dir.quote_sym);
			os << name << ".quote_sym = " << ename << ";\n";
			os <<name<<".timout_num = "<<dir.timeout_num.num<<";\n";
			break;
		case directive::QUOTE:
			os << name << ".type = directive::QUOTE;\n";
			gen(os, ename, dir.quote_sym);
			os << name << ".quote_sym = " << ename << ";\n";
			gen(os, ename, dir.domain_sym);
			os << name << ".domain_sym = " << ename << ";\n";
			gen(os, ename, dir.quote_str);
			os << name << ".quote_str = " << ename << ";\n";
			break;
		case directive::EDOMAIN:
			os << name << ".type = directive::EDOMAIN;\n";
			gen(os, ename, dir.domain_sym);
			os << name << ".domain_sym = " << ename << ";\n";
			os << name << ".limit_num = "<<dir.limit_num.num<<";\n";
			os << name << ".arity_num = "<<dir.arity_num.num<<";\n";
			break;
		case directive::CODEC:
			os << name << ".type = directive::CODEC;\n";
			gen(os, ename, dir.codec_sym);
			os << name << ".codec_sym = " << ename << ";\n";
			gen(os, ename, dir.domain_sym);
			os << name << ".domain_sym = " << ename << ";\n";
			gen(os, ename, dir.eval_sym);
			os << name << ".eval_sym = " << ename << ";\n";
			os << name << ".arity_num = "<<dir.arity_num.num<<";\n";
			break;
		case directive::INTERNAL:
			os << name << ".type = directive::INTERNAL;\n";
			gen(os, ename, dir.internal_term);
			os << name << ".internal_term = " << ename << ";\n";
			break;
	}
	return os;
}

// Generate the C++ code to generate the given TML program
ostream_t& cpp_gen::gen(ostream_t& os, std::string& name, const raw_prog &rp) {
	vector<string> dir_names;
	for (const directive &dir: rp.d)
		dir_names.emplace_back(), gen(os, dir_names.back(), dir);
	vector<string> prod_names;
	for (const production &g: rp.g)
		prod_names.emplace_back(), gen(os, prod_names.back(), g);
	vector<string> rule_names;
	for (const raw_rule &rr : rp.r)
		rule_names.emplace_back(), gen(os, rule_names.back(), rr);
	vector<string> prog_names;
	for (const raw_prog &np : rp.nps)
		prog_names.emplace_back(), gen(os, prog_names.back(), np);
	stringstream ss; ss << "rp" << id++; name = ss.str();
	os << "raw_prog " << name << "(" << dict_name << ");\n";
	// Insert the productions we have constructed into the final program
	if (prod_names.size()) {
		os << name << ".g.insert(" << name << ".g.end(), { ";
		for (const string &gn : prod_names) os << gn << ", ";
		os << "});\n";
	}
	// Insert the rules we have constructed into the final program
	if (rule_names.size()) {
		os << name << ".r.insert(" << name << ".r.end(), { ";
		for (const string &rn : rule_names) os << rn << ", ";
		os << "});\n";
	}
	// Insert the directives we have constructed into the final program
	if (dir_names.size()) {
		os << name << ".d.insert(" << name << ".d.end(), { ";
		for (const string &dn : dir_names) os << dn << ", ";
		os << "});\n";
	}
	// Insert the directives we have constructed into the final program
	if (prog_names.size()) {
		os << name << ".nps.insert(" << name << ".nps.end(), { ";
		for (const string &np : prog_names) os << np << ", ";
		os << "});\n";
	}	
	return os;
}

// Generate the C++ code to generate the given TML raw_progs
ostream_t& cpp_gen::gen(ostream_t& os, std::string& name, const raw_progs &rps){
	string pname;
	gen(os, pname, rps.p);
	stringstream ss; ss << "rps" << id++; name = ss.str();
	return os << "raw_progs " << name << "(" << dict_name << ");\n"
		<< name << ".p.merge(" << pname << ");\n";
}
