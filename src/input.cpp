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
#include <string>
#include <cstring>
#include <sstream>
#include <fstream>
#include <vector>
#include "input.h"
#include "err.h"
#include "output.h"
#include "analysis.h"
using namespace std;

int_t raw_prog::last_id = 0;
bool raw_prog::require_guards = false;
bool raw_prog::require_state_blocks = false;
bool raw_term::require_fp_step = false;

input::input(string f, bool ns) : type_(FILE), newseq(ns), mm_(f),
	beg_((ccs)(mm_.data())), data_(beg_), size_(mm_.size()),
	allocated_(false)
{
	//COUT << "created file(mmap) input: " << beg_ << endl;
	//COUT << "mmap input: " << f << " size: " << size_ << "\n";
	//COUT << mm_.data() << "\n";
	//COUT << "begin char:    " << (const char*) beg_ << "\n";
	if (mm_.error) {
		//CERR << "error: " << mm_.error_message <<endl;
		throw_runtime_error(err_fnf, f);
		error = true;
	}
}

input::~input() {
	//COUT << "destroying input" << (allocated_ ? " freeing *" : "")
	//	<< " data: " << beg_ << endl;
	if (allocated_) free((void*)beg_);
}

lexeme input::lex(pccs s) {
#define PE(pe) ((pe), lexeme{ 0, 0 })
	while (isspace(**s)) ++*s;
	if (!**s) return { 0, 0 };
	ccs t = *s;
	if (!strncmp(*s, "/*", 2)) {
		while (strncmp(++*s, "*/", 2))
			if (!**s) return PE(parse_error(t, err_comment, 0));
		return ++++*s, lex(s);
	}
	if (**s == '#') {
		while (*++*s != '\r' && **s != '\n' && **s);
		return lex(s);
	}
	if (**s == '"') {
		while (*++*s != '"')
			if (!**s) return PE(parse_error(t, unmatched_quotes));
			else if (**s == '\\') ++(*s); // allow any escape seq.
			//else if (**s == '\\' && !strchr("\\\"", *++*s))
			//	return PE(parse_error(*s, err_escape));
		return { t, ++(*s) };
	}
	if (**s == '`') {
		while (*++*s != '`')
			if (!**s) return PE(parse_error(t, unmatched_quotes));
			else if (**s == '\\' && !strchr("\\`", *++*s))
				return PE(parse_error(*s, err_escape));
		return { t, ++(*s) };
	}

	if (**s == '-' && *(*s + 1) == '>') return *s += 2, lexeme{*s - 2, *s};
	if (**s == '<' && *(*s + 1) == '-' && *(*s + 2) == '>')
		return *s += 3, lexeme{ *s - 3, *s };

	if (**s == '&' && *(*s + 1) == '&') return *s += 2, lexeme{*s - 2, *s};
	if (**s == '|' && *(*s + 1) == '|') return *s += 2, lexeme{*s - 2, *s};

	if (	(**s == '<' && *(*s + 1) == '=') ||
		(**s == '>' && *(*s + 1) == '=') ||
		(**s == '!' && *(*s + 1) == '=') )
		return *s += 2, lexeme{ *s - 2, *s };

	if (**s == '>' && (*(*s + 1) == '>')) return *s += 2, lexeme{*s-2, *s};
	if (**s == '<' && (*(*s + 1) == '<')) return *s += 2, lexeme{*s-2, *s};

	if (**s == ':' && (*(*s+1)=='-' || *(*s+1)=='='))
		return *s += 2, lexeme{ *s-2, *s };

	if (**s == '\'') {
		if (*(*s + 1) == '\'') return { t, ++++*s };
		if (*(*s + 1) == '\\') {
			if (*(*s+2) == 'x')
				return	(*(*s+5) != '\'') ?
					PE(parse_error(*s, err_x_escape)) :
					lexeme{ t, *s += 6 };
			if (*(*s+2) == 'u')
				return	(*(*s+7) != '\'') ?
					PE(parse_error(*s, err_u_escape)) :
					lexeme{ t, *s += 8 };
			return { t, *s += 4 };
		}
		char32_t ch;
		size_t chl = peek_codepoint(*s+1, size_ - ((*s+1) - beg_), ch);
		if (*(*s+1+chl) != '\'') return PE(parse_error(*s+2,err_quote));
		return { t, (*s += 2 + chl) };
	}

	if (strchr("!~.,;(){}[]$@=<>|&^+*-:", **s)) return ++*s,lexeme{*s-1,*s};
	if (strchr("?", **s)) ++*s;
	size_t chl, maxs = size_ - (*s - beg_);
	if (!is_alnum(*s, maxs, chl) && **s != '_')
		return PE(parse_error(*s, err_chr));
	while (**s && (is_alnum(*s, maxs, chl) || **s == '_')) *s += chl;
	return { t, *s };
#undef PE
}

lexemes& input::prog_lex() {
	lexeme e;
	error = false;
	do { if ((e=lex(&data_)) != lexeme{0,0}) l.push_back(e);
	} while (!error && *(data_));
	size_ = (data_ - beg_) * sizeof(ccs);
	return l;
}

int_t input::get_int_t(ccs from, ccs to) {
	int_t r = 0;
	bool neg = false;
	if (*from == '-') neg = true, ++from;
	for (ccs s = from; s != to; ++s)
		if (!isdigit(*s)) parse_error(from, err_int);
	string s((const char*) from, to - from);
#ifdef WITH_EXCEPTIONS
	try {
#endif
		r = stoll(s);
#ifdef WITH_EXCEPTIONS
	} catch (...) { parse_error(from, err_int); }
#else
	if (s != to_string_(r)) parse_error(from, err_int);
#endif
	return neg ? -r : r;
}

bool directive::parse(input* in, const raw_prog& prog) {
	const lexemes& l = in->l; size_t& pos = in->pos;
	if (*l[pos][0] != '@') return false;
	if (l[++pos] == "trace") {
		type = TRACE; ++pos;
		if (!rel.parse(in) || rel.type != elem::SYM)
			return	in->parse_error(l[pos-1][0],
				err_trace_rel, l[pos-1]);
		if (*l[pos++][0] != '.')
			return	in->parse_error(l[pos-1][0],
				dot_expected, l[pos-1]);
		return true;
	}
	if (l[pos] == "bwd") {
		type = BWD;
		if (*l[++pos][0] != '.')
			return in->parse_error(l[pos][0], dot_expected, l[pos]);
		return ++pos, true;
	}
	// Parse @internal <internal_term>.
	if (l[pos] == "internal") {
		type = INTERNAL; pos++;
		if (!internal_term.parse(in, prog))
			return in->parse_error(l[pos-1][0], err_internal_term, l[pos-1]);
		if (*l[pos++][0] != '.') return
			in->parse_error(l[pos-1][0], dot_expected, l[pos-1]);
		return true;
	}
#ifdef WITH_EVAL
	// Parse @domain <domain_sym> <limit_num> <arity_num>.
	if (l[pos] == "domain") {
		type = EDOMAIN; ++pos;
		if (!domain_sym.parse(in) || domain_sym.type != elem::SYM)
			return in->parse_error(l[pos-1][0], err_domain_sym, l[pos-1]);
		if (!limit_num.parse(in) || limit_num.type != elem::NUM)
			return in->parse_error(l[pos-1][0], err_limit_num, l[pos-1]);
		if (!arity_num.parse(in) || arity_num.type != elem::NUM)
			return in->parse_error(l[pos-1][0], err_arity_num, l[pos-1]);
		if (*l[pos++][0] != '.') return
			in->parse_error(l[pos-1][0], dot_expected, l[pos-1]);
		return true;
	}
	// Parse @eval <eval_sym> <domain_sym> <quote_sym> <timeout_num>.
	if (l[pos] == "eval") {
		type = EVAL; ++pos;
		if (!eval_sym.parse(in) || eval_sym.type != elem::SYM)
			return	in->parse_error(l[pos-1][0],
				err_eval_sym, l[pos-1]);
		if (!domain_sym.parse(in) || domain_sym.type != elem::SYM)
			return	in->parse_error(l[pos-1][0],
				err_domain_sym, l[pos-1]);
		if (!quote_sym.parse(in) || quote_sym.type != elem::SYM)
			return	in->parse_error(l[pos-1][0],
				err_quote_sym, l[pos-1]);
		if (!timeout_num.parse(in) || timeout_num.type != elem::NUM)
			return	in->parse_error(l[pos-1][0],
				err_timeout_num, l[pos-1]);
		if (*l[pos++][0] != '.')
			return	in->parse_error(l[pos-1][0],
				dot_expected, l[pos-1]);
		return true;
	}
	// Parse @quote <quote_sym> <domain_sym> <quote_str>.
	if (l[pos] == "quote") {
		type = QUOTE; ++pos;
		if (!quote_sym.parse(in) || quote_sym.type != elem::SYM)
			return	in->parse_error(l[pos-1][0],
				err_quote_sym, l[pos-1]);
		if (!domain_sym.parse(in) || domain_sym.type != elem::SYM)
			return	in->parse_error(l[pos-1][0], err_domain_sym,
				l[pos-1]);
		if (!quote_str.parse(in) || quote_str.type != elem::STR ||
				quote_str.e[1] <= quote_str.e[0] ||
				*quote_str.e[0] != '`')
			return	in->parse_error(l[pos-1][0], err_quote_str,
				l[pos-1]);
		if (*l[pos++][0] != '.')
			return	in->parse_error(l[pos-1][0], dot_expected,
				l[pos-1]);
		return true;
	}
	// Parse @codec <codec_sym> <domain_sym> <eval_str> <arity_num>.
	if (l[pos] == "codec") {
		type = CODEC; ++pos;
		if (!codec_sym.parse(in) || codec_sym.type != elem::SYM)
			return	in->parse_error(l[pos-1][0], err_codec_sym,
				l[pos-1]);
		if (!domain_sym.parse(in) || domain_sym.type != elem::SYM)
			return	in->parse_error(l[pos-1][0], err_domain_sym,
				l[pos-1]);
		if (!eval_sym.parse(in) || eval_sym.type != elem::SYM)
			return	in->parse_error(l[pos-1][0], err_eval_sym,
				l[pos-1]);
		if (!arity_num.parse(in) || arity_num.type != elem::NUM)
			return	in->parse_error(l[pos-1][0], err_arity_num,
				l[pos-1]);
		if (*l[pos++][0] != '.')
			return	in->parse_error(l[pos-1][0], dot_expected,
				l[pos-1]);
		return true;
	}
#endif
	if (l[pos] == "stdout") {
		type = STDOUT; ++pos;
		if (!t.parse(in, prog)) return
			in->parse_error(l[pos][0], err_stdout, l[pos]);
		if (*l[pos++][0] != '.') return
			in->parse_error(l[pos-1][0], dot_expected, l[pos-1]);
		return true;
	}
	if (!(l[pos] == "string")) return
		in->parse_error(l[pos][0], err_directive, l[pos]);
	++pos;
	if (!rel.parse(in) || rel.type != elem::SYM) return
		in->parse_error(l[pos-1][0], err_rel_expected, l[pos-1]);
	size_t curr2 = pos;
	if (*l[pos][0] == '<') {
		while (*l[pos++][0] != '>')
			if (!(pos < l.size())) return
				in->parse_error(l[curr2][1], err_fname);
		type = FNAME, arg = lexeme{ l[curr2][0], l[pos-1][1] };
	}
	else if (*l[pos][0] == '"' || *l[pos][0] == '`')
		type = STR, arg = l[pos++];
	else if (*l[pos][0] == '$')
		type=CMDLINE, ++pos, n = in->get_int_t(l[pos][0], l[pos][1]),
		++pos;
	else if (l[pos] == "stdin") type = STDIN;
	else if (t.parse(in, prog)) {
		type = TREE;
		if (*l[pos++][0]!='.') return
			in->parse_error(l[pos][0], dot_expected, l[pos]);
		return true;
	} else return in->parse_error(l[pos][0], err_directive_arg, l[pos]);
	if (*l[pos++][0]!='.') return
		in->parse_error(l[curr2][1], dot_expected, l[curr2]);
	return !in->error;
}

bool directive::operator==(const directive &b) const {
		if(type != b.type) return false;
		switch(type) {
			case directive::STR: return rel == b.rel && arg == b.arg;
			case directive::FNAME: return rel == b.rel && arg == b.arg;
			case directive::CMDLINE: return rel == b.rel && n == b.n;
			case directive::STDIN: return rel == b.rel;
			case directive::STDOUT: return t == b.t;
			case directive::TREE: return t == b.t;
			case directive::TRACE: return rel == b.rel;
			case directive::BWD: return true;
			case directive::EVAL: return eval_sym == b.eval_sym &&
				domain_sym == b.domain_sym && quote_sym == b.quote_sym &&
				timeout_num == b.timeout_num;
			case directive::QUOTE: return quote_sym == b.quote_sym &&
				domain_sym == b.domain_sym && quote_str == b.quote_str;
			case directive::EDOMAIN: return domain_sym == b.domain_sym &&
				limit_num == b.limit_num && arity_num == b.arity_num;
			case directive::CODEC: return codec_sym == b.codec_sym &&
				domain_sym == b.domain_sym && eval_sym == b.eval_sym &&
				arity_num == b.arity_num;
			case directive::INTERNAL: return internal_term == b.internal_term;
			default: return false;
		}
	}

elem::etype elem::peek(input* in) {
	size_t curr = in->pos;
	type = NONE;
	if (in->pos < in->l.size()) parse(in);
	in->pos = curr;
	return type;
}

bool elem::parse(input* in) {
	const lexemes& l = in->l;
	size_t& pos = in->pos;
	size_t chl;
	int_t i;
	if ('|' == *l[pos][0]) return e = l[pos++],type=ALT,   true;
	if ('(' == *l[pos][0]) return e = l[pos++],type=OPENP, true;
	if (')' == *l[pos][0]) return e = l[pos++],type=CLOSEP,true;
	if ('[' == *l[pos][0]) return e = l[pos++],type=OPENSB, true;
	if (']' == *l[pos][0]) return e = l[pos++],type=CLOSESB,true;
	if ('{' == *l[pos][0]) return e = l[pos++],type=OPENB, true;
	if ('}' == *l[pos][0]) return e = l[pos++],type=CLOSEB,true;
	// NEQ: should we check for any limits here?
	if ('!' == l[pos][0][0] && '=' == l[pos][0][1])
		return e = l[pos++], type = NEQ, true;
	if ('-' == l[pos][0][0] && '>' == l[pos][0][1])
		return e = l[pos++], type = IMPLIES, true;
	if ('<' == l[pos][0][0] && '-' == l[pos][0][1] && '>' == l[pos][0][2])
		return e = l[pos++], type = COIMPLIES, true;
	if (('<' == l[pos][0][0])  && !('<' == l[pos][0][1]))
		return	('=' == l[pos][0][1] ? (e = l[pos++], type = LEQ) :
			(e = l[pos++], type = LT)), true;
	if ('>' == l[pos][0][0] && !('>' == l[pos][0][1]))
		return	(('=' == l[pos][0][1]) ? (e = l[pos++], type = GEQ) :
			(e = l[pos++], type = GT)), true;
	if ('=' == l[pos][0][0])
		return	pos + 1 < l.size() && '>' == l[pos+1][0][0] ? false :
			(e = l[pos++], type = EQ, true);
	if (('|' == l[pos][0][0]) && ('|' == l[pos][0][1]))
		return e = l[pos++], type = OR, true;
	if (('&' == l[pos][0][0]) && ('&' == l[pos][0][1]))
		return e = l[pos++], type = AND, true;
	if ('+' == l[pos][0][0])
		return e = l[pos++], type = ARITH, arith_op = ADD, true;
	if ('-' == l[pos][0][0])
		return e = l[pos++], type = ARITH, arith_op = SUB, true;
	if ('*' == l[pos][0][0])
		return e = l[pos++], type = ARITH, arith_op = MULT, true;

	//FIXME conflicting with ALT
	if ('|' == l[pos][0][0])
		return e = l[pos++], type = ARITH, arith_op = BITWOR, true;
	if ('&' == l[pos][0][0])
		return e = l[pos++], type = ARITH, arith_op = BITWAND, true;
	if ('^' == l[pos][0][0])
		return e = l[pos++], type = ARITH, arith_op = BITWXOR, true;
	if ('>' == l[pos][0][0] && '>' == l[pos][0][1])
		return e = l[pos++], type = ARITH, arith_op = SHR, true;
	if ('<' == l[pos][0][0] && '<' == l[pos][0][1])
		return e = l[pos++], type = ARITH, arith_op = SHL, true;

	if (!is_alnum(l[pos][0], l[pos][1]-l[pos][0], chl) && *l[pos][0]!='_' &&
		!strchr("\"`'?", *l[pos][0])) return false;
	if (e = l[pos], *l[pos][0] == '\'') {
		type = CHR;
		if (l[pos][0][1] == '\'') ch = 0;
		else if (l[pos][0][1] == '\\') switch (l[pos][0][2]) {
			case 'r': ch = U'\r'; break;
			case 'n': ch = U'\n'; break;
			case 't': ch = U'\t'; break;
			case '\\':ch = U'\\'; break;
			case '\'':ch = U'\''; break;
			case 'x': if ((l[pos][0] + 6 != l[pos][1]) ||
				((i = hex_to_int_t(l[pos][0]+3, 2)) < 0))
			 		return in->parse_error(l[pos][0] + 4,
						err_x_escape, l[pos]);
				  ch = (char32_t) i; break;
			case 'u': if ((l[pos][0] + 8 != l[pos][1]) ||
				((i = hex_to_int_t(l[pos][0]+3, 4)) < 0))
					return in->parse_error(l[pos][0] + 4,
						err_u_escape, l[pos]);
				  ch = (char32_t) i; break;
			default: { DBGFAIL; }
		}
		else chl = peek_codepoint(l[pos][0]+1,l[pos][1]-l[pos][0]-2,ch);
	}
	else if (*l[pos][0] == '?') type = VAR;
	else if (is_alpha(l[pos][0], l[pos][1]-l[pos][0], chl) ||
		*l[pos][0] == '_')
	{
		size_t len = l[pos][1]-l[pos][0];
		if( len == 6 && !strncmp(l[pos][0], "forall", len ))
			type = FORALL;
		else if ( len == 6 && !strncmp(l[pos][0], "exists", len ) )
			type = EXISTS;
		else if ( len == 6 && !strncmp(l[pos][0], "unique", len ) )
			type = UNIQUE;
		else if ((len == 5 && !strncmp(l[pos][0], "renew",  len )) ||
			 (len == 6 && !strncmp(l[pos][0], "forget", len )))
			type = BLTINMOD;
		else type = SYM;
	}
	else if (*l[pos][0] == '"' || *l[pos][0] == '`') type = STR;
	else type = NUM, num = in->get_int_t(l[pos][0], l[pos][1]);
	return ++pos, !in->error;
}

bool raw_term::parse(input* in, const raw_prog& prog, bool is_form,
	raw_term::rtextype pref_type) {
	const lexemes& l = in->l;
	size_t& pos = in->pos;
	const lexeme &s = l[pos];
	size_t curr = pos;
	if (s == "__fp__") require_fp_step = true;
	if ((neg = *l[pos][0] == '~')) ++pos;
	bool noteq = false, eq = false, leq = false, gt = false,
		lt = false, geq = false, bltin = false, arith = false,
		forget = false, renew = false;

	t_arith_op arith_op_aux = NOP;
	while ((!strchr(".:,;{}|&",*l[pos][0]) && !is_form &&  !(l[pos]=="else")) ||
			(!strchr(".:,;{}|&-<", *l[pos][0]) && is_form)) {
		if (e.emplace_back(), !e.back().parse(in)) return false;
		else if (pos == l.size()) return
			in->parse_error(l[pos-1][1], err_eof, s[0]);
		elem& el = e.back(); // TODO: , el = e.back(), !el.parse(l, pos)
		switch (el.type) {
			case elem::EQ:     eq = true; break;
			case elem::NEQ: noteq = true; break;
			case elem::LEQ: leq   = true; break;
			case elem::GT:  gt    = true; break;
			case elem::LT:  lt    = true; break;
			case elem::GEQ: geq   = true; break;
			case elem::BLTINMOD:
				if      (el.e == "forget") forget = true;
				else if (el.e == "renew")  renew = true;
				break;
			case elem::SYM:	if (prog.dict.is_bltin(el.e)) {
					el.type = elem::BLTIN;
					bltin = true;
					el.num = renew << 1 | forget;
					if (el.num) e.erase(remove_if(e.begin(),
						e.end(), [] (const elem& el) {
							return el.type ==
								elem::BLTINMOD;
						}), e.end()); // del modifiers
				}
				break;
			case elem::ARITH: arith = true; arith_op_aux = e.back().arith_op; break;
			default: break;
		}
	}
	if (e.empty()) return false;

	if (e.size() == 1 && e[0].type == elem::VAR) {
		extype = rtextype::VAR;
		return true;
	}

	// TODO: provide specific error messages. Also, something better to group?

	// make 'forget' work as a builtin as well and not just a builtin modifier
	if (forget) bltin = true, e[0].type = elem::BLTIN;

	if (pref_type == rtextype::CONSTRAINT)  {
		extype = rtextype::CONSTRAINT;
		return true;
	}

	if (bltin) {
		// similar as for SYM below (join?) but this format will expand.
		if (e[0].type != elem::BLTIN) return
			in->parse_error(l[pos][0], err_builtin_expected, l[pos]);
		extype = raw_term::BLTIN; // isbltin = true;
		return calc_arity(in);
	}
	if ((noteq || eq) && !arith) {
		if (e.size() < 3) return
			in->parse_error(l[pos][0], err_3_els_expected, l[pos]);
		// only supporting smth != smthelse (3-parts) and negation in front ().
		if (e[1].type != elem::NEQ && e[1].type != elem::EQ) return
			in->parse_error(l[pos][0], err_eq_expected, l[pos]);
		if (noteq)
			neg = !neg; // flip the neg as we have NEQ, don't do it for EQ ofc
		extype = raw_term::EQ; // iseq = true;
		return calc_arity(in);
	}
	if ((leq || gt) && !arith) {
		if (e.size() < 3) return
			in->parse_error(l[pos][0], err_3_els_expected, l[pos]);
		// only supporting smth != smthelse (3-parts) and negation in front ().
		if (e[1].type != elem::LEQ && e[1].type != elem::GT) return
			in->parse_error(l[pos][0], err_leq_expected, l[pos]);
		if (gt) neg = !neg;
		extype = raw_term::LEQ; // isleq = true;
		return calc_arity(in);
	}
	if (lt || geq) {
		if (e.size() < 3) return
			in->parse_error(l[pos][0], err_3_els_expected, l[pos]);
		// only supporting smth != smthelse (3-parts) and negation in front ().
		if (e[1].type != elem::LT && e[1].type != elem::GEQ) return
			in->parse_error(l[pos][0], err_leq_expected, l[pos]);
		// GEQ <==> LEQ + reverse args + !neg
		swap(e[2], e[0]); // e = { e[2], e[1], e[0] };
		if (lt) neg = !neg;
		extype = raw_term::LEQ;
		return calc_arity(in);
	}
	if (arith) {
		// ARITH operations are currently implemented to work with three arguments
		// var OPERATOR var RELATIONSHIP var
		// supported OPERATORs : + * | & ^ << >> (XXX - is TBD)
		// supported RELATIONSHIPs: = (TODO: add support for <= => < > != )
		// TODO: improve checks here
		if (e.size() < 4)
			return	in->parse_error(l[pos][0], err_term_or_dot,
				l[pos]);
		if (e[1].type != elem::ARITH || e[3].type != elem::EQ)
			return	in->parse_error(l[pos][0], err_term_or_dot,
				l[pos]);
		//iseq = true;
		neg = false;
		arith_op = arith_op_aux;
		extype = raw_term::ARITH;
		//return calc_arity(in), true;
		return true;
	}

	if (e[0].type != elem::SYM)
		return in->parse_error(l[curr][0], err_relsym_expected,l[curr]);
	if (e.size() == 1) return calc_arity(in), true;
	if (e[1].type != elem::OPENP)
		return in->parse_error(l[pos][0], err_paren_expected, l[pos]);
	if (e.back().type != elem::CLOSEP)
		return in->parse_error(e.back().e[0], err_paren, l[pos]);
	return calc_arity(in);
}

void raw_term::add_parenthesis() {
	elem o = elem(elem::OPENP), c = elem(elem::CLOSEP);
	e.insert(e.begin() + 1, o), e.push_back(c);
	for (size_t n = 0, k = 2; n != arity.size(); ++n)
		if (arity[n] == -1) e.insert(e.begin() + k++, o);
		else if (arity[n] == -2) e.insert(e.begin() + k++, c);
		else k += arity[n];
}

bool raw_term::calc_arity(input* in) {
	size_t dep = 0;
	arity = {0};
	//XXX: are we comparing over an enum?
	if (extype > raw_term::REL && extype < raw_term::BLTIN)
		return arity = { 2 }, true;
	if (e.size() == 1) return true;
	for (size_t n = 2; n < e.size()-1; ++n)
		if (e[n].type == elem::OPENP) ++dep, arity.push_back(-1);
		else if (e[n].type != elem::CLOSEP) {
			if (arity.back() < 0) arity.push_back(1);
			else ++arity.back();
		} else if (!dep--)
			return in->parse_error(e[n].e[0], err_paren, e[n].e);
		else arity.push_back(-2);
	if (dep) return in->parse_error(e[0].e[0], err_paren, e[0].e);
	return true;
}

/* Returns the arity of the raw_term; That is the arity excluding parenthesis.
 * In particular if extype = raw_term::REL, it returns
 * the mathematical arity of the relation. */

int_t raw_term::get_formal_arity() const {
	int_t one_arity = 0;
	for (const int_t& i : arity) {
		if (i == -1 || i == -2) continue;
		else one_arity+=i;
	} return one_arity;
}

bool macro::parse(input* in, const raw_prog& prog){
	const lexemes& l = in->l;
	size_t& pos = in->pos;	size_t curr = pos;
	elem e;
	if(	!this->def.parse(in,prog) ||
		pos >= l.size() ||
		l[pos][0][0] != ':' ||
		l[pos][0][1] != '=' )
		goto fail;

	++pos;
	for (b.emplace_back(); b.back().parse(in, prog);
		b.emplace_back(), ++pos) {
		if (*l[pos][0] == '.') return ++pos, true;
		else if (*l[pos][0] != ',') break;
	}

	fail: return pos = curr , false;
}

/* Makes a tree representing the given non-empty conjunction. Otherwise
 * return nullopt. */

optional<raw_form_tree> conj_to_tree(vector<raw_term> conj) {
	if(conj.empty()) return nullopt;
	raw_form_tree tree(conj[0]);
	for(size_t i = 1; i < conj.size(); i++)
		tree = raw_form_tree(elem::AND,
				make_shared<raw_form_tree>(tree),
				make_shared<raw_form_tree>(conj[i]));
	return tree;
}

/* Return the stored formula tree or one equivalent to the body.
 * Otherwise return nullopt. */

optional<raw_form_tree> raw_rule::get_prft() const {
	if(prft || b.empty()) return prft;
	else {
		raw_form_tree disj = *conj_to_tree(b[0]);
		for(size_t i = 1; i < b.size(); i++)
			disj = raw_form_tree(elem::ALT, make_shared<raw_form_tree>(disj),
				make_shared<raw_form_tree>(*conj_to_tree(b[i])));
		return disj;
	}
}

/* Switch the representation of this rule from DNF vectors to equivalent
 * tree .*/

raw_rule raw_rule::try_as_prft() const {
	raw_rule copy = *this;
	if(!prft && !b.empty()) copy.set_prft(*get_prft());
	return copy;
}

/* Return the stored DNF or one equivalent to the formula tree. If
 * neither is possible then return nullopt. */

optional<vector<vector<raw_term>>> raw_rule::get_b() const {
	if(!b.empty() || !prft) return b;
	else {
		vector<vector<raw_term>> disjuncts;
		// Iterate through disjuncts of the given formula
		for(const raw_form_tree *disj : prft->flatten_associative(elem::ALT)) {
			vector<raw_term> conjuncts;
			// Iterate through the conjunctions of the current disjunct
			for(const raw_form_tree *conj : disj->flatten_associative(elem::AND)) {
				bool sign = true;
				// Figure out the effective sign of the current conjunct
				for(; conj->type == elem::NOT; conj = &*conj->l, sign = !sign);
				// Note the term at this position. If this is not possible then
				// the tree does not represent a DNF.
				if(conj->type == elem::NONE) {
					raw_term tm = *conj->rt;
					tm.neg = !sign;
					conjuncts.push_back(tm);
				} else return std::nullopt;
			}
			disjuncts.push_back(conjuncts);
		}
		return disjuncts;
	}
}

/* Switch the representation of this rule from a tree to equivalent
 * DNF vectors.*/

raw_rule raw_rule::try_as_b() const {
	raw_rule copy = *this;
	if(b.empty() && prft) {
		const optional<vector<vector<raw_term>>> &ob = get_b();
		if(ob) copy.set_b(*ob);
	}
	return copy;
}

bool raw_rule::parse(input* in, const raw_prog& prog) {
	const lexemes& l = in->l;
	size_t& pos = in->pos;	size_t curr = pos;
	if (*l[pos][0] == '!') {
		if (*l[++pos][0] == '!') ++pos, type = TREE;
		else type = GOAL;
	}
head:	h.emplace_back();
	if (!h.back().parse(in, prog)) return pos = curr, false;
	if (l[pos] == "else") return true;
	if (*l[pos][0] == '.') return ++pos, true;
	if (*l[pos][0] == ',') { ++pos; goto head; }
	if (*l[pos][0] != ':' || (l[pos][0][1] != '-' && l[pos][0][1] != '=' ))
		return in->parse_error(l[pos][0], err_head, l[pos]);

	++pos;

	//XXX: workaround to use ":-" both for standard rules and formulas
	//     syntax revision for formula may be required
	bool is_form = false;
	//TODO: check for fault
	for (size_t x = pos; x != l.size() && l[x][0][0] != '.'; x++) {
		if (l[x] == "forall" || l[x] == "exists" || l[x] == "unique" ||
			l[x] == "&&" || l[x] == "||" || l[x] == "|") {
			is_form = true; break;
		}
	}

	if(is_form) {
		raw_sof rsof(prog);
		sprawformtree root = NULL;
		bool ret = rsof.parse(in, root);
		sprawformtree temp(root);
		if(temp) this->prft = *temp;
		if(ret) return true;
		return in->parse_error(l[pos][0], "Formula has errors", l[pos]);
	} else {
		b.emplace_back();
		for (b.back().emplace_back(); b.back().back().parse(in, prog);
			b.back().emplace_back(), ++pos) {
			if (*l[pos][0] == '.') return ++pos, true;
			else if (*l[pos][0] == L';') b.emplace_back();
			else if (*l[pos][0] != ',') return
				in->parse_error(l[pos][0], err_term_or_dot,l[pos]);
		}
		return in->error ? false
			: in->parse_error(l[pos][0], err_body, l[pos]);
	}

	return false;
}

bool raw_prefix::parse(input* in) {
	size_t curr = in->pos;
	isfod = false;
	if (!qtype.parse(in)) return false;
	if (qtype.type != elem::FORALL &&
		qtype.type != elem::EXISTS &&
		qtype.type != elem::UNIQUE)
			return in->pos = curr, false;
	if (*in->l[in->pos][0] == '?') isfod = true;
	if (!ident.parse(in)) return false;
	if (ident.type != elem::VAR && ident.type != elem::SYM)
		return in->pos = curr, false;
	return true;
}

bool raw_sof::parsematrix(input* in, sprawformtree &matroot) {
	const lexemes& l = in->l;
	size_t& pos = in->pos;
	size_t curr = pos;
	sprawformtree root = NULL;
	bool isneg = false;

	if (pos == l.size()) return false;
	while (*l[pos][0] == '~') isneg = !isneg, ++pos;
	if (pos != l.size() && *l[pos][0] == '{') {
		++pos;
		if( ! parseform(in, root, 0) ) goto Cleanup;
		if( isneg)
			root = std::make_shared<raw_form_tree>(elem::NOT, root);

		if( pos == l.size() && *l[pos][0] != '}') goto Cleanup;
		++pos;

		matroot = root;
		return true;
	}
	else {
		elem next;
		next.peek(in);

		if(next.type == elem::SYM || next.type == elem::NUM) {
			raw_term tm;
			if( !tm.parse(in, prog, next.type == elem::SYM)) goto Cleanup;
			root = std::make_shared<raw_form_tree>(tm);
			if( isneg ) root = std::make_shared<raw_form_tree>(elem::NOT, root);
			matroot = root;
			return true;
		}
		//XXX: Constraints, by now using && in the form matrix
		else if(next.type == elem::VAR) {
			raw_term tm;
			if( !tm.parse(in, prog, false)) goto Cleanup;
			root = std::make_shared<raw_form_tree>(tm);
			if( isneg ) root = std::make_shared<raw_form_tree>(elem::NOT, root);
			matroot = root;
			return true;
		} else {
			sprawformtree cur = NULL;
			while(next.type == elem::FORALL ||
				next.type == elem::UNIQUE ||
				next.type == elem::EXISTS )
			{
				raw_prefix rpfx;

				if( !rpfx.parse(in) ) goto Cleanup;

				if(!cur) root = cur = std::make_shared<raw_form_tree>(rpfx.qtype);
				else cur->r = std::make_shared<raw_form_tree>(rpfx.qtype),
					cur = cur->r;
				cur->l = std::make_shared<raw_form_tree>(rpfx.ident);
				next.peek(in);
			}

			if (cur == NULL || pos == l.size() || *l[pos][0] != '{')
				goto Cleanup;

			++pos;
			if (!parseform(in, cur->r, 0)) goto Cleanup;

			if (pos == l.size() || *l[pos][0] != '}') goto Cleanup;

			++pos;
			if (isneg) root = std::make_shared<raw_form_tree>(elem::NOT, root);

			matroot = root;
			return true;
		}
	}

	Cleanup:
	//if(root) delete root;
	matroot = root;
	return pos=curr, false;
}

bool raw_sof::parseform(input* in, sprawformtree &froot, int_t prec ) {

	size_t curr = in->pos;
	sprawformtree root = NULL;
	sprawformtree cur = NULL;

	bool ret = parsematrix(in, root);
	elem nxt;
	if ( !ret ) goto Cleanup;

	nxt.peek(in);
	while (prec <=1 &&
		(nxt.type == elem::IMPLIES || nxt.type == elem::COIMPLIES))
	{
		nxt.parse(in);
		cur = std::make_shared<raw_form_tree>(nxt, root);
		root = cur;
		if (!parseform(in, root->r, 2)) goto Cleanup ;
		nxt.peek(in);
	}

	nxt.peek(in);
	while( prec <= 0 && (nxt.type == elem::AND || nxt.type == elem::ALT) ) {
		nxt.parse(in);
		cur = std::make_shared<raw_form_tree>(nxt, root);
		root = cur;
		if (!parseform(in, root->r, 1) ) goto Cleanup;
		nxt.peek(in);
	}
	froot = root;
	return true;

	Cleanup:
	//if(root) delete root;
	froot = root;
	return in->pos=curr, false;
}

/* Populates root argument by creeating a binary tree of formula.
	It is caller's responsibility to manage the memory of root. If the parse function,
	returns false or the root is not needed any more, the caller should delete the root pointer.
	*/
bool raw_sof::parse(input* in, sprawformtree &root) {

	root = NULL;
	bool ret = parseform(in, root );

	if (!(in->l[in->pos] == "then" || in->l[in->pos] == "do")) {
		if (in->pos >= in->l.size() || *in->l[in->pos][0] != '.')
			ret = false;
		else in->pos++;
	}

	//DBG(COUT << "\n cur = " << in->pos << " tot= " << in->l.size() << " \n ";)
	//DBG(root->printTree());
	return ret;
}

void raw_form_tree::printTree( int level) const {
	if( r ) r->printTree(level + 1)	;
	COUT << '\n';
	for(int i = 0; i < level; i++) COUT << '\t';
	(this->rt)?	COUT<<*rt : (this->el)? COUT << *el : (this->type) == elem::NOT ? COUT <<"not" : COUT << "";
	if (l) l->printTree(level + 1);
}

bool production::parse(input *in, const raw_prog& prog) {
	const lexemes& l = in->l;
	size_t& pos = in->pos;
	size_t curr2, curr = pos;
	elem e;
	if (!e.parse(in) || l.size() <= pos+1) goto fail;
/*	if (*l[pos++][0] == '<') {
		if (l[pos++][0][0] != '=') goto fail;
		start = true;
		if (!t.parse(l, pos)) parse_error(err_start_sym, l[pos]);
		if (*l[pos++][0] != '.') parse_error(dot_expected, l[pos]);
		return true;
	}*/
	if (*l[pos++][0] != '=' || l[pos++][0][0] != '>') goto fail;
	curr2 = pos;
	for (p.push_back(e);;) {
		elem e;
		if (pos == l.size()) break;
		if (*l[pos][0] == '.') return ++pos, true;
		if (*l[pos][0] == ',') {

			if(p.size() < 2 ) goto fail;  // prod rhs atleast one non-terminal

			for (;*l[pos][0] == L','; ) {
				++pos;
				raw_term rt;
				if (!rt.parse(in, prog, 0,raw_term::CONSTRAINT))
					goto fail;
				c.push_back(rt);
			}
			if (*l[pos][0] != '.') goto fail;
			return ++pos, true;
		}
		if (!e.parse(in)) goto fail;
		p.push_back(e);
	}
	in->parse_error(l[curr2][0], err_prod, l[curr2]);
fail:	return pos = curr, false;
}

bool guard_statement::parse_condition(input* in, raw_prog& np) {
	sprawformtree root = 0;
	raw_sof rsof(np);
	bool ret = rsof.parse(in, root);
	if(root) prft = *root;
	rp_id = np.id;
	return ret ? true : in->parse_error(in->l[in->pos][0],
		"Formula has errors", in->l[in->pos]);
}

bool guard_statement::parse_if(input* in, dict_t &dict, raw_prog& rp) {
	lexemes& l  = in->l;
	size_t& pos = in->pos;
	if (!(l[pos] == "if")) return false;
	++pos, type = IF;
	if (!parse_condition(in, rp)) return false;
	if (!(l[pos] == "then")) return in->parse_error(l[pos][0],
		"'then' expected.", l[pos]);
	raw_prog t_p(dict);
	++pos;
	if (!t_p.parse_nested(in) && !in->error) {
		t_p.id = ++raw_prog::last_id;
		if (!t_p.r.emplace_back().parse(in, t_p))
			return --raw_prog::last_id, false;
		t_p.r.back().update_states(t_p.has);
	}
	t_p.guarded_by = rp.id;
	true_rp_id = t_p.id;
	rp.nps.push_back(t_p);
	if (pos != l.size() && l[pos] == "else") {
		raw_prog f_p(dict);
		++pos;
		if (!f_p.parse_nested(in) && !in->error) {
			f_p.id = ++raw_prog::last_id;
			if (!f_p.r.emplace_back().parse(in, f_p))
				return --raw_prog::last_id, false;
			f_p.r.back().update_states(f_p.has);
		}
		f_p.guarded_by = rp.id;
		f_p.true_rp_id = true_rp_id;
		false_rp_id = f_p.id;
		rp.nps.push_back(f_p);
	}
	return true;
}

bool guard_statement::parse_while(input* in, dict_t &dict, raw_prog& rp) {
	lexemes& l = in->l;
	size_t& pos = in->pos;
	if (!(l[pos] == "while")) return false;
	++pos, type = WHILE;
	if (!parse_condition(in, rp)) return false;
	if (!(l[pos] == "do")) return in->parse_error(l[pos][0],
		"'do' expected.", l[pos]);
	++pos;
	raw_prog l_p(dict);
	if (!l_p.parse_nested(in) && !in->error) {
		l_p.id = ++raw_prog::last_id;
		if (!l_p.r.emplace_back().parse(in, l_p))
			return --raw_prog::last_id, false;
	}
	rp_id = l_p.id;
	rp.nps.push_back(l_p);
	p_break_rp = &(rp.nps.back());
	return true;
}

bool guard_statement::parse(input* in, dict_t &dict, raw_prog& rp) {
	return parse_if(in, dict, rp) || parse_while(in, dict, rp);
}

bool state_block::parse(input* in) {
	lexemes& l = in->l;
	size_t& pos = in->pos;
	size_t bpos = pos;
	if (*l[pos][0] != '[' || ++pos >= l.size()) return false;
	label = l[pos];
	if (++pos >= l.size()) return false;
	if (*l[pos][0] == '~') ++pos, flip = true;
	if (pos >= l.size() || *l[pos][0] != ':' || ++pos >= l.size())
		return false;
	while (*l[pos][0] != ']' && pos < l.size()) {
		if (!p.parse(in)) return false;
		if (p.nps.size()) return in->parse_error(l[bpos][0], "programs cannot be nested inside a state block",
			l[bpos]);
	}
	if (*l[pos][0] == ']') return ++pos, true;
	else return false;
}

bool raw_prog::parse_xfp(input* in) {
	lexemes& l = in->l;
	size_t& pos = in->pos;
	if (*l[pos][0] != '{') return false;
	++pos;
	if (!parse(in)) return in->error ? false :
		in->parse_error(l[pos][0], err_parse, l[pos]);
	if (pos == l.size() || *l[pos++][0] != '}') return in->error ? false
		: in->parse_error(l[pos-1][1], err_close_curly, l[pos-1]);
	return true;
}

bool raw_prog::parse_statement(input* in) {
	directive x;
	raw_rule y;
	production p;
	macro m;
	guard_statement c;
	typestmt ts;
	raw_prog np(dict);
	state_block sb(dict);
	//COUT << "\tparsing statement " << in->l[in->pos] << endl;
	if (sb.parse(in)) sbs.push_back(sb);
	else if (!in->error && ts.parse(in, *this)) vts.push_back(ts);
	else if (!in->error && np.parse_nested(in)) nps.push_back(np);
	else if (!in->error && c.parse(in, dict, *this)) {
		if (c.type == guard_statement::IF) has[COND] = true;
		else c.p_break_rp->has[CURR] = true;
		gs.push_back(c);
	}
	else if (!in->error && m.parse(in, *this)) macros.emplace_back(m);
	else if (!in->error && x.parse(in, *this)) d.push_back(x);
	else if (!in->error && y.parse(in, *this))
		y.update_states(has), r.push_back(y);
	else if (!in->error && p.parse(in, *this)) g.push_back(p);
	else return false;
	if (!require_guards && gs.size()) require_guards = true;
	if (!require_state_blocks && sbs.size()) require_state_blocks = true;
	return !in->error;
}

bool raw_prog::parse_nested(input* in) {
	lexemes& l = in->l;
	size_t& pos = in->pos;
	type = PFP;
	if (*l[pos][0] != '{') {
		if      (l[pos] == "lfp") ++pos, type = LFP;
		else if (l[pos] == "gfp") ++pos, type = GFP;
		else if (l[pos] == "pfp") ++pos;
		else return false;
	}
	if (pos >= l.size() || *l[pos][0] != '{') return in->parse_error(
		l[pos][0], "unexpected end of nested", l[pos]);
	return parse_xfp(in);
}

bool raw_prog::parse(input* in) {
	// BLTINS: insert builtins from dict
	for (size_t n = 0; n != dict.nbltins(); ++n)
		dict.get_bltin(n);
	id = ++last_id;
	while (in->pos < in->l.size() &&
			*in->l[in->pos][0] != '}' &&
			*in->l[in->pos][0] != ']')
		if (!parse_statement(in)) return --last_id, false;
	//COUT << "\t\tparsed rp statements:\n" << *this << endl;

	if (macros.empty()) return true;

	for(raw_rule &rr : r)
		for (vector<raw_term> &vrt : rr.b)
			for (size_t i = 0; i != vrt.size(); i++)
				for (macro &mm : macros)
					for(size_t j = 0; j < vrt[i].e.size(); j++)
						if( vrt[i].e[j].e == mm.def.e[0].e ) {
							if( !macro_expand(in, mm, i, j, vrt))
								return --last_id, false;
							else break;
						}
	return true;
}
environment& raw_prog::get_typenv() {
	return *typenv;
}
void raw_prog::set_typenv( const environment &e ) {
	*typenv = e;
}

raw_prog::raw_prog(dict_t &dict_) : dict(dict_) {
	//TODO: review pointer here
	typenv = std::make_shared<environment>();
}

bool raw_prog::macro_expand(input *in, macro mm, const size_t i, const size_t j,
						vector<raw_term> &vrt) {

	std::map<elem, elem> chng;
	vector<elem>::iterator et = vrt[i].e.begin()+j;
	vector<elem>::iterator ed = mm.def.e.begin();

	if( vrt[i].e.size() == mm.def.e.size()  && j == 0)  {// normal macro
		for( ++et, ++ed; et!=vrt[i].e.end() && ed!=mm.def.e.end(); 	et++, ed++)
			if( (et->type == elem::VAR || et->type == elem::NUM ||
				et->type == elem::CHR || et->type == elem::SYM || et->type == elem::STR)
				&& ed->type == elem::VAR)
				chng[*ed] = *et;

		for ( auto &tt:mm.b )
			for(  auto tochng = tt.e.begin(); tochng!=tt.e.end(); tochng++ )
				if( tochng->type == elem::VAR &&  (chng.find(*tochng)!= chng.end()))
					*tochng = chng[*tochng];

		vrt.erase(i+vrt.begin());
		vrt.insert(i+vrt.begin(), mm.b.begin(), mm.b.end());
		return true;

	} else if( j > 0)  {// create fresh var and unary case
		vector<elem> carg;
		for( ; et != vrt[i].e.end() && et->type != elem::CLOSEP; et++)
			if(	et->type == elem::VAR ) carg.emplace_back(*et);
		if(carg.size() == 0 )
			return in->parse_error(vrt[i].e[0].e[0],"Missing arg in macro call",vrt[i].e[0].e),
			false;

		elem ret;
		for( size_t a = 0 ; ed!=mm.def.e.end(); ed++) {
			if(ed->type == elem::VAR)  {
				if(a < carg.size())
					chng[*ed] = carg[a++];
				else
					chng[*ed] = elem(elem::VAR, dict.get_var_lexeme(dict.get_fresh_var())),
					ret = chng[*ed];
			}
		}
		for( auto &tt:mm.b )
			for(  auto tochng = tt.e.begin(); tochng!=tt.e.end(); tochng++ )
				if( tochng->type == elem::VAR &&  (chng.find(*tochng)!= chng.end()))
					*tochng = chng[*tochng];
		// TODO
		DBG(o::dbg()<<carg.size();)
		vrt[i].e.erase(vrt[i].e.begin()+j, vrt[i].e.begin()+j+1+carg.size()+2);
		vrt[i].e.insert(vrt[i].e.begin()+2, ret);
		vrt[i].calc_arity(in);
		vrt.insert(i+vrt.begin()+1, mm.b.begin(), mm.b.end());
		return true;
	}
	else return in->parse_error(vrt[i].e[0].e[0],"Error macro call",vrt[i].e[0].e),
			false;
}

bool raw_progs::parse(input* in, dict_t& dict) {
	if (!in->data()) return true;
	lexemes& l = in->l;
	size_t& pos = in->pos;
	in->prog_lex();
	if (in->error) return false;
	if (!l.size()) return true;
	raw_prog rp(dict); //raw_prog& rp = p.nps.emplace_back(raw_prog(dict));
	raw_prog::require_guards = false;
	raw_prog::require_state_blocks = false;
	if (!rp.parse(in))  return in->error?false:
		in->parse_error(l[pos][0],
			err_rule_dir_prod_expected, l[pos]);
	
	//FIXME: guards needs ROOT_EMPTY
 	p.nps.push_back(rp);
	return true;
}

/* Compare lexemes by their character content rather than by memory
 * locations. */

bool operator==(const lexeme& x, const lexeme& y) {
	return x[1] - x[0] == y[1] - y[0] && !strncmp(x[0], y[0], x[1] - x[0]);
}

bool less<lexeme>::operator()(const lexeme& m, const lexeme &n) const {
	return lexeme2str(m) < lexeme2str(n);
}

bool operator<(const lexeme& m, const lexeme &n) {
	return less<lexeme>()(m, n);
}

size_t hash<lexeme>::operator()(const lexeme& m) const {
	string_t str = lexeme2str(m);
	return hash<string>()(string(str.begin(), str.end()));
}

/* Compare signatures in a manner that treats their identifier as a
 * string rather than a pair of memory locations. */

bool operator==(const signature& m, const signature &n) {
	return m.first == n.first && m.second == n.second;
}

bool less<signature>::operator()(const signature& m, const signature &n) const {
	return less<lexeme>()(m.first, n.first) ||
		(equal_to<lexeme>()(m.first, n.first) &&
		less<ints>()(m.second, n.second));
}

bool operator<(const signature& m, const signature &n) {
	return less<signature>()(m, n);
}

bool operator<(const raw_term& x, const raw_term& y) {
	if (x.neg != y.neg) return x.neg < y.neg;
	if (x.extype != y.extype) return x.extype < y.extype;
	//if (x.iseq != y.iseq) return x.iseq < y.iseq;
	//if (x.isleq != y.isleq) return x.isleq < y.isleq;
	//if (x.islt != y.islt) return x.islt < y.islt;
	//if (x.isarith != y.isarith) return x.isarith < y.isarith;
	if (x.e != y.e) return x.e < y.e;
	if (x.arity != y.arity) return x.arity < y.arity;
	return false;
}

//bool operator==(const raw_term& x, const raw_term& y) {
//	return x.neg == y.neg && x.e == y.e && x.arity == y.arity;
//}

bool operator<(const raw_rule& x, const raw_rule& y) {
	if (x.h != y.h) return x.h < y.h;
	else if (x.is_form() != y.is_form()) return x.is_form() < y.is_form();
	else if (x.is_form()) return *x.prft < *y.prft;
	else return x.b < y.b;
/*	if (x.h.size() != y.h.size())
		return x.heads().size() < y.heads().size();
	if (x.bodies().size() != y.bodies().size())
		return x.bodies().size() < y.bodies().size();
	for (size_t n = 0; n != x.h.size(); ++n)
		if (!(x.head(n) == y.h[n])) return x.head(n) < y.head(n);
	for (size_t n = 0; n != x.bodies().size(); ++n)
		if (!(x.body(n) == y.body(n))) return x.body(n) < y.body(n);*/
}

bool operator==(const lexeme& l, const string& s) {
	if ((size_t) (l[1] - l[0]) != s.size()) return false;
	return !strncmp(l[0], s.c_str(), l[1] - l[0]);
}

bool operator==(const lexeme& l, const char* s) {
	size_t n = strlen(s);
	return (size_t) (l[1] - l[0]) != n
		? false : !strncmp(l[0], s, n);
}

bool lexcmp::operator()(const lexeme& x, const lexeme& y) const {
	//COUT<<""
	//	<< "\tx: \t"<<&x[0]<<" - "<<&x[1]<<"\n"
	//	<< "\ty: \t"<<&y[0]<<" - "<<&y[1]<<"\n";
	if (x[1]-x[0] != y[1]-y[0]) return x[1]-x[0] < y[1]-y[0];
	for (size_t n = 0; n != (size_t)(x[1]-x[0]); ++n)
		if (x[0][n] != y[0][n]) return x[0][n] < y[0][n];
	return false;
	// the following causes valgrind to complain about __STRNCMP_avx2:
//	return	x[1]-x[0] != y[1]-y[0] ? x[1]-x[0] < y[1]-y[0]
//		: (STRNCMP(x[0], y[0], x[1]-x[0]) < 0);
}

bool operator==(const vector<raw_term>& x, const vector<raw_term>& y){
	if (x.size() != y.size()) return false;
	for (size_t n = 0; n != x.size(); ++n) if (!(x[n]==y[n])) return false;
	return true;
}

off_t fsize(const char *fname) {
	struct stat s;
	return stat(fname, &s) ? 0 : s.st_size;
}

off_t fsize(ccs s, size_t len) {
	return fsize(to_string(string_t(s, len)).c_str());
}

string input::file_read(string fname) {
	ifstream s(fname);
	stringstream ss;
	return (ss << s.rdbuf()), ss.str();
}

string input::file_read_text(::FILE *f) {
	stringstream ss;
	char buf[32];
	int_t c, n, l;
	bool skip = false;
	*buf = 0;
next:	for (n = l = 0; n != 31; ++n)
		if (EOF == (c = getc(f))) { skip = 0; break; }
//		else if (c == '#') skip = 1;
		else if (c == '\r' || c == '\n') skip = 0, buf[l++] = c;
		else if (!skip) buf[l++] = c;
	if (n) {
		buf[l] = 0, ss << buf;
		goto next;
	} else if (skip) goto next;
	return ss.str();
}

string input::file_read_text(string fname) {
	::FILE *f = fopen(fname.c_str(), "r");
	if (!f) throw_runtime_error(err_fnf, fname);
	string r = file_read_text(f);
	fclose(f);
	return r;
}
void input::count_pos(ccs o, long& l, long& ch) {
	l = 1;
	ccs c = beg_ ? beg_ : o, n = c - 1;
	while (c < o) {
		if (*c && *c == '\n') { n = c; ++l; }
		++c;
	}
	ch = o-n;
}

bool throw_runtime_error(string err, string details) {
	ostringstream msg; msg << "Runtime error: \"" << err << "\"";
	if (details.size()) msg << " details: \"" << details << "\"";
	o::err() << msg.str() << endl;
#ifdef WITH_EXCEPTIONS
	throw runtime_error_exception(msg.str());
#else
	return false;
#endif
}

bool parse_error(const char* e, lexeme l) {
	input in((void*) 0, (size_t) 0);
	return in.parse_error(0, e, l);
}

bool parse_error(const char* e) {
	input in((void*) 0, (size_t) 0);
	return in.parse_error(0, e, 0);
}

bool parse_error(const char* e, std::string s) {
	input in((void*) 0, (size_t) 0);
	return in.parse_error(0, e, (ccs) s.c_str());
}

// Display an error with the given message, erronous lexeme, and context

bool parse_error(const char* e, lexeme l, std::string u) {
	input in((void*) 0, (size_t) 0);
	return in.parse_error(0, e, l[0], (ccs) u.c_str());
}

bool parse_error(ccs offset, const char* err) {
	input in((void*) 0, (size_t) 0);
	return in.parse_error(offset, err, offset);
}

bool input::parse_error(ccs offset, const char* err, lexeme close_to) {
	return parse_error(offset, err, close_to[0]);
}
bool input::type_error(const char* e, lexeme l) {
	return type_error(0, e, l[0]);
}

// Display an error with the given location, message, erronous lexeme,
// and context

bool input::parse_error(ccs offset, const char* err, ccs close_to, ccs ctx) {
	//DBG(o::dbg() << "parse_error: in->data: " << &data_ << " '" << data_
	//	<< "' offset: " << &offset << " '" << offset << "' "
	//	<< " error: '" << err << "' "
	//	<< " s: " << &close_to << " '" << close_to << "'"
	//	<< endl;)
	error = true;
	ostringstream msg; msg << "Parse error: \"" << err << '"';
	ccs p = close_to;
	while (p && *p && *p != '\n') ++p;
	ccs q = ctx;
	while (q && *q && *q != '\n') ++q;
	if (offset) {
		long l, ch; count_pos(offset, l, ch);
		msg << " at " << l << ':' << ch;
	}
	if (close_to) msg << " close to \""
		<< to_string(string_t(close_to, p - close_to)) << '"';
	if(ctx) msg << " of \"" << to_string(string_t(ctx, q - ctx)) << '"';
	o::err() << msg.str() << endl;
#ifdef WITH_EXCEPTIONS
	throw parse_error_exception(msg.str());
#endif
	return false;
}

bool input::type_error(ccs offset, const char* err, ccs close_to) {
	error = true;
	ostringstream msg; msg << "Type error: \"" << err << '"';
	ccs p = close_to;
	while (p && *p && *p != '\n') ++p;
	if (offset) {
		long l, ch; count_pos(offset, l, ch);
		msg << " at " << l << ':' << ch;
	}
	if (close_to) msg << " close to \""
		<< to_string(string_t(close_to, p - close_to)) << '"';
	o::err() << msg.str() << endl;
#ifdef WITH_EXCEPTIONS
	throw parse_error_exception(msg.str());
#endif
	return false;
}
