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
#include <filesystem>
#include "input.h"
#include "err.h"
#include "output.h"
using namespace std;

uint_t file_size(const string &filename) {
    try {
	return filesystem::file_size(filename);
    } catch(exception & e) {
        cout << e.what() << '\n';
    }
    return 0;
}

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
	}
}

input::~input() {
	//COUT << "destroying input" << (allocated_ ? " freeing *" : "")
	//	<< " data: " << beg_ << endl;
	if (allocated_) free((void*)beg_);
}

/**
 * This function tokenizes the input string
 * @param moving pointer to the string part
 * @return pointer to the beginning and end of lexeme in the string
 */
lexeme input::lex(pccs s) {
	while (isspace(**s)) ++*s;
	if (!**s) return { 0, 0 };
	ccs t = *s;
	if (!strncmp(*s, "/*", 2)) {
		while (strncmp(++*s, "*/", 2))
			if (!**s) parse_error(t, err_comment, 0);
		return ++++*s, lex(s);
	}
	if (**s == '#') {
		while (*++*s != '\r' && **s != '\n' && **s);
		return lex(s);
	}
	if (**s == '"') {
		while (*++*s != '"')
			if (!**s) parse_error(t, unmatched_quotes);
			else if (**s == '\\' && !strchr("\\\"", *++*s))
				parse_error(*s, err_escape);
		return { t, ++(*s) };
	}

	if (**s == '-' && *(*s + 1) == '>') {
		return *s += 2, lexeme{ *s - 2, *s };
	}
	// implication and coimplication
	if (**s == '<' && *(*s + 1) == '-' && *(*s + 2) == '>') {
		return *s += 3, lexeme{ *s - 3, *s };
	}
	// LEQ: put this in front if '<file>' below (as that'll eat us + error out)
	//if (**s == '<') {
	if (**s == '<' && !(*(*s + 1) == '<')) {
		if (*(*s + 1) == '=')
			return *s += 2, lexeme{ *s - 2, *s };
		// D: lex/parse: <file> parsing is moved to directive::parse, tag just <
		return ++*s, lexeme{ *s-1, *s };
	}
	//if (**s == '>') {
	if (**s == '>' && !(*(*s + 1) == '>')) {
		if (*(*s + 1) == '=')
			return *s += 2, lexeme{ *s - 2, *s };
		return ++*s, lexeme{ *s-1, *s };
	}
	if (**s == '\'') {
		if (*(*s + 1) == '\'') return { t, ++++*s };
		if (*(*s + 1) == '\\') {
			//if ((*(*s+2)!='\''&&*(*s+2)!='\\')
			if (!strchr("\\'rnt",*(*s+2)) ||*(*s+3)!='\'')
				parse_error((*s+2), err_escape);
			return { t, ++++++++*s };
		}
		if (*(*s + 2) != '\'') parse_error(*s+2, err_quote);
		return { t, ++++++*s };
	}
	if (**s == ':') {
		if (*++*s=='-' || **s=='=') return ++*s, lexeme{ *s-2, *s };
		else parse_error(*s, err_chr);
	}
	// NEQ: make sure we don't turn off directives (single '!'). limits?
	if (**s == '!' && *(*s + 1) == '=') {
		return *s += 2, lexeme{ *s - 2, *s };
	}

	//ARITH operators:
	//SHR, SHL, XXX: EQ?
	if (**s == '>' && (*(*s + 1) == '>')) return *s += 2, lexeme{ *s - 2, *s };
	if (**s == '<' && (*(*s + 1) == '<')) return *s += 2, lexeme{ *s - 2, *s };
	//if (**s == '=' && *(*s + 1) == '=') return *s += 2, lexeme{ *s - 2, *s };

	// TODO: single = instead of == recheck if we're not messing up something?
	if (**s == '=') return ++*s, lexeme{ *s-1, *s };
	if (strchr("!~.,;(){}$@=<>|&", **s)) return ++*s, lexeme{ *s-1, *s };
	if (strchr("!~.,;(){}$@=<>|&^+*", **s)) return ++*s, lexeme{ *s-1, *s };
	//TODO: review - for subtraction
	if (strchr("?-", **s)) ++*s;
	if (!isalnum(**s) && **s != '_') parse_error(*s, err_chr);
	while (**s && (isalnum(**s) || **s == '_')) ++*s;
	return { t, *s };
}

lexemes& input::prog_lex() {
	lexeme e;
	do {
		if ((e=lex(&data_)) != lexeme{0,0}) l.push_back(e);
	} while (*(data_));
	//size_ = (*(data_)) - (*(beg_));
	size_ = (data_ - beg_) * sizeof(ccs);
	//DBG(o::dbg() << "size of input: " << size_
	//	<< " beg_: " << (void*)beg_ << " data_: " << (void*)data_
	//	<< endl;)
	return l;
}

int_t input::get_int_t(ccs from, ccs to) {
	int_t r = 0;
	bool neg = false;
	if (*from == '-') neg = true, ++from;
	for (ccs s = from; s != to; ++s) if (!isdigit(*s))
		::parse_error(from, err_int);
	string s(from, to - from);
	try { r = stoll(s); }
	catch (...) { ::parse_error(from, err_int); }
	return neg ? -r : r;
}

bool directive::parse(input& in, const raw_prog& prog) {
	const lexemes& l = in.l;
	size_t& pos = in.pos;
	if (*l[pos][0] != '@') return false;
	if (l[++pos] == "trace") {
		type = TRACE; ++pos;
		if (!rel.parse(in) || rel.type != elem::SYM)
			in.parse_error(l[pos-1][0], err_trace_rel, l[pos-1]);
		if (*l[pos++][0] != '.')
			in.parse_error(l[pos-1][0], dot_expected, l[pos-1]);
		return true;
	}
	if (l[pos] == "bwd") {
		type = BWD;
		if (*l[++pos][0] != '.')
			in.parse_error(l[pos][0], dot_expected, l[pos]);
		return ++pos, true;
	}
	if (l[pos] == "stdout") {
		type = STDOUT; ++pos;
		if (!t.parse(in, prog))
			in.parse_error(l[pos][0], err_stdout, l[pos]);
		if (*l[pos++][0] != '.')
			in.parse_error(l[pos-1][0], dot_expected, l[pos-1]);
		return true;
	}
	if (!(l[pos] == "string"))
		in.parse_error(l[pos][0], err_directive, l[pos]);
	++pos;
	if (!rel.parse(in) || rel.type != elem::SYM)
		in.parse_error(l[pos-1][0], err_rel_expected, l[pos-1]);
	size_t curr2 = pos;
	if (*l[pos][0] == '<') {
		// D: parsing <file> is moved here (from lex) so we could process LT.
		//type = FNAME, arg = l[pos++];
		while (*l[pos++][0] != '>')
			if (!(pos < l.size()))
				in.parse_error(l[curr2][1], err_fname);
		type = FNAME, arg = lexeme{ l[curr2][0], l[pos-1][1] };
	}
	else if (*l[pos][0] == '"') type = STR, arg = l[pos++];
	else if (*l[pos][0] == '$')
		type=CMDLINE, ++pos, n = in.get_int_t(l[pos][0], l[pos][1]), ++pos;
	else if (l[pos] == "stdin") type = STDIN;
	else if (t.parse(in, prog)) {
		type = TREE;
		if (*l[pos++][0]!='.')
			in.parse_error(l[pos][0], dot_expected, l[pos]);
		return true;
	} else in.parse_error(l[pos][0], err_directive_arg, l[pos]);
	if (*l[pos++][0]!='.')
		in.parse_error(l[curr2][1], dot_expected, l[curr2]);
	return true;
}
elem::etype elem::peek(input& in) {
	size_t curr = in.pos;
	type = NONE;
	if (in.pos < in.l.size()) parse(in);
	in.pos = curr;
	return type;
}
bool elem::parse(input& in) {
	const lexemes& l = in.l;
	size_t& pos = in.pos;
	if ('|' == *l[pos][0]) return e = l[pos++],type=ALT,   true;
	if ('(' == *l[pos][0]) return e = l[pos++],type=OPENP, true;
	if (')' == *l[pos][0]) return e = l[pos++],type=CLOSEP,true;
	// NEQ: should we check for any limits here?
	if ('!' == l[pos][0][0] &&
		'=' == l[pos][0][1]) {
		return e = l[pos++], type = NEQ, true;
	}
	if ('-' == l[pos][0][0] &&
		'>' == l[pos][0][1]) {
		return e = l[pos++], type = IMPLIES, true;
	}

	if ('<' == l[pos][0][0] &&
		'-' == l[pos][0][1] &&
		'>' == l[pos][0][2]) {
		return e = l[pos++], type = COIMPLIES, true;
	}

	// LEQ: recheck if '<' is going to make any issues (order/card is important)
	// 	if ('<' == l[pos][0][0] && '=' == l[pos][0][1])
	if (('<' == l[pos][0][0])  && !('<' == l[pos][0][1])) {
		if ('=' == l[pos][0][1]) return e = l[pos++], type = LEQ, true;
		return e = l[pos++], type = LT, true;
	}

	if ('>' == l[pos][0][0] && !('>' == l[pos][0][1])) {
		if ('=' == l[pos][0][1]) return e = l[pos++], type = GEQ, true;
		return e = l[pos++], type = GT, true;
	}
	// TODO: single = instead of == recheck if we're not messing up something?
	if ('=' == l[pos][0][0]) {
		if (pos + 1 < l.size() && '>' == l[pos+1][0][0]) return false;
		return e = l[pos++], type = EQ, true;
	}

	if (('|' == l[pos][0][0]) && ('|' == l[pos][0][1])) {
		return e = l[pos++], type = OR, true;
	}
	if (('&' == l[pos][0][0]) && ('&' == l[pos][0][1])) {
		return e = l[pos++], type = AND, true;
	}

	if ('+' == l[pos][0][0]) {
		return e = l[pos++], type = ARITH, arith_op = ADD, true;
	}
	if ('-' == l[pos][0][0]) {
		return e = l[pos++], type = ARITH, arith_op = SUB, true;
	}
	if ('*' == l[pos][0][0]) {
		return e = l[pos++], type = ARITH, arith_op = MULT, true;
	}

	//FIXME conflicting with ALT
	if ('|' == l[pos][0][0]) {
		return e = l[pos++], type = ARITH, arith_op = BITWOR, true;
	}
	if ('&' == l[pos][0][0]) {
		return e = l[pos++], type = ARITH, arith_op = BITWAND, true;
	}
	if ('^' == l[pos][0][0]) {
		return e = l[pos++], type = ARITH, arith_op = BITWXOR, true;
	}
	if ('>' == l[pos][0][0] && '>' == l[pos][0][1]) {
		return e = l[pos++], type = ARITH, arith_op = SHR, true;
	}
	if ('<' == l[pos][0][0] && '<' == l[pos][0][1]) {
		return e = l[pos++], type = ARITH, arith_op = SHL, true;
	}

	if (!isalnum(*l[pos][0]) && !strchr("\"'-?", *l[pos][0])) return false;
	if (e = l[pos], *l[pos][0] == '\'') {
		type = CHR, e = { 0, 0 };
		if (l[pos][0][1] == '\'') ch = 0;
		else if (l[pos][0][1] != '\\') ch = l[pos][0][1];
		else if (l[pos][0][2] == 'r') ch = '\r';
		else if (l[pos][0][2] == 'n') ch = '\n';
		else if (l[pos][0][2] == 't') ch = '\t';
		else if (l[pos][0][2] == '\\') ch = '\\';
		else if (l[pos][0][2] == '\'') ch = '\'';
		else throw 0;
	}
	else if (*l[pos][0] == '?') type = VAR;
	else if (isalpha(*l[pos][0])) {
		size_t len = l[pos][1]-l[pos][0];
		if( len == 6 && !strncmp(l[pos][0], "forall", len ))
			type = FORALL;
		else if ( len == 6 && !strncmp(l[pos][0], "exists", len ) )
			type = EXISTS;
		else if ( len == 6 && !strncmp(l[pos][0], "unique", len ) )
			type = UNIQUE;
		else type = SYM;
	}
	else if (*l[pos][0] == '"') type = STR;
	else type = NUM, num = in.get_int_t(l[pos][0], l[pos][1]);
	return ++pos, true;
}

bool raw_term::parse(input& in, const raw_prog& prog,
	raw_term::rtextype pref_type)
{
	const lexemes& l = in.l;
	size_t& pos = in.pos;
	const lexeme &s = l[pos];
	size_t curr = pos;
	if ((neg = *l[pos][0] == '~')) ++pos;
	bool rel = false, noteq = false, eq = false, leq = false, gt = false,
		lt = false, geq = false, bltin = false, arith = false;

	t_arith_op arith_op_aux = NOP;

	// D: why was '<' a terminator? (only in directive). Removed, messes up LT.
	//XXX: review for "-"
	//FIXME: here we have conflict with LEC, ARITH and SOL(formula) parsing.
	//       also eventually ARITH will become formula as well.
	while (!strchr(".:,;{}-", *l[pos][0])) { // ".:,;{}|&-<"
		if (e.emplace_back(), !e.back().parse(in)) return false;
		else if (pos == l.size())
			in.parse_error(l[pos-1][1], err_eof, s[0]);
		elem& el = e.back(); // TODO: , el = e.back(), !el.parse(l, pos)
		switch (el.type) {
			case elem::EQ:  eq    = true; break;//TODO: review - for substraction
			case elem::NEQ: noteq = true; break;
			case elem::LEQ: leq   = true; break;
			case elem::GT:  gt    = true; break;
			case elem::LT:  lt    = true; break;
			case elem::GEQ: geq   = true; break;
			case elem::SYM:	if (prog.builtins.find(el.e)
						!= prog.builtins.end())
				{
					el.type = elem::BLTIN;
					bltin = true;
				}
				break;
			case elem::ARITH: arith = true; arith_op_aux = e.back().arith_op; break;
			default: break;
		}
		if (!rel) rel = true;
	}
	if (e.empty()) return false;
	// TODO: provide specific error messages. Also, something better to group?

	if (pref_type == rtextype::CONSTRAINT)  {

		extype = rtextype::CONSTRAINT;		
		return true;	
	}

	if (bltin) {
		// similar as for SYM below (join?) but this format will expand.
		if (e[0].type != elem::BLTIN)
			in.parse_error(l[pos][0], err_builtin_expected, l[pos]);
		if (e[1].type != elem::OPENP)
			in.parse_error(l[pos][0], err_paren_expected, l[pos]);
		if (e.back().type != elem::CLOSEP)
			in.parse_error(e.back().e[0], err_paren, l[pos]);
		extype = raw_term::BLTIN; // isbltin = true;
		return calc_arity(in), true;
	}
	if ( (noteq || eq) && !arith) {
		if (e.size() < 3)
			in.parse_error(l[pos][0], err_3_els_expected, l[pos]);
		// only supporting smth != smthelse (3-parts) and negation in front ().
		if (e[1].type != elem::NEQ && e[1].type != elem::EQ)
			in.parse_error(l[pos][0], err_eq_expected, l[pos]);
		if (noteq)
			neg = !neg; // flip the neg as we have NEQ, don't do it for EQ ofc
		extype = raw_term::EQ; // iseq = true;
		return calc_arity(in), true;
	}
	if ((leq || gt) && !arith) {
		if (e.size() < 3)
			in.parse_error(l[pos][0], err_3_els_expected, l[pos]);
		// only supporting smth != smthelse (3-parts) and negation in front ().
		if (e[1].type != elem::LEQ && e[1].type != elem::GT)
			in.parse_error(l[pos][0], err_leq_expected, l[pos]);
		if (gt) neg = !neg;
		extype = raw_term::LEQ; // isleq = true;
		return calc_arity(in), true;
	}
	if (lt || geq) {
		if (e.size() < 3)
			in.parse_error(l[pos][0], err_3_els_expected, l[pos]);
		// only supporting smth != smthelse (3-parts) and negation in front ().
		if (e[1].type != elem::LT && e[1].type != elem::GEQ)
			in.parse_error(l[pos][0], err_leq_expected, l[pos]);
		// GEQ <==> LEQ + reverse args + !neg
		swap(e[2], e[0]); // e = { e[2], e[1], e[0] };
		if (!geq) neg = !neg;
		extype = raw_term::LEQ;
		return calc_arity(in), true;
	}
	if (arith) {

		// ARITH operations are currently implemented to work with three arguments
		// var OPERATOR var RELATIONSHIP var
		// supported OPERATORs : + * | & ^ << >> (XXX - is TBD)
		// supported RELATIONSHIPs: = (TODO: add support for <= => < > != )
		// TODO: improve checks here
		if (e.size() < 4)
			in.parse_error(l[pos][0], err_term_or_dot, l[pos]);
		if (e[1].type != elem::ARITH || e[3].type != elem::EQ)
			in.parse_error(l[pos][0], err_term_or_dot, l[pos]);

		//iseq = true;
		neg = false;
		arith_op = arith_op_aux;
		extype = raw_term::ARITH;
		//return calc_arity(in), true;
		return true;
	}
	
	if (e[0].type != elem::SYM)
		in.parse_error(l[curr][0], err_relsym_expected, l[curr]);
	if (e.size() == 1) return calc_arity(in), true;
	if (e[1].type != elem::OPENP)
		in.parse_error(l[pos][0], err_paren_expected, l[pos]);
	if (e.back().type != elem::CLOSEP)
		in.parse_error(e.back().e[0], err_paren, l[pos]);
	return calc_arity(in), true;
}

void raw_term::insert_parens(lexeme op, lexeme cl) {
	elem o = elem(elem::OPENP, op), c = elem(elem::CLOSEP, cl);
	e.insert(e.begin() + 1, o), e.push_back(c);
	for (size_t n = 0, k = 2; n != arity.size(); ++n)
		if (arity[n] == -1) e.insert(e.begin() + k++, o);
		else if (arity[n] == -2) e.insert(e.begin() + k++, c);
		else k += arity[n];
}

void raw_term::calc_arity(input& in) {
	size_t dep = 0;
	arity = {0};
	//if (iseq || isleq || islt || isarith) {
	if (extype > raw_term::REL && extype < raw_term::BLTIN) {
		arity = { 2 };
		return;
	}
	if (e.size() == 1) return;
	for (size_t n = 2; n < e.size()-1; ++n)
		if (e[n].type == elem::OPENP) ++dep, arity.push_back(-1);
		else if (e[n].type != elem::CLOSEP) {
			if (arity.back() < 0) arity.push_back(1);
			else ++arity.back();
		} else if (!dep--) in.parse_error(e[n].e[0], err_paren, e[n].e);
		else arity.push_back(-2);
	if (dep) in.parse_error(e[0].e[0], err_paren, e[0].e);
}

bool raw_rule::parse(input& in, const raw_prog& prog) {
	const lexemes& l = in.l;
	size_t& pos = in.pos;	size_t curr = pos;
	if (*l[pos][0] == '!') {
		if (*l[++pos][0] == '!') ++pos, type = TREE;
		else type = GOAL;
	}
head:	h.emplace_back();
	if (!h.back().parse(in, prog)) return pos = curr, false;
	if (*l[pos][0] == '.') return ++pos, true;
	if (*l[pos][0] == ',') { ++pos; goto head; }
	if (*l[pos][0] != ':' || (l[pos][0][1] != '-' && l[pos][0][1] != '=' ))
		in.parse_error(l[pos][0], err_head, l[pos]);
	++pos;
	if(l[pos-1][0][1] == '=') { //  formula
		curr = pos;
		raw_sof rsof(prog);
		raw_form_tree * root = NULL;
		bool ret = rsof.parse(in, root);

		sprawformtree temp(root);
		this->prft = temp;

		if(ret) return true;
		in.parse_error(l[pos][0], "Formula has errors", l[pos]);
	} else {

		b.emplace_back();
		for (b.back().emplace_back(); b.back().back().parse(in, prog);
			b.back().emplace_back(), ++pos) {
			if (*l[pos][0] == '.') return ++pos, true;
			else if (*l[pos][0] == ';') b.emplace_back();
			else if (*l[pos][0] != ',') in
				.parse_error(l[pos][0], err_term_or_dot,l[pos]);
		}
		in.parse_error(l[pos][0], err_body, l[pos]);
	}
	return false;
}

bool raw_prefix::parse(input& in) {
	size_t curr = in.pos;
	isfod = false;
	if (!qtype.parse(in)) return false;
	if (qtype.type != elem::FORALL &&
		qtype.type != elem::EXISTS &&
		qtype.type != elem::UNIQUE)
			return in.pos = curr, false;
	if (*in.l[in.pos][0] == '?') isfod = true;
	if (!ident.parse(in)) return false;
	if (ident.type != elem::VAR && ident.type != elem::SYM)
		return in.pos = curr, false;
	return true;
}

bool raw_sof::parsematrix(input& in, raw_form_tree *&matroot) {
	const lexemes& l = in.l;
	size_t& pos = in.pos;
	size_t curr = pos;
	raw_form_tree * root = NULL;
	bool isneg = false;

	if (pos == l.size()) return NULL;
	if (*l[pos][0] == '~') isneg=true,++pos;
	if (pos != l.size() && *l[pos][0] == '{') {
		++pos;
		if( ! parseform(in, root, 0) ) goto Cleanup;
		if( isneg)
			root = new raw_form_tree(elem::NOT, NULL, NULL, root);

		if( pos == l.size() && *l[pos][0] != '}') goto Cleanup;
		++pos;

		matroot = root;
		return true;
	}
	else {
		elem next;
		next.peek(in);
		if (next.type == elem::SYM) {
			raw_term tm;
			if( !tm.parse(in, prog)) goto Cleanup;

			root = new raw_form_tree(elem::NONE, &tm);

			if (isneg) root = new raw_form_tree(elem::NOT,
				NULL, NULL, root);

			matroot = root;
			return true;
		} else {
			raw_form_tree *cur = NULL;
			while(next.type == elem::FORALL ||
				next.type == elem::UNIQUE ||
				next.type == elem::EXISTS )
			{
				raw_prefix rpfx;

				if( !rpfx.parse(in) ) goto Cleanup;

				if(!cur) root = cur = new raw_form_tree(
					rpfx.qtype.type, NULL, &rpfx.qtype);
				else cur->r = new raw_form_tree(
					rpfx.qtype.type, NULL, &rpfx.qtype),
					cur = cur->r;
				cur->l = new raw_form_tree(rpfx.ident.type,
					NULL, &rpfx.ident);
				next.peek(in);
			}

			if (cur == NULL || pos == l.size() || *l[pos][0] != '{')
				goto Cleanup;

			++pos;
			if (!parseform(in, cur->r, 0)) goto Cleanup;

			if (pos == l.size() || *l[pos][0] != '}') goto Cleanup;

			++pos;
			if (isneg) root = new raw_form_tree(elem::NOT,
				NULL, NULL, root);

			matroot = root;
			return true;
		}
	}

	Cleanup:
	//if(root) delete root;
	matroot = root;
	return pos=curr, false;
}
bool raw_sof::parseform(input& in, raw_form_tree *&froot, int_t prec ) {

	size_t curr = in.pos;
	raw_form_tree* root = NULL;
	raw_form_tree* cur = NULL;

	bool ret = parsematrix(in, root);
	elem nxt;
	if ( !ret ) goto Cleanup;

	nxt.peek(in);
	while (prec <=1 &&
		(nxt.type == elem::IMPLIES || nxt.type == elem::COIMPLIES))
	{
		nxt.parse(in);
		cur = new raw_form_tree(nxt.type, NULL, &nxt, root);
		root = cur;
		if (!parseform(in, root->r, 2)) goto Cleanup ;
		nxt.peek(in);
	}

	nxt.peek(in);
	while( prec <= 0 && (nxt.type == elem::AND || nxt.type == elem::ALT) ) {

		nxt.parse(in);
		cur = new raw_form_tree(nxt.type, NULL, &nxt, root);

		root = cur;
		if (!parseform(in, root->r, 1)) goto Cleanup;
		nxt.peek(in);

	}
	froot = root;
	return true;

	Cleanup:
	//if(root) delete root;
	froot = root;
	return in.pos=curr, false;
}

/* Populates root argument by creeating a binary tree of formula.
	It is caller's responsibility to manage the memory of root. If the parse function,
	returns false or the root is not needed any more, the caller should delete the root pointer.
	*/
bool raw_sof::parse(input& in, raw_form_tree *&root) {

	root = NULL;
	bool ret = parseform(in, root );

	if( in.pos >= in.l.size() || *in.l[in.pos][0] != '.') ret = false;
	else in.pos++;

	DBG(COUT << "\n cur = " << in.pos << " tot= " << in.l.size() << " \n ";)

	return ret;
}
 void raw_form_tree::printTree( int level)
{
	if( r ) r->printTree(level + 1)	;

	COUT << '\n';

	for(int i = 0; i < level; i++) COUT << '\t';

	if (type == elem::NOT ) COUT << '~';
	else if (this->rt)
		for(elem &etemp: rt->e) COUT <<lexeme2str(etemp.e).c_str()<<" ";
	else COUT <<lexeme2str(el->e).c_str()<<" ";
	if (l) l->printTree(level + 1);
}

bool production::parse(input &in, const raw_prog& prog) {
	const lexemes& l = in.l;
	size_t& pos = in.pos;
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
				if (!rt.parse(in, prog, raw_term::CONSTRAINT))
					goto fail;
				c.push_back(rt);
			}
			if (*l[pos][0] != '.') goto fail;
			return ++pos, true;
		}		
		if (!e.parse(in)) goto fail;
		p.push_back(e);
	}
	in.parse_error(l[curr2][0], err_prod, l[curr2]);
fail:	return pos = curr, false;
}

bool raw_prog::parse(input& in) {
	while (in.pos < in.l.size() && *in.l[in.pos][0] != '}') {
		directive x;
		raw_rule y;
		production p;
		// TODO: temp. passing prog/context, make parse(s) prog static instead.
		if (x.parse(in, *this)) d.push_back(x);
		else if (y.parse(in, *this)) r.push_back(y);
		else if (p.parse(in, *this)) g.push_back(p);
		else return false;
	}
	return true;
}

raw_progs::raw_progs() { } // parse(s); 

void raw_progs::parse(input& in, dict_t& dict, bool newseq) {
	try {
		if (!in.data_) return;
		lexemes& l = in.l;
		size_t& pos = in.pos;
		in.prog_lex();
		if (!l.size()) return;
		auto prepare_builtins = [&dict](raw_prog& x) {
			// BLTINS: prepare builtins (dict)
			for (const string& s : str_bltins)
				x.builtins.insert(
					dict.get_lexeme(s));
		};
		if (*l[pos][0] != '{') {
			raw_prog& x = !p.size() || newseq
				? p.emplace_back() : p.back();
			//raw_prog x;
			prepare_builtins(x);
			if (!x.parse(in))
				in.parse_error(l[pos][0],
					err_rule_dir_prod_expected, l[pos]);
			//p.push_back(x);
		} else do {
			// emplace to avoid copying dict etc. (or handle to avoid issues)
			raw_prog& x = p.emplace_back(); // if needed on err: p.pop_back();
			//raw_prog x;
			prepare_builtins(x);
			if (++pos, !x.parse(in))
				in.parse_error(l[pos][0], err_parse, l[pos]);
			//if (p.push_back(x), pos==l.size() || *l[pos++][0]!='}')
			if (pos == l.size() || *l[pos++][0] != '}')
				in.parse_error(l[pos-1][1],
					err_close_curly, l[pos-1]);
		} while (pos < l.size());
	} catch (parse_error_exception &e) {
		o::err() << e.what() << endl;
	} catch (runtime_error_exception &e) {
		o::err() << e.what() << endl;
	}
}

bool operator==(const lexeme& x, const lexeme& y) {
	return x[1] - x[0] == y[1] - y[0] && !strncmp(x[0], y[0], x[1] - x[0]);
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
	if (x.b != y.b) return x.b < y.b;
/*	if (x.h.size() != y.h.size())
		return x.heads().size() < y.heads().size();
	if (x.bodies().size() != y.bodies().size())
		return x.bodies().size() < y.bodies().size();
	for (size_t n = 0; n != x.h.size(); ++n)
		if (!(x.head(n) == y.h[n])) return x.head(n) < y.head(n);
	for (size_t n = 0; n != x.bodies().size(); ++n)
		if (!(x.body(n) == y.body(n))) return x.body(n) < y.body(n);*/
	return false;
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

off_t fsize(ccs s, size_t len) { return fsize(string(s, len).c_str()); }

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

void throw_runtime_error(string err, string details) {
	ostringstream msg; msg << "Runtime error: \"" << err << "\"";
	if (details.size()) msg << " details: \"" << details << "\"";
	throw runtime_error_exception(msg.str());
}

void parse_error(const char* e, lexeme l) {
	input in((void*) 0, (size_t) 0); in.parse_error(0, e, l);
}

void parse_error(const char* e) {
	input in((void*) 0, (size_t) 0); in.parse_error(0, e, 0);
}

void parse_error(const char* e, std::string s) {
	input in((void*) 0, (size_t) 0); in.parse_error(0, e, s.c_str());
}

void parse_error(ccs offset, const char* err) {
	input in((void*) 0, (size_t) 0); in.parse_error(offset, err, offset);
}

void input::parse_error(ccs offset, const char* err, lexeme close_to) {
	parse_error(offset, err, close_to[0]);
}

void input::parse_error(ccs offset, const char* err, ccs close_to) {
	DBG(o::dbg() << "parse_error: in.data: " << &data_ << " '" << data_
		<< "' offset: " << &offset << " '" << offset << "' "
		<< " error: '" << err << "' "
		<< " s: " << &close_to << " '" << close_to << "'"
		<< endl;)

	ostringstream msg; msg << "Parse error: \"" << err << '"';
	ccs p = close_to;
	while (p && *p && *p != '\n') ++p;
	if (offset != 0) {
		long l, ch; count_pos(offset, l, ch);
		msg << " at " << l << ':' << ch;
	}
	if (close_to) msg << " close to \""
		<< string(close_to, p - close_to) << '"';
	throw parse_error_exception(msg.str());
}
