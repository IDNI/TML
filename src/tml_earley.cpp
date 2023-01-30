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
#include <map>
#include <set>
#include <string>
#include <cstring>
#include <sstream>
#include <forward_list>
#include <functional>
#include <cctype>
#include <ctime>
#include <locale>
#include <codecvt>
#include <fstream>
#include <iostream>
#include "driver.h"
#include "err.h"
#include "ir_builder.h"

using namespace std;

namespace idni {

#ifdef NEEDS_REWRITE

struct parsing_context {
	raw_progs& rps;
	std::vector<raw_prog*> rp;
	std::vector<state_block*> sbs;
	raw_rule rr;
	raw_term rt;
	directive d;
	production p;
	macro m;
	typestmt ts;
	bool head = true;
	bool neg  = false;
	bool is_directive = false;
	bool is_production = false;
	bool is_macro = false;
	bool is_type = false;
	bool is_predtype = false;
	bool renew = false;
	bool forget = false;
	bool is_constraint = false;
	bool is_fof = false;
	bool is_prefix = false;
	sprawformtree root;
	std::vector<std::pair<elem, elem>> prefixes;
	parsing_context(raw_progs& rps) : rps(rps) {}
};

vector<production> driver::load_tml_grammar() {
	// the following file is generated from /src/tml.g by /gen_tml.g.cpp.sh
	#include "tml.g.cpp"
	auto g = program_gen.p.nps[0].g;
	ir->transform_strsplit(g);
	bool changed = false;
	if (!ir->transform_ebnf(g, dict, changed)) return {};
	ir->transform_alts(g);
//#ifdef DEBUG
	//o::dbg() << "vector<production>:\n";
	//for (auto& x : g) o::dbg() << "\t" << x << endl;
	//o::dbg() << "///vector<production>;" << endl;
//#endif
	return g;
}

bool driver::parse_tml(input* in, flat_prog& fp) {
	typedef const parser_t::pnode& n_t; 
	typedef const parser_t::pnodes_set& ns_t;

	//#include "tml.grammar.inc.h"
	parser_t::grammar g = {};

	parser_t::parser_options po;
	po.bin_lr = opts.enabled("bin-lr");
	po.cc_fns = { "eof", "space", "digit", "alnum", "alpha", "printable" };
	parser_t pr(g, po);
	o::inf() << "\n### pr.recognize() : ";
	bool success = pr
		.recognize(to_u32string(string_t(in->data())));
	o::inf() << (success ? "OK" : "FAIL") << " <###\n" << endl;	
	return true;
}

bool driver::parse_tml_old(input* in, raw_progs& rps) {
	typedef const parser_t::pnode& ni_t; // node id/handle
	typedef const parser_t::pnodes_set& ncs_t;
	                                      // various node children args
	auto g = load_tml_grammar();
	parser_t::parser_options po;
	po.bin_lr = opts.enabled("bin-lr");
	po.cc_fns = { "eof", "space", "digit", "alnum", "alpha", "printable" };
	parser_t pr(ir->to_grammar(g), po);
	o::inf() << "\n### pr.recognize() : ";
	bool success = pr
		.recognize(to_u32string(string_t(in->data())));
	o::inf() << (success ? "OK" : "FAIL")<<
		" <###\n" << endl;
	parsing_context ctx(rps);
	parser_t::actions a{};
	auto to_int = [](std::string s) {
		int_t r = stoll(s);
		if (to_string(r) != s) { DBGFAIL; } // number reading parse err
		return r;
	};
	auto to_elem = [&to_int, this]
		(const std::u32string& s, const std::u32string& f)
	{
		elem::etype t = elem::NONE;
		if      (s == U"sym")         t = elem::SYM;
		else if (s == U"number")      t = elem::NUM;
		else if (s == U"var")         t = elem::VAR;
		else if (s == U"quoted_char") t = elem::CHR;
		else if (s == U"string")      t = elem::STR;
		if (t == elem::NUM)
			return elem{ to_int(to_string(to_string_t(f))) };
		else if (t == elem::CHR) {
			char32_t ch = f[1];
			if (ch == U'\\' && f.size() > 1)
				switch (f[2]) {
					case 'r':  ch = U'\r'; break;
					case 'n':  ch = U'\n'; break;
					case 't':  ch = U'\t'; break;
					case '\\': ch = U'\\'; break;
					case '\'': ch = U'\''; break;
				}
			return elem{ ch };
		} else  return elem{ t, dict.get_lexeme(
			to_string(to_string_t(f))) };
	};

	a.emplace(U"start", [&pr, &ctx, &a, &in, this](ni_t, ncs_t ncs) {
		ctx.rps.p.nps.emplace_back(dict);
		ctx.rp.push_back(&(ctx.rps.p.nps.back()));
		pr.down(ncs, a);
		ctx.rp.back()->expand_macros(in);
		ctx.rp.pop_back();
	});
	a.emplace(U"block", [&pr, &ctx, &a, &in, this](ni_t, ncs_t ncs) {
		ctx.rp.back()->nps.emplace_back(dict);
		ctx.rp.push_back(&(ctx.rp.back()->nps.back()));
		pr.down(ncs, a);
		ctx.rp.back()->expand_macros(in);
		ctx.rp.pop_back();
	});
	a.emplace(U"state_block",[&pr, &ctx, &a, &in, this](ni_t,ncs_t ncs){
		ctx.rp.back()->sbs.emplace_back(dict);
		ctx.sbs.push_back(&(ctx.rp.back()->sbs.back()));
		ctx.rp.push_back(&(ctx.sbs.back()->p));
		pr.down(ncs, a);
		ctx.rp.back()->expand_macros(in);
		ctx.rp.pop_back();
		ctx.sbs.pop_back();
	});
	a.emplace(U"sb_label", [&pr, &ctx, this](ni_t ni, ncs_t) {
		ctx.sbs.back()->label = dict.get_lexeme(to_string_t(
			pr.flatten(ni)));
	});
	a.emplace(U"sb_flipping", [&pr, &ctx, &a](ni_t, ncs_t ncs) {
		ctx.sbs.back()->flip = true;
		pr.down(ncs, a);
	});
	a.emplace(U"query", [&pr, &ctx, &a](ni_t, ncs_t ncs) {
		ctx.rr = {};
		ctx.head = true;
		pr.down(ncs, a);
		ctx.rr.type = raw_rule::GOAL;
		ctx.rp.back()->r.push_back(ctx.rr);
	});
	a.emplace(U"directive",[&pr, &ctx, &a](ni_t, ncs_t ncs) {
		ctx.is_directive = true;
		ctx.d = {};
		pr.down(ncs, a);
		ctx.rp.back()->d.push_back(ctx.d);
		ctx.is_directive = false;
	});
	a.emplace(U"string_drctv", [&pr, &ctx, &a](ni_t, ncs_t ncs) {
		ctx.d.type = directive::STR;
		pr.down(ncs, a);
	});
	a.emplace(U"stdout_drctv", [&pr, &ctx, &a](ni_t, ncs_t ncs) {
		ctx.d.type = directive::STDOUT;
		pr.down(ncs, a);
	});
	a.emplace(U"trace_drctv", [&pr, &ctx, &a](ni_t, ncs_t ncs) {
		ctx.d.type = directive::TRACE;
		pr.down(ncs, a);
	});
	a.emplace(U"internal_drctv", [&pr, &ctx, &a](ni_t, ncs_t ncs) {
		ctx.d.type = directive::INTERNAL;
		pr.down(ncs, a);
	});
	a.emplace(U"bwd_drctv", [&ctx] (ni_t, ncs_t) {
		ctx.d.type = directive::BWD;
	});
#ifdef WITH_EVAL
	a.emplace(U"domain_drctv", [&pr, &ctx, &a](ni_t, ncs_t ncs) {
		ctx.d.type = directive::EDOMAIN;
		pr.down(ncs, a);
	});
	a.emplace(U"eval_drctv", [&pr, &ctx, &a](ni_t, ncs_t ncs) {
		ctx.d.type = directive::EVAL;
		pr.down(ncs, a);
	});
	a.emplace(U"quote_drctv", [&pr, &ctx, &a](ni_t, ncs_t ncs) {
		ctx.d.type = directive::QUOTE;
		pr.down(ncs, a);
	});
	a.emplace(U"codec_drctv", [&pr, &ctx, &a](ni_t, ncs_t ncs) {
		ctx.d.type = directive::CODEC;
		pr.down(ncs, a);
	});
#endif // WITH_EVAL
	a.emplace(U"fname", [&pr, &ctx, this](ni_t ni, ncs_t) {
		ctx.d.type = directive::FNAME;
		ctx.d.arg  = dict.get_lexeme( 
			to_string_t(pr.flatten(ni)));
	});
	a.emplace(U"cmdline", [&pr, &ctx, &to_int](ni_t ni, ncs_t) {
		ctx.d.type = directive::CMDLINE;
		ctx.d.n    = to_int(to_string(to_string_t(
			pr.flatten(ni))));
	});
	a.emplace(U"cmdlinefile", [&pr, &ctx, &to_int](ni_t ni, ncs_t) {
		ctx.d.type = directive::CMDLINEFILE;
		ctx.d.n    = to_int(to_string(to_string_t(
			pr.flatten(ni))));
	});
	a.emplace(U"string",[&pr, &ctx, this](ni_t ni, ncs_t) {
		if (ctx.is_directive) ctx.d.arg = dict.get_lexeme(
			to_string_t(pr.flatten(ni)));
		else if (ctx.is_production) ctx.p.p.emplace_back(
			elem::STR, dict.get_lexeme(
				to_string_t(pr.flatten(ni))));
	});
	a.emplace(U"production", [&pr, &ctx, &a](ni_t, ncs_t ncs) {
		ctx.p = {};
		ctx.is_production = true;
		ctx.head = true;
		pr.down(ncs, a);
		ctx.rp.back()->g.push_back(ctx.p);
		ctx.is_production = false;
	});
	a.emplace(U"constraints", [&pr, &ctx, &a](ni_t, ncs_t ncs) {
		ctx.is_constraint = true;
		pr.down(ncs, a);
		ctx.is_constraint = false;
	});
	a.emplace(U"quoted_char", [&pr, &ctx, &to_elem](ni_t ni, ncs_t) {
		if (ctx.is_production) ctx.p.p
			.push_back(to_elem(U"quoted_char", pr.flatten(ni)));
	});
	a.emplace(U"alt_separator", [&ctx](ni_t, ncs_t) {
		if (ctx.is_production)
			ctx.p.p.push_back(elem{ elem::ALT });
	});
	a.emplace(U"typedef", [&pr, &ctx, &a](ni_t, ncs_t ncs) {
		ctx.is_type = true;
		ctx.ts = {};
		pr.down(ncs, a);
		ctx.rp.back()->vts.push_back(ctx.ts);
		ctx.is_type = false;
	});
	a.emplace(U"type", [&pr, &ctx, &a](ni_t, ncs_t ncs) {
		if (ctx.is_predtype) ctx.ts.typeargs.emplace_back();
		else ctx.ts.rty.membdecl.emplace_back();
		bool amb = ncs.size() > 1;
		for (auto& nc : ncs) for (auto& c : nc)
			if (!amb || c.first == U"primtype")
				pr.down(c.second, a);
	});
	a.emplace(U"predtypedef", [&pr, &ctx, &a](ni_t, ncs_t ncs) {
		ctx.is_predtype = true;
		pr.down(ncs, a);
		ctx.is_predtype = false;
	});
	a.emplace(U"structypename", [&pr, &ctx, this](ni_t ni, ncs_t) {
		ctx.ts.rty.structname = elem(elem::SYM, dict.get_lexeme(
			to_string_t(pr.flatten(ni))));
	});
	a.emplace(U"structype", [&pr, &ctx, this](ni_t ni, ncs_t) {
		(ctx.is_predtype ? ctx.ts.typeargs : ctx.ts.rty.membdecl)
			.back().structname = elem(elem::SYM, dict.get_lexeme(
				to_string_t(pr.flatten(ni))));
	});
	a.emplace(U"int_type", [&ctx](ni_t, ncs_t) {
		(ctx.is_predtype ? ctx.ts.typeargs : ctx.ts.rty.membdecl)
			.back().pty.ty = primtype::_ptype::UINT;
	});
	a.emplace(U"char_type", [&ctx](ni_t, ncs_t) {
		(ctx.is_predtype ? ctx.ts.typeargs : ctx.ts.rty.membdecl)
			.back().pty.ty = primtype::_ptype::UCHAR;
	});
	a.emplace(U"sym_type", [&ctx](ni_t, ncs_t) {
		(ctx.is_predtype ? ctx.ts.typeargs : ctx.ts.rty.membdecl)
			.back().pty.ty = primtype::_ptype::SYMB;
	});
	a.emplace(U"bitsz", [&pr, &ctx, &to_int](ni_t ni, ncs_t) {
		auto& t = ctx.is_predtype ? ctx.ts.typeargs:ctx.ts.rty.membdecl;
		t.back().pty.ty = primtype::_ptype::UINT;
		t.back().pty.bsz = to_int(
			to_string(to_string_t(pr.flatten(ni))));
	});
	a.emplace(U"var", [&pr, &ctx, this](ni_t ni, ncs_t) {
		elem e(elem::VAR,
			dict.get_lexeme(to_string_t(pr.flatten(ni))));
		if (ctx.is_prefix) ctx.prefixes.back().second = e;
		else if (ctx.is_type)
			(ctx.is_predtype ? ctx.ts.typeargs: ctx.ts.rty.membdecl)
			.back().vars.push_back(e);
	});
	a.emplace(U"rule", [&pr, &ctx, &a](ni_t, ncs_t ncs) {
		ctx.rr = {};
		ctx.head = true;
		pr.down(ncs, a);
		ctx.rp.back()->r.push_back(ctx.rr);
	});
	a.emplace(U"fof", [&pr, &ctx, &a](ni_t, ncs_t ncs) {
		ctx.rr = {};
		ctx.neg = false;
		ctx.head = true;
		ctx.is_fof = true;
		ctx.root = NULL;
		pr.down(ncs, a);
		//DBG(print_raw_form_tree(COUT << "parser parsed: ", *ctx.root) << "\n";)
		sprawformtree temp(ctx.root);
		if (temp) ctx.rr.prft = *temp;
		ctx.rp.back()->r.push_back(ctx.rr);
	});
	a.emplace(U"prefix_decl", [&pr, &ctx, &a](ni_t, ncs_t ncs) {
		ctx.prefixes.emplace_back();
		ctx.is_prefix = true;
		pr.down(ncs, a);
		ctx.is_prefix = false;
		//for (auto& t : ctx.prefixes)
		//	COUT << "prefix "<<c++<<": " << t.first << ", " << t.second << "\n";
		auto& p = ctx.prefixes.back();
		if (!ctx.root)
			ctx.root = make_shared<raw_form_tree>(p.first);
		else {
			auto cur = make_shared<raw_form_tree>(p.first);
			cur->r = ctx.root;
			ctx.root = cur;
		}
		ctx.root->l = make_shared<raw_form_tree>(p.second);
		//DBG(print_raw_form_tree(COUT << "new root: ", *ctx.root) << "\n";)
		ctx.prefixes.pop_back();
	});
	a.emplace(U"prefix", [&pr, &ctx](ni_t ni, ncs_t) {
		auto s = pr.flatten(ni);
		ctx.prefixes.back().first = elem(s == U"forall" ? elem::FORALL
			: s == U"exists" ? elem::EXISTS : elem::UNIQUE);
	});
	a.emplace(U"causal_op", [&ctx](ni_t, ncs_t ncs) {
		assert(ncs.size() == 1);
		elem e(ncs[0][0].first == U"implies"
			? elem::IMPLIES : elem::COIMPLIES);
		auto cur = make_shared<raw_form_tree>(e, ctx.root);
		ctx.root = cur;
		//DBG(print_raw_form_tree(COUT << "new root: ", *ctx.root) << "\n";)
	});
	a.emplace(U"junct_op", [&ctx](ni_t, ncs_t ncs) {
		assert(ncs.size() == 1);
		DBG(print_raw_form_tree(COUT << "old root: ", *ctx.root) << "\n";)
		elem e(ncs[0][0].first == U"and" ? elem::AND : elem::OR);
		auto cur = make_shared<raw_form_tree>(e, ctx.root);
		ctx.root = cur;
		//DBG(print_raw_form_tree(COUT << "new root: ", *ctx.root) << "\n";)
	});
	a.emplace(U"neg_matrix", [&pr, &ctx, &a](ni_t, ncs_t ncs) {
		pr.down(ncs, a);
		ctx.root = make_shared<raw_form_tree>(elem::NOT, ctx.root);
		//DBG(print_raw_form_tree(COUT << "new root: ", *ctx.root) << "\n";)
	});
	a.emplace(U"form", [&pr, &ctx, &a](ni_t, ncs_t ncs) {
		ctx.is_prefix = false;
		pr.down(ncs, a);
	});
	a.emplace(U"form1", [&pr, &ctx, &a](ni_t, ncs_t ncs) {
		ctx.is_prefix = false;
		pr.down(ncs, a);
	});
	a.emplace(U"matrix", [&pr, &ctx, &a](ni_t, ncs_t ncs) {
		ctx.is_prefix = false;
		pr.down(ncs, a);
	});
	a.emplace(U"fact", [&pr, &ctx, &a](ni_t, ncs_t ncs) {
		ctx.head = true;
		pr.down(ncs, a);
		ctx.rp.back()->r.push_back(raw_rule(ctx.rt));
	});
	a.emplace(U"macro", [&pr, &ctx, &a](ni_t, ncs_t ncs) {
		ctx.is_macro = true;
		ctx.head = true;
		ctx.m = {};
		pr.down(ncs, a);
		ctx.rp.back()->macros.push_back(ctx.m);
		ctx.is_macro = false;
	});
	a.emplace(U"preds", [&pr, &ctx, &a](ni_t, ncs_t ncs) {
		pr.down(ncs, a);
		ctx.head = false;
	});
	a.emplace(U"pred", [&pr, &a](ni_t, ncs_t ncs) {
		bool amb = ncs.size() > 1;
		for (auto& nc : ncs) for (auto& c : nc)
			if (!amb || c.first == U"builtin_expr")
				pr.down(c.second, a);
	});
	a.emplace(U"negative_term", [&pr, &ctx, &a](ni_t, ncs_t ncs) {
		ctx.neg = true;
		pr.down(ncs, a);
		ctx.neg = false;
	});
	a.emplace(U"positive_term", [&pr, &ctx, &a](ni_t, ncs_t ncs) {
		ctx.rt = {};
		pr.down(ncs, a);
		if (ctx.rt.extype != raw_term::ARITH) ctx.rt.calc_arity(0);
		ctx.rt.neg = ctx.neg;
		if (ctx.is_fof && !ctx.head) {
			if (!ctx.root) ctx.root = make_shared<raw_form_tree>(ctx.rt);
			else ctx.root->r = make_shared<raw_form_tree>(ctx.rt);
			//DBG(print_raw_form_tree(COUT << "new root: ", *ctx.root) << "\n";)
		} else if (ctx.is_directive) {	
			if (ctx.d.type == directive::INTERNAL)
				ctx.d.internal_term = ctx.rt;
			else ctx.d.t = ctx.rt;
		} else if (ctx.is_macro) {
			if (ctx.head) ctx.head = false, ctx.m.def = ctx.rt;
			else ctx.m.b.emplace_back(ctx.rt);
		} else if (ctx.head) ctx.rr.h.push_back(ctx.rt);
		else {
			if (ctx.rr.b.empty()) ctx.rr.b.emplace_back();
			ctx.rr.b.back().push_back(ctx.rt);
		}
	});
	a.emplace(U"relname", [&pr, &ctx, this](ni_t ni, ncs_t) {
		elem e(elem::SYM, dict.get_lexeme(
			to_string_t(pr.flatten(ni))));
		if (ctx.is_predtype)   ctx.ts.reln = e;
		if (ctx.is_directive)  ctx.d.rel   = e;
		if (ctx.is_production) ctx.p.p.push_back(e);
		if (ctx.is_prefix)     ctx.prefixes.back().second = e;
		else ctx.rt.e.push_back(e);
	});
	a.emplace(U"builtin_term", [&pr, &ctx, &a](ni_t, ncs_t ncs) {
		ctx.rt = {};
		ctx.rt.extype = raw_term::rtextype::BLTIN;
		ctx.neg = false;
		pr.down(ncs, a);
		if (ctx.rt.extype != raw_term::ARITH)
			ctx.rt.calc_arity(0);
		ctx.rt.neg = ctx.neg;
		if (ctx.is_macro) {
			if (ctx.head) ctx.head = 0, ctx.m.def = ctx.rt;
			else ctx.m.b.emplace_back(ctx.rt);
		} else if (ctx.head) ctx.rr.h.push_back(ctx.rt);
		else {
			if (ctx.rr.b.empty()) ctx.rr.b.emplace_back();
			ctx.rr.b.back().push_back(ctx.rt);
		}
	});
	a.emplace(U"builtin", [&pr, &ctx, this](ni_t ni, ncs_t) {
		ctx.rt.e.emplace_back(elem::BLTIN, dict.get_lexeme(
			to_string_t(pr.flatten(ni))));
		ctx.rt.e.back().num = ctx.renew << 1 | ctx.forget;
		ctx.renew = false, ctx.forget = false;
	});
	a.emplace(U"renew_prefix", [&ctx](ni_t, ncs_t) {
		ctx.renew = true;
	});
	a.emplace(U"forget_prefix", [&ctx](ni_t, ncs_t) {
		ctx.forget = true;
	});
	a.emplace(U"arith_expr", [&pr, &ctx, &a](ni_t, ncs_t ncs) {
		ctx.rt = {};
		ctx.rt.neg = false;
		ctx.rt.extype = raw_term::ARITH;
		pr.down(ncs, a);
		elem::etype t = ctx.rt.e[1].type;
		bool   neq  = t == elem::NEQ,
			lt  = t == elem::LT,
			gt  = t == elem::GT,
			geq = t == elem::GEQ;
		if (neq || t == elem::EQ) ctx.rt.extype = raw_term::EQ;
		if (lt || gt || geq || t == elem::LEQ)
			ctx.rt.extype = raw_term::LEQ;
		if (lt || geq) swap(ctx.rt.e[2], ctx.rt.e[0]);
		if (neq || gt || lt) ctx.rt.neg = !ctx.rt.neg;
		if (ctx.is_fof) {
			if (!ctx.root) ctx.root = make_shared<raw_form_tree>(ctx.rt);
			else {
				ctx.root->r = make_shared<raw_form_tree>(ctx.rt);
				ctx.root = ctx.root->r;
			}
			//DBG(print_raw_form_tree(COUT << "new root: ", *ctx.root) << "\n";)
		} else if (ctx.is_constraint) ctx.p.c.push_back(ctx.rt);
		else {
			if (ctx.rr.b.empty()) ctx.rr.b.emplace_back();
			ctx.rr.b.back().push_back(ctx.rt);
		}
	});
	a.emplace(U"constraint", [&pr, &ctx, &a](ni_t, ncs_t ncs) {
		ctx.rt = {};
		ctx.rt.neg = false;
		ctx.rt.extype = raw_term::CONSTRAINT;
		pr.down(ncs, a);
		ctx.p.c.push_back(ctx.rt);
	});
	a.emplace(U"constraint_builtin_name", [&pr, &ctx, this](
		ni_t ni, ncs_t)
	{
		ctx.rt.e.emplace_back(elem::SYM, dict.get_lexeme(to_string_t(
			pr.flatten(ni))));
	});
	a.emplace(U"constraint_arg", [&pr, &ctx, &to_elem](ni_t ni, ncs_t) {
		ctx.rt.e.push_back(to_elem(U"number", pr.flatten(ni)));
	});
	a.emplace(U"pref", [&ctx, this](ni_t, ncs_t) {
		ctx.rt.e.emplace_back(elem::SYM, dict.get_lexeme("_pref"));
	});
	a.emplace(U"priority", [&pr, &ctx, &to_int](ni_t ni, ncs_t) {
		ctx.rt.e.emplace_back(to_int(to_string(to_string_t(
			pr.flatten(ni)))));
	});
	a.emplace(U"arith_op", [&pr, &ctx](ni_t ni, ncs_t) {
		elem e;
		auto s = pr.flatten(ni);
		if      (s == U"=")  e = elem(elem::EQ);
		else if (s == U"!=") e = elem(elem::NEQ);
		else if (s == U"<=") e = elem(elem::LEQ);
		else if (s == U">")  e = elem(elem::GT);
		else if (s == U"<")  e = elem(elem::LT);
		else if (s == U">=") e = elem(elem::GEQ);
		else return;
		ctx.rt.e.emplace_back(e);
	});
	a.emplace(U"arith_aux_op", [&pr, &ctx, this](ni_t ni, ncs_t) {
		auto s = pr.flatten(ni);
		if      (s == U"+")  ctx.rt.arith_op = ADD;
		else if (s == U"-")  ctx.rt.arith_op = SUB;
		else if (s == U"*")  ctx.rt.arith_op = MULT;
		else if (s == U"|")  ctx.rt.arith_op = BITWOR;
		else if (s == U"&")  ctx.rt.arith_op = BITWAND;
		else if (s == U"^")  ctx.rt.arith_op = BITWXOR;
		else if (s == U"<<") ctx.rt.arith_op = SHR;
		else if (s == U">>") ctx.rt.arith_op = SHL;
		else return;
		ctx.rt.e.emplace_back(elem::ARITH, ctx.rt.arith_op,
			dict.get_lexeme(to_string_t(s)));
	});
	a.emplace(U"(", [&ctx](ni_t, ncs_t) {
		if (ctx.is_production && !ctx.is_constraint)
			ctx.p.p.emplace_back(elem::OPENP);
		else if (!ctx.is_predtype) ctx.rt.e.emplace_back(elem::OPENP);
	});
	a.emplace(U")", [&ctx](ni_t, ncs_t) {
		if (ctx.is_production && !ctx.is_constraint)
			ctx.p.p.emplace_back(elem::CLOSEP);
		else if (!ctx.is_predtype) ctx.rt.e.emplace_back(elem::CLOSEP);
	});
	a.emplace(U"{", [&ctx](ni_t, ncs_t) {
		if (ctx.is_production) ctx.p.p.emplace_back(elem::OPENB);
	});
	a.emplace(U"}", [&ctx](ni_t, ncs_t) {
		if (ctx.is_production) ctx.p.p.emplace_back(elem::CLOSEB);
	});
	a.emplace(U"[", [&ctx](ni_t, ncs_t) {
		if (ctx.is_production) ctx.p.p.emplace_back(elem::OPENSB);
	});
	a.emplace(U"]", [&ctx](ni_t, ncs_t) {
		if (ctx.is_production) ctx.p.p.emplace_back(elem::CLOSESB);
	});
	a.emplace(U"*", [&ctx](ni_t, ncs_t) {
		if (ctx.is_production) ctx.p.p.emplace_back(t_arith_op::MULT);
	});
	a.emplace(U"+", [&ctx](ni_t, ncs_t) {
		if (ctx.is_production) ctx.p.p.emplace_back(t_arith_op::ADD);
	});
	a.emplace(U"elem", [&pr, &ctx, &to_elem](ni_t, ncs_t ncs) {
		for (auto& nc : ncs) for (auto &c : nc)	ctx.rt.e
			.push_back(to_elem(c.first, pr.flatten(c.second)));
	});

	DBG(pr.print_ambiguity = opts.enabled("print-ambiguity");)
	DBG(pr.print_traversing = opts.enabled("print-traversing");)
	
	pr.topdown(U"start", a);

	return true;
}
#endif

} // idni namespace
