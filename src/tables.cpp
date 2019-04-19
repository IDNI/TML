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
#include "tables.h"
#include "dict.h"
#include "input.h"
using namespace std;
using namespace std::placeholders;

#define mkchr(x) ((((int_t)x)<<2)|1)
#define mknum(x) ((((int_t)x)<<2)|2)

size_t sig_len(const sig_t& s) {
	size_t r = 0;
	for (auto x : get<1>(s)) if (x > 0) r += x;
	return r;
}

#ifdef DEBUG
vbools tables::allsat(spbdd x, ntable tab) {
	const size_t args = sig_len(sigs[tab]);
	vbools v = ::allsat(x, tbits + bits * args), s;
	for (bools b : v) {
		s.emplace_back(bits * args);
		for (size_t n = 0; n != bits; ++n)
			for (size_t k = 0; k != args; ++k)
				s.back()[k*bits+n] = b[pos(n, k, args)];
	}
	return s;
}
#endif

spbdd tables::leq_const(int_t c, size_t arg, size_t args, size_t bit) const {
	if (!bit--) return T;
	spbdd t = leq_const(c, arg, args, bit);
	t = (c & (1 << bit)) ? bdd_ite(pos(bits-bit-1, arg, args), t , T) :
		bdd_ite(pos(bits-bit-1, arg, args), F, t);
	return t;
}

spbdd tables::range(size_t arg, ntable tab) {
	array<int_t, 7> k = { syms, nums, chars, (int_t)tab, (int_t)arg,
		(int_t)bits, (int_t)tbits };
	auto it = range_memo.find(k);
	if (it != range_memo.end()) return it->second;
	const size_t args = sig_len(sigs[tab]);
	spbdd	ischar= bdd::from_bit(pos(bits-1, arg, args), true) &&
			bdd::from_bit(pos(bits-2, arg, args), false);
	spbdd	isnum = bdd::from_bit(pos(bits-1, arg, args), false) &&
			bdd::from_bit(pos(bits-2, arg, args), true);
	spbdd	issym = bdd::from_bit(pos(bits-1, arg, args), false) &&
			bdd::from_bit(pos(bits-2, arg, args), false);
	spbdd	r = range_memo[k] = bdd_and_many({
			ischar || isnum || issym,
			(!chars	? T%ischar : bdd_impl(ischar,
				leq_const(mkchr(chars-1), arg, args, bits))),
			(!nums 	? T%isnum : bdd_impl(isnum, 
				leq_const(mknum(nums-1), arg, args, bits))),
			(!syms 	? T%issym : bdd_impl(issym, 
				leq_const(((syms-1)<<2), arg, args, bits)))});
	DBG(wcout<<"range:"<<endl<<allsat(r, tab)<<endl<<endl;)
	return onmemo(), r;
}

void tables::range_clear_memo() {onmemo(-range_memo.size()),range_memo.clear();}

size_t tables::pos(size_t bit, size_t nbits, size_t arg, size_t args) const {
	DBG(assert(bit < nbits && args <= max_args && arg < args);)
	return (nbits - bit - 1) * args + arg + tbits;
}

size_t tables::pos(size_t bit, size_t arg, size_t args) const {
	DBG(assert(bit < bits && args <= max_args && arg < args);)
	return (bits - bit - 1) * args + arg + tbits;
}

size_t tables::arg(size_t v, size_t args) const {
	DBG(assert(v >= tbits);)
	return (v - tbits) % args;
}

size_t tables::bit(size_t v, size_t args) const {
	DBG(assert(v >= tbits);)
	return bits - ((v - tbits) / args) - 1;
}

spbdd tables::add_bit(spbdd x, ntable tab) {
	validate();
	const size_t args = sig_len(sigs[tab]);
	sizes perm(args * bits + tbits);
	for (size_t n = 0; n != perm.size(); ++n) perm[n] = n;
//	DBG(wcout<<"before perm var:"<<x->v()<<endl<<::allsat(x, max_args*bits+tbits)<<endl;)
	for (size_t n = 0; n != args; ++n)
		for (size_t k = 0; k != bits; ++k)
			perm[pos(k, n, args)] = pos(k, bits+1, n, args);
//	DBG(wcout<<"after perm var:"<<x->v()<<endl<<::allsat(x, max_args*(bits+1)+tbits)<<endl;)
	bdds v = { x ^ perm };
	for (size_t n = 0; n != args; ++n)
		v.push_back(bdd::from_bit(
			pos(bits, bits + 1, n, args), false));
	x = bdd_and_many(move(v));
	validate();
//	DBG(wcout<<"after and:"<<endl<<::allsat(x, max_args*(bits+1)+tbits)<<endl;)
	return x;
}

void tables::add_bit() {
	range_clear_memo();
	DBG(out(wcout<<"before add_bit:"<<endl);)
	spbdd x = F;
	for (size_t n=0; n!=tbdds.size(); ++n) x = x || add_bit(db&&tbdds[n],n);
	db = x, ++bits;
	DBG(out(wcout<<"after add_bit:"<<endl);)
}

void tables::add_tbit() {
	validate();
	range_clear_memo();
	DBG(out(wcout<<"before add_tbit:"<<endl);)
	sizes perm(max_args * bits + tbits);
	for (size_t n = 0; n != perm.size(); ++n) perm[n] = n + 1;
//	DBG(wcout<<"before add_tbit:"<<endl<<::allsat(db, max_args*bits+tbits)<<endl;)
	db = (db ^ perm) && bdd::from_bit(0, false), ++tbits;
	DBG(out(wcout<<"after add_tbit:"<<endl);)
	validate();
//	DBG(wcout<<"after add_tbit:"<<endl<<::allsat(db, max_args*bits+tbits)<<endl;)
}

spbdd tables::from_row(const ints& row, ntable tab, bools *ex) {
	bdd::validate();
	if (ex) *ex = bools(bits * row.size() + tbits, false);
	bdds v;
	const size_t args = row.size();
	map<int_t, size_t> vs;
	for (size_t n = 0, b; n != args; ++n) {
		if (row[n] >= 0)
			for (b = 0; b != bits; ++b) {
				v.push_back(bdd::from_bit(pos(b, n, args),
						row[n]&(1<<(bits-b-1))));
				if (ex) (*ex)[pos(b, n, args)] = true;
			}
		else {
			bdd::validate();
			auto it = vs.find(row[n]);
			if (it == vs.end())
				v.push_back(range(vs[row[n]] = n, tab));
			else for (b = 0; b != bits; ++b) {
				v.push_back(bdd::from_eq(
					pos(b,n,args), pos(b,it->second,args)));
				if (ex) (*ex)[pos(b, it->second, args)] = true;
			}
		}
	}
	bdd::validate();
	spbdd r = bdd_and_many(move(v));
//	DBG(wcout<<"from_row:"<<endl<<::allsat(r, max_args*bits+tbits)<<endl;)
	DBG(wcout<<"from_row:"<<endl<<allsat(r, tab)<<endl;)
	bdd::validate();
	return r;
}

ntable tables::add_table(sig_t s) {
	validate();
	auto it = ts.find(s);
	if (it != ts.end()) return it->second;
	ntable nt = sigs.size();
	max_args = max(max_args, sig_len(s));
	if (!sigs.size() || sigs.size() > (size_t)(1 << (tbits-1))) add_tbit();
	spbdd t = T;
	for (size_t b = 0; b != tbits; ++b)
		t = t && bdd::from_bit(b,nt&(1<<(tbits-b-1)));
//	DBG(wcout<<"table "<<nt<<" bits: "<<tbits<<endl<<::allsat(t, max_args*bits+tbits)<<endl<<endl);
	validate();
	return ts.emplace(s, nt), sigs.push_back(s), tbdds.push_back(t), nt;
}

void tables::add_term(ntable tab, const ints& row) {
	validate();
	if (tab >= (1 << tbits)) add_tbit();
	bdds v;
//	for (const ints& i : rows) v.push_back(from_row(i, tab));
	DBG(wcout<<"before add:"<<endl<<::allsat(db, max_args*bits+tbits)<<endl;)
	//db = (bdd_or_many(v) && tbdds[tab]) || db;
	db = (from_row(row, tab) && tbdds[tab]) || db;
	validate();
	DBG(wcout<<"tbdd:"<<endl<<::allsat(tbdds[tab], /*max_args*bits+*/tbits)<<endl;)
//	DBG(wcout<<"after add:"<<endl<<::allsat(db, max_args*bits+tbits)<<endl;)
	DBG(wcout<<"with tab:"<<endl<<allsat(bdd_or_many((v)) && tbdds[tab], tab)<<endl;)
	DBG(wcout<<"after add:"<<endl<<allsat(db, tab)<<endl;)
}

sig_t tables::get_sig(const raw_term&t){return{dict.get_rel(t.e[0].e),t.arity};}

void tables::add_raw_terms(const vector<raw_term>& r) {
	for (auto x : r) add_raw_term(x);
}

void tables::add_raw_term(const raw_term& r) {
	ints t;
	for (size_t n = 1; n < r.e.size(); ++n)
		switch (r.e[n].type) {
			case elem::OPENP:
			case elem::CLOSEP: break;
			case elem::NUM:
				nums = max(nums, r.e[n].num+1);
				t.push_back(mknum(r.e[n].num)); break;
			case elem::CHR:
				chars = 256;
				t.push_back(mkchr(r.e[n].ch)); break;
			case elem::VAR:
				t.push_back(dict.get_var(r.e[n].e)); break;
			default: t.push_back(dict.get_sym(r.e[n].e));
				 syms = max(syms, (int_t)dict.nsyms());
		}
		/*else if (r.e[n].type == elem::STR) {
			lexeme l = r.e[n].e;
			++l[0], --l[1];
			t.push_back(dict.get_sym(dict.get_lexeme(
				_unquote(lexeme2str(l)))));
		}*/
//	DBG(wcout<<"before add:"<<endl<<::allsat(db, max_args*bits+tbits)<<endl;)
	while (nums + chars + syms > (1 << (bits - 2))) add_bit();
	return add_term(get_table(r), t);
}

ntable tables::get_table(const raw_term& t) { return add_table(get_sig(t)); }

void tables::out(wostream& os) {
	DBG(wcout<<"as:"<<endl<<::allsat(db, max_args*bits+tbits)<<endl;)
	validate();
	lexeme op(dict.get_lexeme(L"(")), cl(dict.get_lexeme(L")"));
	allsat_cb(db, tbits, 0, [&os, op, cl, this](const bools& p, spbdd x) {
		if (x->leaf() && !x->trueleaf()) return;
		ntable tab = 0;
		for (size_t n = 0; n != p.size(); ++n)
			if (p[n]) tab |= 1 << (tbits - n - 1);
		DBG(assert((size_t)tab < sigs.size());)
		validate();
		auto f = [&os, tab, op, cl, this](const bools& p, spbdd DBG(y)){
			DBG(assert(y->leaf());)
			const size_t args = sig_len(sigs[tab]);
			term r = { false, sigs[tab], ints(args, 0) };
			for (size_t n = 0; n != args; ++n)
				for (size_t k = 0; k != bits; ++k)
					if (p[pos(k, n, args)])
						get<2>(r)[n] |= 1 << (bits-k-1);
			raw_term rt;
			rt.e.resize(args+1),
			rt.e[0]=elem(elem::SYM,dict.get_rel(get<0>(sigs[tab])));
			for (size_t n = 1; n != args + 1; ++n) {
				int_t arg = get<2>(r)[n - 1];
				if (arg & 1) rt.e[n]=elem((wchar_t)(arg>>2));
				else if (arg & 3) rt.e[n]=elem((int_t)(arg>>2));
				else rt.e[n]=elem(elem::SYM, dict.get_sym(arg));
			}
			rt.arity = get<1>(sigs[tab]), rt.insert_parens(op, cl),
			os<<rt<<endl;
		};
		allsat_cb(x, sig_len(sigs[tab]) * bits + tbits, tbits, f)();
	})();
}

#ifdef DEBUG
bool _bddcmp(spbdd x, spbdd y) {
	if (x == y) return true;
	if (x->leaf() != y->leaf()) return false;
	if (x->leaf()) return x->trueleaf() == y->trueleaf();
	if (x->v() != y->v()) return false;
	return _bddcmp(x->l(), y->l()) && _bddcmp(x->h(), y->h());
}
#else
bool _bddcmp(spbdd x, spbdd y);
#endif

void tables::validate() {
	NDBG(return;)
	bdd::validate();
	if (db == F) return;
	auto bddcmp = [](spbdd x, spbdd y) {
		bdd::validate();
		bool b = x == y;
		bool c = _bddcmp(x, y);
		if (b != c) bdd::validate(x, y);
		assert((x == y) == (_bddcmp(x, y)));
		return x == y;
	};
	spbdd t = F;
	for (size_t n = 0; n != tbdds.size(); ++n) t = t || tbdds[n];
	if (!bddcmp(F, db%t) || !bddcmp(db, db&&t)) {
		for (size_t n = 0; n != tbdds.size(); ++n) {
			wcout<<"tbdd["<<n<<"]:"<<endl<<::allsat(tbdds[n], tbits)
			<<endl<<"db:"<<endl<<
			::allsat(db, tbits + bits*max_args+1)<<endl
			<<"sig: " << dict.get_rel(get<0>(sigs[n])) << L' ';
			for (int_t i : get<1>(sigs[n])) wcout << i << ' ';
			wcout << endl;
		}
		wcout<<"db&&t:"<<endl<<::allsat(db&&t, tbits+max_args*bits+1);
		spbdd y = db && t;
		assert((db % t) == F);
		assert((db && t) == db);
	}
	assert(tbdds.size() == sigs.size());
	for (size_t n = 0; n != sigs.size(); ++n) {
		t = db && tbdds[n];
		spbdd x;
		for (size_t k = 0; k != sig_len(sigs[n]); ++k)
			x = range(k, n),
			assert(bddcmp(x && t, t));
	}
}

tables::tables() : dict(*new dict_t) {}
tables::~tables() { delete &dict; }

int main() {
	bdd::init();
	//raw_progs rp(L"c(y).e(x).d(4).d(?z).");
//	raw_progs rp(L"a(z).c(y).e(x).d(0).");
	//raw_progs rp(L"e(x 5).c(y).d(1).d(?z).");
	//raw_progs rp(L"d(1 ?z).");
//	raw_progs rp(L"c(y).e(x).e(z).");
	raw_progs rp(L"c(y).");
//	raw_progs rp(stdin);
	tables t;
	for (size_t n = 0; n != rp.p[0].r.size(); ++n)
		t.add_raw_terms(rp.p[0].r[n].heads()),
		t.out(wcout<<endl);
	bdd::onexit = true;
	return 0;
}
