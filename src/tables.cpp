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

class walk {
	const tables& t;
	size_t v = 1;
	const size_t tbits;
	bools p;
public:
	typedef function<void(spbdd, ntable)> callback;
	callback f;
	walk(const tables& t, callback f) :t(t),tbits(t.tbits),p(t.tbits),f(f){}
	void operator()(spbdd x);
};

class transform {
	const tables& t;
	size_t v = 1, tab;
	const size_t tbits;
	bools p;
public:
	typedef function<spbdd(spbdd, ntable)> callback;
	callback f;
	transform(const tables& t, callback f)
		: t(t), tbits(t.tbits), p(tbits), f(f) {}
	spbdd operator()(spbdd x);
};

class sat {
	tables& t;
	size_t v, nvars;
	bools p;
	sig_t s;
	typedef function<void(const raw_term&)> callback;
	callback f;
	walk w;
	lexeme op, cl;
	void cb(spbdd x, ntable tab) {
		p.resize(t.tbits + (nvars = (sig_len(s = t.sigs[tab])*t.bits)));
		run(x);
	}
	void run(spbdd x);
public:
	sat(tables& t, callback f) : t(t), v(t.tbits+1), p(t.tbits), f(f),
		w(t, bind(&sat::cb, this, _1, _2)),
		op(t.dict.get_lexeme(L"(")), cl(t.dict.get_lexeme(L")")) {}
	void operator()(spbdd x) { w(x); }
};

size_t sig_len(const sig_t& s) {
	size_t r = 0;
	for (auto x : get<1>(s)) if (x > 0) r += x;
	return r;
}

void sat::run(spbdd x) {
	if (x->leaf() && !x->trueleaf()) return;
	if (!x->leaf() && v < x->v())
		p[++v-2] = true, run(x), p[v-2] = false, run(x), --v;
	else if (v != t.tbits + nvars + 1)
		p[++v-2] = true, run(x->h()), p[v-2] = false, run(x->l()), --v;
	else {
		const size_t args = nvars / t.bits;
		term r = { false, s, ints(args, 0) };
		for (size_t n = 0; n != args; ++n)
			for (size_t k = 0; k != t.bits; ++k)
				if (p[t.pos(k, n, args)])
					get<2>(r)[n] |= 1 << k;
		raw_term rt;
		rt.e.resize(args+1), rt.neg = false,
		rt.e[0] = elem(elem::SYM, t.dict.get_rel(get<0>(s)));
		for (size_t n = 0; n != args; ++n) {
			int_t arg = get<2>(r)[n];
			if (arg & 1) rt.e[n+1] = elem((wchar_t)(arg>>2));
			else if (arg & 3) rt.e[n+1] = elem((int_t)(arg>>2));
			else rt.e[n+1]= elem(elem::SYM, t.dict.get_sym(arg));
		}
		rt.arity = get<1>(s), rt.insert_parens(op, cl), f(move(rt));
	}
}

void walk::operator()(spbdd x) {
	if (x->leaf() && !x->trueleaf()) return;
	if (v == t.tbits + 1) {
		ntable tab = 0;
		for (size_t n = 0; n != p.size(); ++n)
			if (p[n]) tab |= 1 << (t.tbits-n-1);
		DBG(assert((size_t)tab < t.sigs.size());)
		f(x, tab);
	}
	else if (!x->leaf() && v < x->v())
		p[++v-2] = true, (*this)(x), p[v-2]=false, (*this)(x), --v;
	else p[++v-2]=true, (*this)(x->h()), p[v-2]=false, (*this)(x->l()), --v;
}

spbdd transform::operator()(spbdd x) {
//	DBG(wcout<<"transform var: "<<x->v()<<" v: "<<v<<endl<<::allsat(x, t.max_args*t.bits+t.tbits)<<endl;)
	if (x->leaf() && !x->trueleaf()) return x;
	if (v == t.tbits + 1) {
		tab = 0;
		for (size_t n = 0; n != p.size(); ++n) if (p[n]) tab |= 1 << n;
		return f(x, tab);
	}
	spbdd h, l;
	if (!x->leaf() && v < x->v())
		p[++v-2] = true,h = (*this)(x),
		p[v-2] = false,	l = (*this)(x), --v;
	else	p[++v-2] = true,h = (*this)(x->h()),
		p[v-2] = false,	l = (*this)(x->l()), --v;
//	DBG(wcout<<"after transform h var: "<<h->v()<<" v: " << v<<endl<<::allsat(h, t.max_args*t.bits+t.tbits)<<endl;)
//	DBG(wcout<<"after transform l var: "<<l->v()<<" v: " << v<<endl<<::allsat(l, t.max_args*t.bits+t.tbits)<<endl;)
	x = bdd_ite(x->v(), h, l);
//	DBG(wcout<<"after transform var: "<<x->v()<<" v: " << v<<endl<<::allsat(x, t.max_args*t.bits+t.tbits)<<endl;)
	return x;
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
	return (c & (1 << bit)) ? t : bdd::add(pos(bit, arg, args), F, t);
}

spbdd tables::range(size_t arg, ntable tab) {
	array<int_t, 7> k = { syms, nums, chars, (int_t)tab, (int_t)arg,
		(int_t)bits, (int_t)tbits };
	auto it = range_memo.find(k);
	if (it != range_memo.end()) return it->second;
	const size_t args = sig_len(sigs[tab]);
	spbdd	ischar= bdd::from_bit(pos(0, arg, args), true) &&
			bdd::from_bit(pos(1, arg, args), false);
	spbdd	isnum = bdd::from_bit(pos(0, arg, args), false) &&
			bdd::from_bit(pos(1, arg, args), true);
	spbdd	issym = bdd::from_bit(pos(0, arg, args), false) &&
			bdd::from_bit(pos(1, arg, args), false);
	spbdd	r = range_memo[k] = bdd_and_many({
			ischar || isnum || issym,
			(!chars	? T%ischar : bdd_impl(ischar,
				leq_const(mkchr(chars-1), arg, args, bits))),
			(!nums 	? T%isnum : bdd_impl(isnum, 
				leq_const(mknum(nums-1), arg, args, bits))),
			(!syms 	? T%issym : bdd_impl(issym, 
				leq_const(((syms-1)<<2), arg, args, bits)))});
//	DBG(wcout<<"range:"<<endl<<allsat(r, tab)<<endl<<endl;)
//	DBG(wcout<<"range:"<<endl<<::allsat(r, tbits+max_args*bits)<<endl<<endl;)
//	DBG(wcout<<"issym:"<<endl<<allsat(issym, tab)<<endl<<endl;)
//	DBG(wcout<<"issym:"<<endl<<::allsat(issym, tbits+max_args*bits)<<endl<<endl;)
//	DBG(wcout<<"lc:"<<endl<<allsat(issym&&leq_const(((syms-1)<<2), arg, args, bits-1), tab)<<endl<<endl;)
//	DBG(wcout<<"lc:"<<endl<<::allsat(issym&&leq_const(((syms-1)<<2), arg, args, bits-1), tbits+max_args*bits)<<endl<<endl;)
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
	const size_t args = sig_len(sigs[tab]);
	sizes perm(args * bits + tbits);
	for (size_t n = 0; n != perm.size(); ++n) perm[n] = n;
	DBG(wcout<<"before perm var:"<<x->v()<<endl<<::allsat(x, max_args*bits+tbits)<<endl;)
	for (size_t n = 0; n != args; ++n)
		for (size_t k = 0; k != bits; ++k)
			perm[pos(k, n, args)] = pos(k, bits+1, n, args);
	DBG(wcout<<"after perm var:"<<x->v()<<endl<<::allsat(x, max_args*(bits+1)+tbits)<<endl;)
	bdds v = { x ^ perm };
	for (size_t n = 0; n != args; ++n)
		v.push_back(bdd::from_bit(
			pos(bits, bits + 1, n, args), false));
	x = bdd_and_many(move(v));
	DBG(wcout<<"after and:"<<endl<<::allsat(x, max_args*(bits+1)+tbits)<<endl;)
	return x;
}

void tables::add_bit() {
	range_clear_memo();
	spbdd x = F;
	for (size_t n=0; n!=tbdds.size(); ++n) x = x || add_bit(db&&tbdds[n],n);
	db = x, ++bits;
}

void tables::add_tbit() {
	range_clear_memo();
	sizes perm(max_args * bits + tbits);
	for (size_t n = 0; n != perm.size(); ++n) perm[n] = n + 1;
	DBG(wcout<<"before add_tbit:"<<endl<<::allsat(db, max_args*bits+tbits)<<endl;)
	db = (db ^ perm) && bdd::from_bit(0, false), ++tbits;
	DBG(wcout<<"after add_tbit:"<<endl<<::allsat(db, max_args*bits+tbits)<<endl;)
}

spbdd tables::from_row(const ints& row, ntable tab, bools *ex) {
	if (ex) *ex = bools(bits * row.size() + tbits, false);
	bdds v;
	const size_t args = row.size();
	map<int_t, size_t> vs;
	for (size_t n = 0, b; n != args; ++n) {
		if (row[n] >= 0)
			for (b = 0; b != bits; ++b) {
				v.push_back(bdd::from_bit(pos(b, n, args),
						row[n]&(1<<b)));
				if (ex) (*ex)[pos(b, n, args)] = true;
			}
		else {
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
	spbdd r = bdd_and_many(move(v));
//	DBG(wcout<<"from_row:"<<endl<<::allsat(r, max_args*bits+tbits)<<endl;)
//	DBG(wcout<<"from_row:"<<endl<<allsat(r, tab)<<endl;)
	return r;
}

ntable tables::add_table(sig_t s) {
	auto it = ts.find(s);
	if (it != ts.end()) return it->second;
	ntable nt = sigs.size();
	max_args = max(max_args, sig_len(s));
	if (!sigs.size() || sigs.size() > (size_t)(1 << (tbits-1))) add_tbit();
	spbdd t = T;
	for (size_t b = 0; b != tbits; ++b)
		t = t && bdd::from_bit(b,nt&(1<<(tbits-b-1)));
//	DBG(wcout<<"table "<<nt<<" bits: "<<tbits<<endl<<::allsat(t, max_args*bits+tbits)<<endl<<endl);
	return ts.emplace(s, nt), sigs.push_back(s), tbdds.push_back(t), nt;
}

void tables::add(ntable tab, const vector<ints>& rows) {
	if (tab >= (1 << tbits)) add_tbit();
	bdds v;
	for (const ints& i : rows) v.push_back(from_row(i, tab));
	DBG(wcout<<"before add:"<<endl<<::allsat(db, max_args*bits+tbits)<<endl;)
	db = (bdd_or_many(move(v)) && tbdds[tab]) || db;
	DBG(wcout<<"tbdd:"<<endl<<::allsat(tbdds[tab], /*max_args*bits+*/tbits)<<endl;)
	DBG(wcout<<"after add:"<<endl<<::allsat(db, max_args*bits+tbits)<<endl;)
}

sig_t tables::get_sig(const raw_term&t){return{dict.get_rel(t.e[0].e),t.arity};}
void tables::add(const vector<raw_term>& r) { for (auto x : r) add(x); }

void tables::add(const raw_term& r) {
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
	return add(get_table(r), {t});
}

ntable tables::get_table(const raw_term& t) {
	return add_table(get_sig(t));
}

void tables::out(wostream& os) {
	DBG(wcout<<"as:"<<endl<<::allsat(db, max_args*bits+tbits)<<endl;)
	sat(*this, [&os](const raw_term& t){os<<t<<endl;})(db);
}

tables::tables() : dict(*new dict_t) {}
tables::~tables() { delete &dict; }

int main() {
	bdd::init();
	raw_progs rp(L"c(y).e(x).d(x).d(z).");
//	raw_progs rp(L"c(y).e(x).e(z).");
//	raw_progs rp(L"c(y).");
//	raw_progs rp(stdin);
	tables t;
	t.add(rp.p[0].r[0].heads());
//	t.out(wcout<<endl);
	t.add(rp.p[0].r[1].heads());
//	t.out(wcout<<endl);
	t.add(rp.p[0].r[2].heads());
	t.out(wcout<<endl);
	t.add(rp.p[0].r[3].heads());
	t.out(wcout);
	bdd::onexit = true;
	return 0;
}
