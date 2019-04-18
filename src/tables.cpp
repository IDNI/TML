#include "tables.h"
#include "input.h"
using namespace std;
using namespace std::placeholders;

class walk {
	const tables& t;
	size_t v = 1;
	const size_t tbits;
	bools p;
public:
	typedef function<void(spbdd, ntable)> callback;
	callback f;
	walk(const tables& t, callback f);
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
	transform(const tables& t, callback f);
	spbdd operator()(spbdd x);
};

class sat {
	tables& t;
	size_t v = 1, nvars;
	bools p;
	sig_t s;
	typedef function<void(const raw_term&)> callback;
	callback f;
	walk w;
	lexeme op, cl;
	void cb(spbdd x, ntable tab);
	void run(spbdd x);
public:
	sat(tables& t, callback f);
	void operator()(spbdd x) { w(x); }
};

size_t sig_len(const sig_t& s) {
	size_t r = 0;
	for (auto x : get<1>(s)) if (x > 0) r += x;
	return r;
}

sat::sat(tables& t, sat::callback f) : t(t), p(t.tbits),
	f(f), w(t, bind(&sat::cb, this, _1, _2)),
	op(t.dict.get_lexeme(L"(")), cl(t.dict.get_lexeme(L")")) {}

void sat::cb(spbdd x, ntable tab) {
	p.resize(nvars = sig_len(s = t.sigs[tab]) * t.bits);
	run(x);
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
			else rt.e[n+1]= elem(elem::SYM, t.dict.get_sym(arg>>2));
		}
		rt.insert_parens(op, cl);
		f(move(rt));
	}
}

walk::walk(const tables& t, callback f) : t(t), tbits(t.tbits),p(t.tbits),f(f){}

void walk::operator()(spbdd x) {
	if (x->leaf() && !x->trueleaf()) return;
	if (v == t.tbits + 1) {
		ntable tab = 0;
		for (size_t n = 0; n != p.size(); ++n) if (p[n]) tab |= 1 << n;
		f(x->h(), tab), f(x->l(), tab);
	}
	else if (!x->leaf() && v < x->v())
		p[++v-2] = true, (*this)(x), p[v-2] = false, (*this)(x), --v;
	else p[++v-2]=true, (*this)(x->h()), p[v-2]=false, (*this)(x->l()), --v;
}

transform::transform(const tables& t, callback f)
	: t(t), tbits(t.tbits), p(tbits), f(f) {}

spbdd transform::operator()(spbdd x) {
	if (x->leaf() && !x->trueleaf()) return x;
	if (!x->leaf() && v == t.tbits + 1) {
		tab = 0;
		for (size_t n = 0; n != p.size(); ++n) if (p[n]) tab |= 1 << n;
		return bdd::add(x->v(), f(x->h(), tab), f(x->l(), tab));
	}
	spbdd h, l;
	if (!x->leaf() && v < x->v())
		p[++v-2] = true,h = (*this)(x),
		p[v-2] = false,	l = (*this)(x), --v;
	else	p[++v-2] = true,h = (*this)(x->h()),
		p[v-2] = false,	l = (*this)(x->l()), --v;
	return bdd::add(x->v(), h, l);
}

spbdd tables::leq_const(int_t c, size_t arg, size_t args, size_t bit) const {
	if (bit == bits) return T;
	spbdd t = leq_const(c, arg, args, bit + 1);
	return (c & (1 << bit)) ? t : bdd::add(pos(bit, arg, args), F, t);
}

spbdd tables::range(size_t arg, ntable tab) {
	array<int_t, 7> k = { syms, nums, chars, (int_t)tab, (int_t)arg,
		(int_t)bits, (int_t)tbits };
	auto it = range_memo.find(k);
	if (it != range_memo.end()) return it->second;
	const size_t args = sig_len(sigs[tab]);
	spbdd	st = leq_const(((syms-1)<<2)|3, arg, args, bits - 1),
		nt = leq_const(((nums-1)<<2)|3, arg, args, bits - 1),
		ct = leq_const(((chars-1)<<2)|3, arg, args, bits - 1),
		ischar = from_bit(pos(0, arg, args), true) &&
			from_bit(pos(1, arg, args), false),
		isnum = from_bit(pos(0, arg, args), false) &&
			from_bit(pos(1, arg, args), true),
		issym = from_bit(pos(0, arg, args), false) &&
			from_bit(pos(1, arg, args), false);
	return onmemo(), range_memo[k] = bdd_and_many({
		from_bit(pos(0, arg, args), true) ||
		from_bit(pos(1, arg, args), true),
		chars ? bdd_impl(ischar, ct): (T%ischar),
		nums ? bdd_impl(isnum, nt) : (T%isnum),
		syms ? bdd_impl(issym, st) : (T%issym)});
}

void tables::range_clear_memo() {onmemo(-range_memo.size()),range_memo.clear();}

size_t tables::pos(size_t bit, size_t nbits, size_t arg, size_t args) const {
	return tbits + ((nbits - bit - 1) * args + arg);
}

size_t tables::pos(size_t bit, size_t arg, size_t args) const {
	return tbits + ((bits - bit - 1) * args + arg);
}

size_t tables::arg(size_t v, size_t args) const {
	DBG(assert(v >= tbits);)
	return (v - tbits) % args;
}

size_t tables::bit(size_t v, size_t args) const {
	DBG(assert(v >= tbits);)
	return bits - ((v - tbits) / args) - 1;
}

void tables::add_bit() {
	range_clear_memo();
	db = transform(*this, [this](spbdd x, ntable tab) {
		const size_t args = sig_len(sigs[tab]);
		sizes perm(args * bits + tbits);
		for (size_t n = 0; n != perm.size(); ++n) perm[n] = n;
		for (size_t n = 0; n != args; ++n)
			for (size_t k = 0; k != bits; ++k)
				perm[pos(k, n, args)] = pos(k, bits+1, n, args);
		return x ^ perm;
	})(db);
	++bits;
}

void tables::add_tbit() {
	range_clear_memo();
	sizes perm(max_args * bits + tbits);
	for (size_t n = 0; n != perm.size(); ++n) perm[n] = n+1;
	db = db ^ perm, ++tbits;
}

spbdd tables::from_row(const ints& row, ntable tab, bools *ex) {
	int_t m = 0;
	for (int_t i : row) m = max(m, i);
	while (m >= (1 << bits)) add_bit();
	if (ex) *ex = bools(bits * row.size() + tbits, false);
	bdds v;
	const size_t args = row.size();
	map<int_t, size_t> vs;
	for (size_t n = 0, k, b; n != args; ++n) {
		auto it = vs.find(row[n]);
		if (it == vs.end()) vs.emplace(row[n], n);
		if (row[n] >= 0)
			for (b = 0; b != bits; ++b) {
				v.push_back(from_bit(pos(b, n, args),
						row[n]&(1<<b)));
				if (ex) (*ex)[pos(b, n, args)] = true;
			}
		else for (k = n; --k;)
			if (row[k] < 0 && row[k] == row[n]) {
				for (b = 0; b != bits; ++b) {
					v.push_back(from_eq(
						pos(b,n,args), pos(b,k,args)));
					if (ex) (*ex)[pos(b, k, args)] = true;
				}
				break;
			}
	}
	for (auto x : vs) v.push_back(range(x.second, tab));
	return bdd_and_many(move(v));
}

ntable tables::add_table(sig_t s) {
	auto it = ts.find(s);
	if (it != ts.end()) return it->second;
	spbdd t = T;
	ntable nt = ts.size();
	for (size_t b = 0; b != tbits; ++b) t = t && from_bit(b, nt & (1<<b));
	max_args = max(max_args, sig_len(s));
	return ts.emplace(s, nt), sigs.push_back(s), tbdds.push_back(t), nt;
}

void tables::add(ntable tab, const vector<ints>& rows) {
	if (tab >= (1 << tbits)) add_tbit();
	bdds v;
	for (const ints& i : rows) v.push_back(from_row(i, tab));
	db = (bdd_or_many(move(v)) && tbdds[tab]) || db;
}

sig_t tables::get_sig(const raw_term& t) {
	return { dict.get_rel(t.e[0].e), t.arity };
}

void tables::add(const vector<raw_term>& r) { for (auto x : r) add(x); }

#define mkchr(x) ((((int_t)x)<<2)|1)
#define mknum(x) ((((int_t)x)<<2)|2)

void tables::add(const raw_term& r) {
	ints t;
	for (size_t n = 1; n < r.e.size(); ++n)
		switch (r.e[n].type) {
			case elem::NUM:
				nums = max(nums, r.e[n].num);
				t.push_back(mknum(r.e[n].num)); break;
			case elem::CHR:
				chars = 256;
				t.push_back(mkchr(r.e[n].ch)); break;
			case elem::VAR: t.push_back(dict.get_var(r.e[n].e));
					break;
			case elem::OPENP:
			case elem::CLOSEP: break;
			default: t.push_back(dict.get_sym(r.e[n].e)<<2);
				 syms = max(syms, (int_t)dict.nsyms());
		}
		/*else if (r.e[n].type == elem::STR) {
			lexeme l = r.e[n].e;
			++l[0], --l[1];
			t.push_back(dict.get_sym(dict.get_lexeme(
				_unquote(lexeme2str(l)))));
		}*/
	return add(get_table(r), {t});
}

ntable tables::get_table(const raw_term& t) {
	if (sigs.size() + 1 >= (size_t)(1 << tbits)) add_tbit();
	return add_table(get_sig(t));
}

void tables::out(wostream& os) {
	sat(*this, [&os](const raw_term& t){os<<t<<endl;})(db);
}

int main() {
	bdd::init();
	raw_progs rp(L"e(1 ?x).");
	tables t;
	t.add(rp.p[0].r[0].heads());
	t.out(wcout);
	return 0;
}
