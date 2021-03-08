#include "bdd.h"
#include <vector>
#include <iostream>
#include <cstdlib>
#include <algorithm>
#include <random>
#include <fstream>
#include <sstream>
#include <string>
using namespace std;

typedef vector<int_t> clause;
typedef vector<clause> cnf;

template<typename T> bool subset(const set<T>& big, const set<T>& small) {
	for (const T& t : small)
		if (big.find(t) == big.end())
			return false;
	return true;
}

size_t get_nvars(const cnf& x) {
	size_t n = 0;
	for (const clause& c : x)
		for (int_t i : c)
			n = max(n, (size_t)abs(i));
	cerr << " vars: " << n << endl;
	return n;
}

vector<pair<int_t, set<size_t>>> varsmap(const cnf& x, size_t nvars) {
	vector<pair<int_t, set<size_t>>> r(nvars);
	for (size_t n = 0; n != nvars; ++n)
		r[n].first = n+1;
	for (size_t n = 0; n != x.size(); ++n) {
		for (int_t v : x[n])
			r[abs(v)-1].second.insert(n);
	}
	std::sort(r.begin(), r.end(), [&f = x](const auto& x, const auto& y) {
		int px, nx, py, ny;
		px=nx=py=ny=0;
		for (size_t i : x.second)
			for (int_t v : f[i])
				if (abs(v) == x.first)
					(v < 0 ? nx : px)++;
		for (size_t i : y.second)
			for (int_t v : f[i])
				if (abs(v) == y.first)
					(v < 0 ? ny : py)++;
		return abs(px-nx) < abs(py-ny);
		return x.second.size() > y.second.size(); });
	return r;
}

spbdd_handle from_cnf(const clause& c) {
	spbdd_handle r = hfalse;
	for (int_t i : c) r = r || from_bit(abs(i), i > 0);
	return r;
}

spbdd_handle and_many_ex(bdd_handles v, const bools& ex) {
	return bdd_and_many_ex(v, ex);
	if (v.size() <= 5) return bdd_and_many_ex(v, ex);
	vector<bdd_handles> t;
	for (size_t n = 0; n != v.size(); ++n) {
		if (!(n % 5)) t.emplace_back();
		t.back().push_back(v[n]);
	}
	bdd_handles r;
	for (const auto& b : t) r.push_back(bdd_and_many_ex(b, ex)), (cerr << '*').flush();
	cerr<<endl;
	return and_many_ex(r, ex);
}

spbdd_handle from_cnf(cnf& f) {
	bdd_handles v, y;
	spbdd_handle r = htrue;
	size_t nvars = get_nvars(f), step = 1;
	set<size_t> cum;
	vector<pair<int_t, set<size_t>>> vm = varsmap(f, nvars);
	map<int_t, int_t> m;
	for (size_t n = 0; n != vm.size(); ++n) m[n+1] = vm[n].first;
	for (clause& c : f)
		for (int_t& v : c)
			v = v > 0 ? m[v] : -m[-v];
	vm = varsmap(f, nvars);
	for (const clause& c : f) v.push_back(from_cnf(c));
	return bdd_and_many(v);

	for (size_t n = 0; n != vm.size(); ++n) {
		if (!vm[n].second.size()) continue;
		bools b(nvars, 0);
		b[vm[n].first] = 1;
		for (size_t k : vm[n].second) 
			if (cum.insert(k).second)
				y.push_back(v[k]);
		for (size_t k = n + 1; k < vm.size(); ++k)
			if (subset(cum, vm[k].second))
				vm[k].second.clear(), b[vm[k].first] = 1;
		cerr << step++ << ' ' << y.size() << endl;
		if (y.empty()) continue;
		y.push_back(r);
		r = and_many_ex(move(y), b);
		y.clear();
	}
	return r;
}

spbdd_handle from_cnf_slow(const cnf& f) {
	spbdd_handle r = from_bit(0, true);
	for (const clause& c : f) r = r && from_cnf(c);
	return r;
}

void print(const clause& c) {
	for (int_t i : c) cout << i << '\t';
	cout << " 0" << endl;
}

void print(const cnf& f) { for (const clause& c : f) print(c); cout << endl; }

void print(cr_spbdd_handle x, size_t nvars) {
	allsat_cb(x, nvars, [](bools b, int_t) {
		b.erase(b.begin());
		for (bool x : b) cout << (x ? '1' : '0');
		cout << endl;
	});
}

size_t get_rnd() {
	return random();
	static random_device rd;
	static mt19937 gen(rd());	 
	static negative_binomial_distribution<> d(50, .5);
	return d(gen);
}

cnf dimacs(string fname) {
	cnf r;
	ifstream is(fname);
	string l;
	int_t n;
	char c;
	while (getline(is, l)) {
		istringstream iss(l);
		c = iss.peek();
		if ((c = iss.peek()), (c == 'p' || c == 'c')) continue;
		r.emplace_back();
		while (iss >> n && n) r.back().push_back(n);
	}
	cerr << "clauses: " << r.size();
	return r;
}

cnf random_cnf(size_t nvars, size_t nclauses, size_t k) {
	int v;
	set<set<int_t>> s;
	for (size_t n = 0; n != nclauses; ++n) {
		set<int_t> c;
		for (size_t m = 0; m != k; ++m) {
			do { v = (get_rnd() % nvars) + 1; }
			while (c.find(v) != c.end());
			c.insert((get_rnd() % 2) ? v : -v);
		}
		s.insert(c);
	}
	cnf r;
	for (auto& c : s) r.emplace_back(c.begin(), c.end());
	return r;
}

int main(int argc, char** argv) {
	if (argc != 4 && argc != 2) {
		cout << "usage: <nvars> <nclauses> <k>" << endl;
		return 0;
	}
	srand(time(0));
	bdd::init(MMAP_NONE, 20000, "");
	size_t n = 0;
//	for (;;) 
	{
		cnf f = argc == 4 ? random_cnf(atoi(argv[1]), atoi(argv[2]), atoi(argv[3])) : dimacs(argv[1]);
		cnf g = f;
		//print(f);
		spbdd_handle r, s;
		clock_t start, end;
		measure_time(r = from_cnf(f));
		cerr << ++n << ' ';
		if (r == hfalse) cerr << "unsat" << endl;
		else cerr << "sat" << endl;
		cerr<<"slow:\t";
		measure_time(s = from_cnf_slow(f));

		assert((r == hfalse) == (hfalse == s));
	}
	return 0;
}
