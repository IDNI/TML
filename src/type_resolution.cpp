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


#ifdef TYPE_RESOLUTION

#define ever ;;

typedef map<int_t, rel> tdecl;
typedef pair<tdecl, vector<term>> rule;

void infer_types(vector<rule>& p, const map<rel, size_t>& rels) {
        map<rel, vector<rel>> m;
        for (auto r : rels) m.emplace(r.first, vector<rel>(r.second, -1));
        auto infer_var = [&m](rel r, int_t v, size_t n, tdecl& t) {
                rel& x = m[r][n];
                auto it = t.find(v);
                if (x == -1 && it == t.end()) return false;
                if (x == -1 && it != t.end()) return x = it->second, true;
                if (x != -1 && it == t.end()) return t.emplace(t[n], x), true;
                if (it->second != x) throw "type mismatch";
        };
        auto infer_rule = [&m, &infer_var](rule& r) {
                bool b = false;
                for (const term& t : r.second)
                        for (size_t n = 1; n != t.size(); ++n)
                                if (t[n] < 0) // todo: handle consts
                                        b |= infer_var(t[0],t[n-1],n-1,r.first);
                return b;
        };
        for (ever) {
                bool b = false;
                for (rule& r : p) b |= infer_types(r);
                if (!b) break;
        }
        for (const auto& x : m)
                for (rel r : x.second)
                        if (r == -1)
                                throw "dont know type of x.first";
}

void infer_types(vector<rule>& p) {
        map<rel, size_t> rels;
        set<rel> eur; // extensional unary relations
        auto move_to_head = [&eur](rule& r) {
                for (size_t n = 1; n < r.second.size(); ++n)
                        if (eur.find(r.second[n][0]) == eur.end()) continue;
                        else (auto it = r.first.find(r.second[n][1];
                                it == r.first.end()))
                                r.emplace(r.second[n][1], r.second[n][0]),
                                r.second.erase(n);
                        else if (it->second != r.second[n][0])
                                throw "type mismatch for var n";
        };

        for (rule& r : p)
                for (const term& t : r.second)
                        if (t.size() == 2) eur.insert(t.at(0));
                        // here we crucially assume that rels with different
                        // arity always have different rel id.
                        else rels[t.at(0)] = t.size() - 1;
        for (const rule& r : p)
                if (r.second.at(0).size() == 2)
                        eur.erase(r.second.at(0).at(0));
        for (rule& r : p) move_to_head(r);
        infer_types(p, rels);
}

#endif