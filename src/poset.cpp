#include "poset.h"

#ifndef NOOUTPUTS
#include "output.h"
#define OUT(x) x
#else
#define OUT(x)
#endif

using namespace std;

auto abs_cmp = [](int_t a, int_t b) {
  int_t abs_a = abs(a), abs_b = abs(b);
  if (abs_a < abs_b) return true;
  if (abs_b < abs_a) return false;
  return a < b;
};

auto abs_lex_cmp = [](const std::pair<int_t,int_t>& p1, const std::pair<int_t,int_t> &p2){
  if (abs_cmp(p1.first, p2.first)) return true;
  if (p1.first == p2.first && abs_cmp(p1.second, p2.second)) return true;
  return false;
};

std::vector<PersistentUnionFind> uf_univ;
std::unordered_map<PersistentUnionFind, int_t> memo;
unordered_map<pair<int_t,int_t>,int_t> set_cache;
unordered_map<pair<int_t,pair<int_t,int_t>>,int_t> pair_cache;

size_t std::hash<PersistentUnionFind>::operator()(const PersistentUnionFind & uf) const {
  return uf.hash;
}

size_t std::hash<PersistentSet>::operator()(const PersistentSet &s) const {
  return hash_pair(s.e, s.n);
}
size_t std::hash<PersistentPairs>::operator()(const PersistentPairs &p) const {
  std::hash<std::pair<int_t,int_t>> hasher;
  return hash_pair(hasher(p.e), p.n);
}

size_t std::hash<poset>::operator()(const poset &p) const {
  return hash_tri(p.eqs, p.imps, p.vars);
}

size_t std::hash<std::pair<int_t, int_t>>::operator()(const std::pair<int_t, int_t> &p) const {
  return hash_pair(p.first, p.second);
}

size_t std::hash<std::pair<int_t, std::pair<int_t,int_t>>>::operator()(const std::pair<int_t, std::pair<int_t,int_t>> &p) const {
  return hash_pair(p.first, hash_pair(p.second.first,p.second.second));
}


int_t PersistentArray::get(storage& arr, const sppa& t, int_t pos){
  if (t->diff == nullptr){
    // Here we operate directly on the vector
    return arr[pos];
  }
  reroot(arr, t);
  DBG(assert(t->diff == nullptr));
  return arr[pos];
}

PersistentArray::sppa PersistentArray::set(storage& arr, const sppa &t, int_t pos, int_t val) {
  reroot(arr, t);
  // The hash also stays the same in this situation
  if(get(arr, t,pos)==val) return t;

  DBG(assert(t->diff == nullptr));
  int_t old_val = arr[pos];
  arr[pos] = val;
  auto res = make_shared<PersistentArray>(PersistentArray());
  t->p = pos;
  t->v = old_val;
  t->diff = res;
  return res;
}

// This function must only be called directly after a set command and not at a later point in time
void PersistentArray::undo(storage &arr, const sppa &current, const sppa &last) {
  DBG(assert(current->diff == nullptr));

  arr[last->p] = last->v;
  last->diff = nullptr;
}

void PersistentArray::reroot(storage& arr, const sppa &t){
  if(t->diff == nullptr) return;
  reroot(arr, t->diff);
  DBG(assert(t->diff->diff==nullptr));
  int_t pos = t->p;
  int_t val = arr[pos];
  arr[pos] = t->v;
  shared_ptr<p_arr> arr_pt = t->diff;

  t->p = t->diff->p;
  t->v = t->diff->v;
  t->diff = t->diff->diff;

  arr_pt->diff = t;
  arr_pt->p = pos;
  arr_pt->v = val;
}

vector<int_t> PersistentUnionFind::parent_s;
vector<int_t> PersistentUnionFind::link_s;
vector<int_t> PersistentUnionFind::hashes_s;

void PersistentUnionFind::init(int_t n) {
  if(!uf_univ.empty()) return;
  puf root = puf (n);
  uf_univ.push_back(root);
  memo.try_emplace(move(root),0);
}

int_t PersistentUnionFind::find(const puf &t, int_t elem) {
  auto t_elem = p_arr::get(parent_s, t.arr_pt,abs(elem));
  if (abs(t_elem) == abs(elem)) return elem<0?-t_elem:t_elem;
  else {
    auto r = elem<0 ? -find(t, t_elem) : find(t,t_elem);
    t.arr_pt = p_arr::set(parent_s, t.arr_pt, abs(elem), elem<0?-r:r);
    // We do not reset the hashes because those are only queried on root nodes
    return r;
  }
}

// Updates t by setting the value at x to y
// while assuming that x and y are root nodes
// y is the new parent of x
int_t PersistentUnionFind::update(const puf &t, int_t x, int_t y) {
  DBG(assert(y>=0));
  auto hash_x = p_arr::get(hashes_s, t.hash_pt, abs(x));
  auto hash_y = p_arr::get(hashes_s, t.hash_pt, y);
  auto uf = puf(p_arr::set(parent_s, t.arr_pt, abs(x), x<0?-y:y), update_link(t,x,y),
                p_arr::set(hashes_s, t.hash_pt, y, hash_set(x,y,hash_x,hash_y)),
                t.hash, x, y, hash_x, hash_y);
  return add(uf);
}

int_t PersistentUnionFind::add(puf &uf) {
  if (auto it = memo.find(uf); it != memo.end()) {
    return it->second;
  }
  else {
    uf_univ.push_back(uf);
    memo.try_emplace(move(uf),uf_univ.size()-1);
    return (int_t)uf_univ.size()-1;
  }
}

PersistentUnionFind::sppa PersistentUnionFind::update_link(const puf &t, int_t x, int_t y) {
  // y is the new parent of x
  DBG(assert(y>=0));
  int_t y_link = p_arr::get(link_s,t.link_pt,y);
  int_t x_link = p_arr::get(link_s,t.link_pt,abs(x));

  auto link1 = p_arr::set(link_s,t.link_pt,y, x<0?-x_link:x_link);
  return p_arr::set(link_s,link1,abs(x),x<0?-y_link:y_link);
}

int_t PersistentUnionFind::merge(int_t t, int_t x, int_t y) {
  auto form = [](int_t &x, int_t &y) {
    //y will hold the lower variable number
    if(abs(x) < abs(y)) swap(x,y);
    //y will be positive
    if(y < 0) x = -x, y = -y;
  };
  form(x,y);
  auto &uf = uf_univ[t];
  auto cx = puf::find(uf, x);
  auto cy = puf::find(uf, y);
  form(cx,cy);
  if (cx != cy) {
    if (abs(cy) < abs(cx)) return update(uf, cx, cy);
    else assert(false); return 0;
  }
  else return t;
}

int_t PersistentUnionFind::int_tersect(int_t t1, int_t t2) {
  if (t1 == t2) return t1;
  else if (t1 == 0 || t2 == 0) return 0;

  static map<pair<int_t,int_t>, vector<int_t>> eq_classes;
  eq_classes.clear();

  auto &uf1 = uf_univ[t1];
  auto &uf2 = uf_univ[t2];

  // Make uf1 root, so we check the diff path from uf2
  p_arr::reroot(parent_s, uf1.arr_pt);
  weak_ptr<p_arr> diff_pt = uf2.arr_pt;

  vector<pair<int_t,int_t>> diffs;
  while(diff_pt.lock()->diff != nullptr) {
    auto el = make_pair(diff_pt.lock()->p,0);
    if(!binary_search(diffs.begin(),diffs.end(),el)) {
      diffs.emplace_back(move(el));
      sort(diffs.begin(),diffs.end());
    }
    diff_pt = diff_pt.lock()->diff;
  }

  for (auto &el : diffs) {
    el.second = find(uf1, el.first);
  }

  int_t result = t2;
  for (auto &el : diffs) {
    // Now create equivalence pairs
    int_t eq_class_uf2 = find(uf2,el.first);
    if(el.first == el.second || el.first == eq_class_uf2) {
      // Element is set representative --> no further equality possible in intersection
      t2 = remove(t2, el.first);
    }
    if(el.second < 0) {
      eq_classes[{-el.first,-eq_class_uf2}].emplace_back(-el.first);
    } else {
      eq_classes[{el.first,eq_class_uf2}].emplace_back(el.first);
    }
  }

  for (const auto& p : eq_classes) {
    // Remove singletons
    if (p.second.size() == 1) t2 = remove(t2,p.second[0]);
    // Merge equivalence classes --> already done?!
    //else if (p.second.size() > 1) {
    //  for(const auto& el : p.second)
    //    merge(t2,p.second[0],el);
    //}
  }
  return result;
}

bool PersistentUnionFind::equal(int_t t, int_t x, int_t y) {
  auto &uf = uf_univ[t];
  return find(uf, x) == find(uf, y);
}

bool PersistentUnionFind::operator==(const puf& uf) const {
  //Quickcheck hashes
  if(hash != uf.hash) return false;
  // First reroot and then check the diff path from one to another
  p_arr::reroot(parent_s, arr_pt);
  weak_ptr<p_arr> diff_pt = uf.arr_pt;

  vector<pair<int_t,int_t>> diffs;
  while(diff_pt.lock()->diff != nullptr) {
    auto el = make_pair(diff_pt.lock()->p,0);
    if(!binary_search(diffs.begin(),diffs.end(),el)) {
      diffs.emplace_back(move(el));
      sort(diffs.begin(),diffs.end());
    }
    //if(find(uf, diff_pt.lock()->p) != find(*this, arr_pt->p)) return false;
    diff_pt = diff_pt.lock()->diff;
  }
  for (auto &el : diffs) {
    el.second = find(*this, el.first);
  }
  return all_of(diffs.begin(),diffs.end(),
                [&](pair<int_t,int_t> &el){ return find(uf, el.first) == el.second; });
}

template <typename T>
basic_ostream<T> PersistentUnionFind::print_t(int_t uf, basic_ostream<T> &os) {
  auto &t = uf_univ[uf];
  for (int_t i = 0; i < (int_t)p_arr::size(parent_s); ++i) {
    os << i << " ";
  } os << endl;
  for (int_t i = 0; i < (int_t)p_arr::size(parent_s); ++i){
    os << p_arr::get(parent_s, t.arr_pt, i) << " ";
  } os << endl;
  for (int_t i = 0; i < (int_t)p_arr::size(parent_s); ++i){
    os << p_arr::get(hashes_s, t.hash_pt, i) << " ";
  }
  os << endl << "Hash: " << t.hash << endl;
  os << endl << endl;
}

//Returns a vector of all equal elements to x including x in t
std::vector<int_t> PersistentUnionFind::get_equal(int_t t, int_t x) {
  auto &uf = uf_univ[t];
  int_t rep_x = find(uf,x);

  vector<int_t> set {};
  bool negate = false;
  //Go down linked list and negate rest of chain if - is encountered
  int_t next = rep_x;
  do{
    if (next < 0) negate = !negate;
    next = p_arr::get(link_s, uf.link_pt, abs(next));
    set.push_back(negate ? -next : next);
  } while (abs(next) != abs(rep_x));
  return move(set);
}

// Removes the set of equal elements from t
int_t PersistentUnionFind::rm_equal(int_t t, int_t x) {
  auto reset = [&](int_t pos, puf& uf) {
    uf.arr_pt = p_arr::set(parent_s,uf.arr_pt,pos,pos);
    uf.link_pt = p_arr::set(link_s,uf.link_pt,pos,pos);
    uf.hash_pt = p_arr::set(hashes_s,uf.hash_pt,pos,0);
  };

  //Create copy of current union find and remove from their
  auto uf  = uf_univ[t];
  int_t rep_x = find(uf,x);
  int_t hash_rm = p_arr::get(hashes_s, uf.hash_pt, abs(rep_x));
  // Nothing to remove
  if(abs(rep_x) == abs(p_arr::get(link_s,uf.link_pt,abs(rep_x)))) return t;

  int_t next = rep_x;
  do{
    int_t tmp = p_arr::get(link_s, uf.link_pt, abs(next));
    reset(abs(next), uf);
    next = tmp;
  } while(abs(rep_x) != abs(next));
  uf.hash -= hash_rm;

  return add(uf);
}

bool PersistentUnionFind::resize(int_t n) {
  if(p_arr::size(parent_s) <= n) return false;

  p_arr::resize(parent_s, n, [](int_t i) { return i; });
  p_arr::resize(link_s,n,[](int_t i) { return i; });
  p_arr::resize(hashes_s, n, [](int_t i) { return 0; });
  return true;
}

int_t PersistentUnionFind::size() {
  return p_arr::size(parent_s);
}

bool PersistentSet::operator==(const PersistentSet & s) const {
  return e==s.e && n == s.n;
}

int_t PersistentSet::add(setuniv u, setmemo m, int_t e, int_t n) {
  PersistentSet set = PersistentSet(e, n);
  if(auto it = m.find(set); it != m.end()) return it->second;
  else return m.emplace(set, u.size()), u.emplace_back(set), (int_t)u.size()-1;
}

bool PersistentSet::empty(int_t set_id) {
  return set_id == 0;
}

void PersistentSet::init(setuniv u, setmemo m) {
  u.emplace_back(PersistentSet(0, 0));
  m.emplace(PersistentSet(0, 0), 0);
}

int_t PersistentSet::next(setuniv u, int_t set_id) {
  return u[set_id].n;
}

bool PersistentSet::contains(setuniv u, int_t set_id, int_t elem) {
  while (set_id != 0) {
    if (u[set_id].e == elem) return true;
    set_id = next(u, set_id);
  }
  return false;
}

int_t PersistentSet::insert(setuniv u, setmemo m, int_t set_id, int_t elem) {
  if (auto it = set_cache.find(make_pair(set_id,elem)); it!=set_cache.end())
    return it->second;
  int_t el = u[set_id].e;
  if (el == elem) return set_id;

  int_t r;
  if (abs(el) == abs(elem)) r = 0;
  else if(abs_cmp(el,elem)) r = add(u, m,elem, set_id);
  else r = add(u, m, el, insert(u, m, u[set_id].n, elem));

  set_cache.emplace(make_pair(set_id,elem),r);
  return r;
}

int_t PersistentSet::remove(setuniv u, setmemo m, int_t set_id, int_t elem) {
  int_t el = u[set_id].e;
  if (el == elem) return u[set_id].n;
  // In this case the element does not belong to the set
  else if (abs_cmp(el,elem)) return set_id;
  else return add(u, m, el, remove(u, m, u[set_id].n, elem));
}

void PersistentSet::print_t(setuniv u, int_t set_id) {
  std::cout << "{";
  while(set_id != 0) {
    std::cout << u[set_id].e;
    set_id = next(u, set_id);
    if(set_id!=0) std::cout << ", ";
  }
  std::cout << "}" << std::endl << std::endl;
}

int_t PersistentSet::find(setuniv u, int_t set_id, int_t elem) {
  while(set_id != 0) {
    if (u[set_id].e == elem) return set_id;
    set_id = next(u, set_id);
  }
  return 0;
}


bool PersistentPairs::operator==(const PersistentPairs &p) const {
  return (e == p.e && n == p.n);
}

// Canonicity with negation is ensured by having the larger variable first
int_t PersistentPairs::add(pairuniv u, pairmemo m, pair<int_t, int_t> &e, int_t n) {
  PersistentPairs pair = PersistentPairs(form(e),n);
  if(auto it = m.find(pair); it != m.end()) return it->second;
  else return m.emplace(pair, u.size()), u.emplace_back(pair), (int_t)u.size()-1;
}

void PersistentPairs::init(pairuniv u, pairmemo m) {
  u.emplace_back(PersistentPairs({0,0}, 0));
  m.emplace(PersistentPairs({0,0}, 0), 0);
}

int_t PersistentPairs::insert(pairuniv u, pairmemo m, int_t set_id, pair<int_t, int_t> &elem) {
  elem = form(elem);
  if (auto it = pair_cache.find(make_pair(set_id,elem)); it!=pair_cache.end())
    return it->second;
  int_t r;
  auto& el = u[set_id].e;
  if (el == elem) r = set_id;
  else if(abs_lex_cmp(el,elem)) r = add(u, m,elem, set_id);
  else r = add(u, m, el, insert(u, m, u[set_id].n, elem));

  pair_cache.emplace(make_pair(set_id,elem),r);
  return r;
}

int_t PersistentPairs::remove(pairuniv u, pairmemo m, int_t set_id, pair<int_t, int_t> &elem) {
  elem = form(elem);
  auto& el = u[set_id].e;
  if (el == elem) return u[set_id].n;
  // In this case the element does not belong to the set
  else if (abs_lex_cmp(el,elem)) return set_id;
  else return add(u, m, el, remove(u, m, u[set_id].n, elem));
}

bool PersistentPairs::empty(int_t set_id) {
  return set_id == 0;
}

bool PersistentPairs::contains(pairuniv u, int_t set_id, pair<int_t, int_t> &elem) {
  elem = form(elem);
  while (set_id != 0) {
    if (u[set_id].e == elem) return true;
    set_id = next(u, set_id);
  }
  return false;
}

std::vector<int_t> PersistentPairs::implies(pairuniv u, int_t set_id, int_t elem) {
  vector<int_t> imp;
  while (set_id != 0) {
    auto &p = u[set_id].e;
    if (p.first == elem) imp.emplace_back(p.second);
    else if (-p.second == elem) imp.emplace_back(-p.first);
    set_id = next(u,set_id);
  }
  return move(imp);
}

int_t PersistentPairs::next(pairuniv u, int_t set_id) {
  return u[set_id].n;
}

void PersistentPairs::print_t(pairuniv u, int_t set_id) {
  std::cout << "{";
  while(set_id != 0) {
    auto& p = u[set_id].e;
    std::cout << "{" + to_string(p.first) + "," + to_string(p.second) + "}";
    set_id = next(u, set_id);
    if(set_id != 0) std::cout << ", ";
  }
  std::cout << "}" << std::endl << std::endl;
}

pair<int_t,int_t> PersistentPairs::form(pair<int_t, int_t> &p) {
  return abs_cmp(p.first, -p.second) ? move(make_pair(-p.second,-p.first)) : move(p);
}













