#include "persistent_dag.h"

using namespace std;

using pd = persistent_dag;
using ps = persistent_set;
using pu = persistent_union_find;

static std::vector<pd> dag_univ;
static std::unordered_map<pd, int_t> dag_memo;

static unordered_map<int_t, int_t> get_elements;
static unordered_map<int_t, int_t> G;

size_t std::hash<persistent_dag>::operator()(const pd &dag) const {
	return hash_tri(dag.var, dag.sh, dag.sl);
}

namespace { abs_cmp_ abs_cmp; }

int_t pd::find(int_t root_id, int_t elem) {
	vector<int_t> visited;
	int_t r = find(root_id, elem, visited);
	return r;
}

// Simple Depth-First search for elem in DAG denoted by root_id
int_t pd::find(int_t root_id, int_t elem, vector<int_t> &visited) {
	assert(root_id >= 0);
	const auto& root = dag_univ[root_id];
	if(root.var == abs(elem)) return elem < 0 ? -root_id : root_id;
	if(binary_search(all(visited), root_id)) return 0;

	int_t r = 0;
	visited.insert(lower_bound(all(visited), root_id), root_id);
	int_t pos = root.sh;
	while(pos != 0 && r == 0) {
		r = find(abs(ps::get(pos).e), elem, visited);
		pos = ps::next(pos);
	}
	pos = root.sl;
	while(pos != 0 && r == 0) {
		r = find(abs(ps::get(pos).e), elem, visited);
		pos = ps::next(pos);
	}
	return r;
}

bool pd::operator==(const pd& dag) const {
	return var == dag.var && sh == dag.sh && sl == dag.sl;
}

void pd::form(pair<int_t, int_t> &p) {
	form(p.first, p.second);
}

void pd::form(int_t &fst, int_t &snd) {
	if(!abs_cmp(fst,snd)) {
		int_t tmp = fst;
		fst = -snd;
		snd = -tmp;
	}
}

// Initializes Union Find and Set data structure while setting up the DAG universe
void pd::init(int_t n) {
	ps::init();
	pu::init(n);
	dag_univ.emplace_back();
	dag_memo.emplace(pd(), 0);
}

int_t pd::add(int_t v, int_t suc_high, int_t suc_low) {
	assert(v >= 0);
	auto dag = pd(v, suc_high, suc_low);
	if (auto it = dag_memo.find(dag); it != dag_memo.end()) return it->second;
	dag_univ.emplace_back(dag);
	dag_memo.emplace(dag, (int_t) dag_univ.size() - 1);
	return (int_t) dag_univ.size() - 1;
}

int_t pd::insert(int_t dag_id, int_t fst, int_t snd, vector<int_t> &sings,
		 vector<int_t> &eqs) {
	// We can only insert into the root of a dag
	assert(dag_univ[dag_id].var == 0);

	// Either trivial insertion or insertion of singleton
	if (abs(fst) == abs(snd)) {
		if (fst == -snd) {
			insertb(sings, -fst);
			dag_id = set_var(dag_id, -fst, sings);
		}
		return dag_id;
	}

	// Ensure canonical form
	form(fst, snd);
	int_t component_set_id = dag_univ[dag_id].sh;

	return analyze_component(component_set_id, fst, snd, dag_id,
				 sings, eqs);
}

// Returns a new dag_root
int_t
pd::analyze_component(int_t set_id, int_t fst, int_t snd, int_t dag_root,
		      std::vector<int_t> &sings, std::vector<int_t> &eqs) {
	if(set_id == 0) return insert_component(dag_root, fst, snd);

	int_t component = ps::get(set_id).e;
	int_t uf_id = get_elements[component];
	assert(uf_id != 0);
	if(pu::equal(uf_id, abs(fst), abs(snd))) {
		//Create temporary non-persistent representation of component
		create_graph_G(component);
		// Check if fst and snd are on same branch
		if (existsPath_G(fst, snd)) return G.clear(), dag_root;
		// fst and snd are on different branches
		vector<int_t> suc_snd;
		all_suc_G(snd, suc_snd);
		// Check for singleton extraction
		if(int_t conflicts = is_singleton_G(component, suc_snd, fst, snd); conflicts != 0) {
			for (; conflicts != 0; conflicts = ps::next(conflicts))
				set_var_G(-ps::get(conflicts).e, sings);
			return make_persistent_G(dag_root, component);
		}
		// Check for equality extraction
		if (hasbc(suc_snd, fst, abs_cmp)) {
			// Adding fst -> snd introduces a loop
			do {
				remove_loop_G(snd, fst, eqs);
				// Check for additional loops
			} while (existsPath_G(snd, fst));
			return make_persistent_G(dag_root, component);
		}
		// Check for transitive reduction
		transitive_reduction_G(fst, suc_snd);
		G[fst] = ps::insert(G[fst], snd);
		return make_persistent_G(dag_root, component);
	}
	if (!pu::is_singleton(uf_id, fst)) {
		// fst is in component but not snd
		// See if snd is on different component
		auto r = find_in_dag(ps::next(set_id), snd);
		if (r != 0) return connect_components(dag_root, component, r, fst, snd);

		int_t fst_id = find(component, fst);
		int_t snd_id = add(abs(snd), 0, 0);
		snd_id = snd < 0 ? -snd_id : snd_id;
		int_t original_component = component;
		int_t res = plain_insert_edge(fst_id, snd_id, dag_root, component);
		get_elements[component] = add_to_component(original_component, fst, snd);
		return res;
	}
	if (!pu::is_singleton(uf_id, snd)) {
		// snd is in component but fst is not
		// See if fst is on different component
		auto r = find_in_dag(ps::next(set_id), fst);
		if (r != 0) return connect_components(dag_root, r, component, fst, snd);

		int_t snd_id = find(component, snd);
		int_t fst_id = add(abs(fst), fst < 0 ? 0 : ps::insert(0, snd_id),
				   fst < 0 ? ps::insert(0, snd_id) : 0);
		fst_id = fst < 0 ? -fst_id : fst_id;
		int_t original_component = component;
		int_t res = insert_root_node(dag_root, component, fst_id);
		get_elements[component] = add_to_component(original_component, fst, snd);
		return res;
	}
	return analyze_component(ps::next(set_id), fst, snd, dag_root, sings, eqs);
}

// Assume that fst is on comp_source and snd on comp_dest
int_t pd::connect_components(int_t dag_root, int_t &comp_source, int_t comp_dest, int_t fst, int_t snd) {
	int_t fst_id = find(comp_source, fst);
	int_t snd_id = find(comp_dest, snd);
	int_t comp_source_original = comp_source;
	//Put snd_id on comp_source
	dag_root = plain_insert_edge(fst_id, snd_id, dag_root, comp_source);
	//Add all roots from comp_dest to comp_source except snd_id
	for(int_t root_id = dag_univ[comp_dest].sh; root_id != 0; root_id = ps::next(root_id))
		if(root_id != snd_id) dag_root = insert_root_node(dag_root, comp_source, ps::get(root_id).e);

	//Remove comp_dest from dag_root
	int_t new_root = ps::remove(dag_univ[dag_root].sh, comp_dest);
	get_elements[comp_source] = add_to_component(comp_source_original, abs(fst), abs(snd));
	return add(0, new_root, 0);
}

int_t pd::find_in_dag(int_t component_set, int_t elem) {
	int_t uf_id;
	while(component_set != 0){
		uf_id = get_elements[ps::get(component_set).e];
		if(!pu::is_singleton(uf_id, elem)) return ps::get(component_set).e;
		else component_set = ps::next(component_set);
	}
	return 0;
}

int_t pd::insert_root_node(int_t dag_root, int_t &component, int_t node_id) {
	int_t component_set = ps::remove(dag_univ[dag_root].sh, component);
	component = add(0,ps::insert(dag_univ[component].sh, node_id),0);
	component_set = ps::insert(component_set, component);
	return add(0, component_set, 0);
}

int_t pd::plain_insert_edge(int_t node_id, int_t suc_id, int_t dag_root, int_t &component) {
	int_t upd_node = insert_suc(node_id, suc_id);
	return update_root_dag(dag_root, component, node_id, upd_node);
}

int_t pd::update_root_dag(int_t root_id, int_t &component, int_t old_node, int_t new_node) {
	auto const& dag_root = dag_univ[root_id];
	assert(dag_root.var == 0);
	int_t new_comp_set = ps::remove(dag_root.sh, component);
	component = update(abs(old_node), abs(new_node), component);
	return add(0, ps::insert(new_comp_set, component), 0);
}

int_t pd::update(int_t old_node, int_t new_node, int_t component) {
	assert(old_node != 0 && component != 0);
	if(old_node == abs(component)) { return component < 0 ? -new_node : new_node; }
	auto const comp = dag_univ[abs(component)];
	if(dag_univ[abs(old_node)].var < comp.var) { return component; }
	assert(!(comp.var == 0 && comp.sh == 0 && comp.sl == 0));
	if(comp.sh == 0 && comp.sl == 0) { return component; }

	int_t new_suc_h = 0;
	int_t old_suc = comp.sh;
	while(old_suc != 0) {
		new_suc_h = ps::insert(new_suc_h, update(old_node, new_node, ps::get(old_suc).e));
		old_suc = ps::next(old_suc);
	}

	int_t new_suc_l = 0;
	old_suc = comp.sl;
	while(old_suc != 0) {
		new_suc_l = ps::insert(new_suc_l, update(old_node, new_node, ps::get(old_suc).e));
		old_suc = ps::next(old_suc);
	}

	return component < 0 ? -add(comp.var, new_suc_h, new_suc_l) : add(comp.var, new_suc_h, new_suc_l);
}

// Set a variable given the node id
void pd::set_var_G(int_t var, std::vector<int_t> &sings) {
	int_t suc = G[var];
	int_t pred = G[-var];
	// Remove var from graph
	G.erase(var);
	// Remove all contra positions
	G.erase(-var);
	if(!hasb(sings, var))
		insertb(sings, var);
	// Remove all predecessor implications
	while (pred != 0) {
		G[-ps::get(pred).e] = ps::remove(G[-ps::get(pred).e], var);
		pred = ps::next(pred);
	}
	//Set all implied variables
	while (suc != 0) {
		set_var_G(ps::get(suc).e, sings);
		suc = ps::next(suc);
	}
}

void pd::transitive_reduction_G(int_t fst, const vector<int_t> &suc_snd) {
	vector<int_t> preds;
	all_pred_G(fst, preds);
	for(const auto& el : preds) {
		int_t suc = G[el];
		// Intersect immediate successors and suc_snd and perform transitive reduction
		while(suc != 0) {
			int_t s = ps::get(suc).e;
			if(hasbc(suc_snd, s, abs_cmp)){
				//Remove edge from el to node contained in suc_snd
				G[el] = ps::remove(G[el], s);
				G[-s] = ps::remove(G[-s], -el);
			}
			suc = ps::next(suc);
		}
	}
}

// Assumes that fst and snd do not appear in any other component
int_t pd::insert_component(int_t root, int_t fst, int_t snd) {
	int_t snd_id = add(abs(snd), 0, 0);
	snd_id = snd < 0 ? -snd_id : snd_id;
	int_t fst_id = add(abs(fst), fst < 0 ? 0 : ps::insert(0, snd_id),
			   fst < 0 ? ps::insert(0, snd_id) : 0);
	fst_id = fst < 0 ? -fst_id : fst_id;
	int_t component = add(0, ps::insert(0,fst_id), 0);
	get_elements[component] = add_to_component(component, fst, snd);
	return insert_suc(root, component);
}

int_t pd::insert_suc(int_t node_id, int_t suc_id) {
	const auto& n = get(node_id);
	if(n.var < 0)
		return -add(abs(n.var), n.sh, ps::insert(n.sl, suc_id));
	else
		return add(n.var, ps::insert(n.sh, suc_id), n.sl);
}

void pd::remove_loop_G(int_t origin, int_t dest, vector<int_t> &eqs) {
	vector<int_t> path, visited;
	find_path_G(origin, dest, visited, path);
	path.push_back(origin);
	for (int_t i = path.size()-1; i > 0; --i) {
		G[-path[i-1]] = ps::remove(G[-path[i-1]], -path[i]);
		G[path[i]] = ps::remove(G[path[i]], path[i-1]);
		check_insertb(eqs, path[i]);
	}
	if(!path.empty()){
		G[-path[path.size()-1]] = ps::remove(G[-path[path.size()-1]], -path[0]);
		G[path[0]] = ps::remove(G[path[0]], path[path.size()-1]);
	}
	if(!path.empty() && !hasb(eqs, path[0]))
		insertb(eqs, path[0]);
}

int_t
pd::is_singleton_G(int_t component, vector<int_t> &suc_snd, int_t fst, int_t snd) {
	for(int_t root = get(component).sh; root != 0; root = ps::next(root)){
		vector<int_t> suc_root;
		all_suc_G(get(ps::get(root).e).var, suc_root);
		auto iter_root = suc_root.rbegin();
		auto iter_snd = suc_snd.rbegin();

		while (iter_root != suc_root.rend() && iter_snd != suc_snd.rend()) {
			if (abs(*iter_root) > abs(*iter_snd)) {
				++iter_root;
			} else {
				if (abs(*iter_snd) <= abs(*iter_root)) {
					// Here equality
					if (-*iter_snd == *iter_root) {
						// Find all preds of *iter_snd and *iter_root and intersect them

						G[fst] = ps::insert(G[fst], snd);
						G[-snd] = ps::insert(G[-snd], -fst);
						return intersection_preds(*iter_snd, *iter_root);
					}
					++iter_root;
				}
				++iter_snd;
			}
		}
	}
	return 0;
}

bool pd::find_path_G(int_t origin, int_t dest, vector<int_t> &visited, vector<int_t> &path) {
	int_t suc = G[origin];
	while(suc != 0){
		int_t el = ps::get(suc).e;
		if(el == dest) return path.push_back(el), true;
		if(!binary_search(all(visited), el)){
			visited.insert(lower_bound(all(visited), el), el);
			if(find_path_G(el, dest, visited, path))
				return path.push_back(el), true;
		}
		suc = ps::next(suc);
	}
	return false;
}

int_t
pd::insert(int_t dag_id, std::pair<int_t, int_t> &elem, vector<int_t> &sings,
	   vector<int_t> &eqs) {
	return insert(dag_id, elem.first, elem.second, sings, eqs);
}

pd pd::get(int_t dag_id) {
	assert(abs(dag_id) < dag_univ.size());
	auto p = dag_univ[abs(dag_id)];
	p.var = dag_id < 0 ? -p.var : p.var;
	return p;
}

bool pd::is_leaf(int_t dag_id) {
	const auto& node = get(dag_id);
	return node.sh == 0 && node.sl == 0;
}

int_t pd::add_to_component(int_t component, int_t v, int_t w) {
	int_t t = get_elements[component];
	return pu::merge(t, abs(v), abs(w));
}

void pd::print(int_t root_id, ostream &os) {
	const auto& root = get(root_id);
	if(root.sh == 0 && root.sl == 0) return;

	int_t pos = root_id > 0 ? root.sh : root.sl;
	if(pos != 0) os << "(" << root.var << ", " << abs(root_id) << ")" << " --> ";
	bool first = true;
	while(pos != 0) {
		if(first) first = false, os << "[" << "(" << pd::get(ps::get(pos).e).var << ", " << ps::get(pos).e << ")";
		else os << ", " << "(" << pd::get(ps::get(pos).e).var << ", " << ps::get(pos).e << ")";
		pos = ps::next(pos);
	}
	if(!first) os << "]" << endl;

	pos = root_id > 0 ? root.sh : root.sl;
	while(pos != 0) {
		print(ps::get(pos).e, os);
		pos = ps::next(pos);
	}
}

int_t pd::set_var(int_t root_id, int_t var, std::vector<int_t> &sings) {
	// Setting a variable on an empty DAG
	if(root_id == 0) return 0;

	assert(root_id > 0);
	const auto& root = get(root_id);
	int_t component = find_in_dag(root.sh, var);
	assert(component >= 0);
	if(component == 0) return root_id;

	create_graph_G(component);
	set_var_G(var, sings);

	return make_persistent_G(root_id, component);
}

void
pd::create_graph_G(int_t component) {
	auto add_edge = [](int_t node_var, int_t x) {
	    int_t v = get(ps::get(x).e).var;
	    G[node_var] = ps::insert(G[node_var], v);
	    G[-v] = ps::insert(G[-v], -node_var);
	};

	if(is_leaf(component)) return;
	const auto& node = get(component);
	int_t suc = node.sh;
	while(suc != 0){
		if(node.var != 0) add_edge(abs(node.var), suc);
		create_graph_G(ps::get(suc).e);
		suc = ps::next(suc);
	}
	suc = node.sl;
	while(suc != 0){
		if(node.var != 0) add_edge(-abs(node.var), suc);
		create_graph_G(ps::get(suc).e);
		suc = ps::next(suc);
	}
}

void pd::all_suc_G(int_t var, vector<int_t> &sucs) {
	int_t suc = G[var];
	insertbc(sucs, var, abs_cmp);
	while(suc != 0){
		if(!hasbc(sucs, ps::get(suc).e, abs_cmp)) {
			all_suc_G(ps::get(suc).e, sucs);
		}
		suc = ps::next(suc);
	}
}

void pd::all_pred_G(int_t var, vector<int_t> &preds) {
	int_t pred = G[-var];
	while(pred != 0){
		if(!hasbc(preds, -ps::get(pred).e, abs_cmp)) {
			insertbc(preds, -ps::get(pred).e, abs_cmp);
			all_pred_G(-ps::get(pred).e, preds);
		}
		pred = ps::next(pred);
	}
}

bool pd::existsPath_G(int_t origin, int_t dest, vector<int_t> &visited) {
	int_t suc = G[origin];
	while(suc != 0){
		int_t el = ps::get(suc).e;
		if(el == dest) return true;
		if(!binary_search(all(visited), el)){
			visited.insert(lower_bound(all(visited), el), el);
			if(existsPath_G(el, dest, visited)) return true;
		}
		suc = ps::next(suc);
	}
	return false;
}

// This version takes care of possible component splits due to equality removal
int_t pd::make_persistent_G(int_t dag_id, int_t component) {
	int_t root_set = 0;
	vector<int_t> visited;

	int_t component_set = ps::remove(get(dag_id).sh, component);
	for(auto [var, imp] : G) {
		if(hasb(visited, abs(var))) continue;
		// Get roots of component represented by var and create new component for the current DAG
		int_t component_roots = 0, comp_sh = 0, equality_set = 0;
		get_component_roots_G(var, visited, component_roots);
		for (; component_roots != 0; component_roots = ps::next(component_roots)) {
			comp_sh = ps::insert(comp_sh, make_persistent_node(ps::get(component_roots).e, equality_set, var));
		}
		//Insert new component into current DAG
		if(comp_sh != 0){
			int_t new_comp = add(0, comp_sh, 0);
			component_set = ps::insert(component_set, new_comp);
			get_elements[new_comp] = equality_set;
		}
	}

	G.clear();
	return add(0, component_set, 0);
}

int_t pd::make_persistent_node(int_t var, int_t &eq, int_t rep) {
	eq = pu::merge(eq, abs(rep), abs(var));

	int_t imp = G[var];
	int_t pos_set = 0;
	while(imp != 0){
		if(abs_cmp(var, ps::get(imp).e))
			pos_set = ps::insert(pos_set, make_persistent_node(ps::get(imp).e, eq, rep));
		imp = ps::next(imp);
	}
	imp = G[-var];
	int_t neg_set = 0;
	while(imp != 0){
		if(abs_cmp(-var, ps::get(imp).e))
			neg_set = ps::insert(neg_set, make_persistent_node(ps::get(imp).e, eq, rep));
		imp = ps::next(imp);
	}
	return var > 0 ? add(var, pos_set, neg_set) : -add(-var, neg_set, pos_set);
}

void pd::print_G(ostream &os) {
	for(const auto& el : G){
		os << el.first << ", " << el.second << endl;
	}
}

void pd::print_G() {
	for(auto [fst, snd] : G){
		cout << fst << " --> ";
		ps::print(snd, cout);
	}
}

int_t pd::intersection_preds(int_t val1, int_t val2) {
	vector<int_t> preds1, preds2;
	all_pred_G(val1, preds1);
	all_pred_G(val2, preds2);

	int_t intersection = 0;
	auto iter1 = preds1.begin();
	auto iter2 = preds2.begin();
	while(iter1 != preds1.end() && iter2 != preds2.end()){
		if(abs_cmp(*iter1, *iter2)){
			++iter1;
		} else {
			if(!abs_cmp(*iter2, *iter1)){
				//equality
				intersection = ps::insert(intersection, *iter2);
				++iter1;
			}
			++iter2;
		}
	}
	return intersection;
}

bool pd::existsPath_G(int_t origin, int_t dest) {
	vector<int_t> visited;
	return existsPath_G(origin, dest, visited);
}

void pd::get_component_roots_G(int_t var, vector<int_t> &visited, int_t& roots) {
	if(hasb(visited, abs(var))) return;
	else insertb(visited, abs(var));

	bool valid_pred = false;
	for(int_t imp = G[var]; imp != 0; imp = ps::next(imp)) {
		if (abs_cmp(-ps::get(imp).e, -var)) valid_pred = true;
		get_component_roots_G(ps::get(imp).e, visited, roots);
	}
	if(!valid_pred && G[-var] != 0)
		for(int_t imp = G[-var]; imp != 0; imp = ps::next(imp))
			// Is there a valid successor?
			if(abs_cmp(-var, ps::get(imp).e)) roots = ps::insert(roots, -var);

	valid_pred = false;
	for(int_t imp = G[-var]; imp != 0; imp = ps::next(imp)){
		if(abs_cmp(-ps::get(imp).e, var)) valid_pred = true;
		get_component_roots_G(ps::get(imp).e, visited, roots);
	}
	if(!valid_pred && G[var] != 0)
		for(int_t imp = G[var]; imp != 0; imp = ps::next(imp))
			// Is there a valid successor?
			if(abs_cmp(var, ps::get(imp).e)) roots = ps::insert(roots, var);
}

void pd::print_eqs(int_t dag_id, ostream &os) {
	for(int_t comp = get(dag_id).sh; comp != 0; comp = ps::next(comp))
		pu::print(get_elements[ps::get(comp).e], os);
}

map<int_t,int_t,abs_cmp_> persistent_dag::get_graph(int_t dag_id) {
	const auto& dag = get(dag_id);
	assert(dag.var == 0 && dag.sl == 0);
	map<int_t,int_t,abs_cmp_> graph(abs_cmp);
	for(int_t comp = dag.sh; comp != 0; comp = ps::next(comp))
		//Insert component into graph
		create_graph_non_extended(ps::get(comp).e, graph);
	return graph;
}

void persistent_dag::create_graph_non_extended(int_t component,
					       map<int_t, int_t, abs_cmp_> &graph) {
	if(is_leaf(component)) return;
	const auto& node = get(component);
	int_t suc = node.sh;
	while(suc != 0){
		if(node.var != 0)
			graph[node.var] = ps::insert(graph[node.var],
						      get(ps::get(suc).e).var);
		create_graph_non_extended(ps::get(suc).e, graph);
		suc = ps::next(suc);
	}
	suc = node.sl;
	while(suc != 0){
		if(node.var != 0)
			graph[node.var] = ps::insert(graph[node.var],
							  get(ps::get(suc).e).var);
		create_graph_non_extended(ps::get(suc).e, graph);
		suc = ps::next(suc);
	}
}

int_t persistent_dag::size(int_t dag_id) {
	const auto& dag = get(dag_id);
	if(dag.sh == 0 && dag.sl == 0) return 0;
	int_t s = 0;
	for (int_t pos = dag_id > 0 ? dag.sh : dag.sl; pos > 0; pos = ps::next(pos)) {
		if (dag.var != 0) ++s;
		s += size(pos);
	}
	return s;
}

int_t persistent_dag::remove(int_t dag_id, int_t fst, int_t snd) {
	auto comp = find_in_dag(get(dag_id).sh, fst);
	if (comp == 0) return dag_id;
	create_graph_G(comp);
	vector<int_t> path, visited;
	find_path_G(fst, snd, visited, path);
	path.push_back(fst);
	for (int_t i = (int_t)path.size()-1; i > 0; --i) {
		G[-path[i-1]] = ps::remove(G[-path[i-1]], -path[i]);
		G[path[i]] = ps::remove(G[path[i]], path[i-1]);
	}
	return make_persistent_G(dag_id, comp);
}

bool persistent_dag::contains(int_t dag_id, int_t fst, int_t snd) {
	auto comp = find_in_dag(get(dag_id).sh, fst);
	if (comp == 0) return false;
	auto fst_id = find(comp, fst);
	auto snd_id = find(fst_id, snd);
	return snd_id == 0;
}

bool persistent_dag::weakly_connected(int_t dag_id, int_t v1, int_t v2) {
	auto comp1 = find_in_dag(get(dag_id).sh, v1);
	auto comp2 = find_in_dag(get(dag_id).sh, v1);
	return comp1 != 0 && comp2 != 0 && comp1 == comp2;
}
