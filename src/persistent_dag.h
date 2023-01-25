#ifndef TML_PERSISTENT_DAG_H
#define TML_PERSISTENT_DAG_H

#include "defs.h"
#include "persistent_set.h"
#include "persistent_union_find.h"

class persistent_dag;

template<>
struct std::hash<persistent_dag> {
	size_t operator()(const persistent_dag &) const;
};

class persistent_dag {
	using pd = persistent_dag;
	using ps = persistent_set;
	using pu = persistent_union_find;
	// References to persistent set of persistent_dags
	int_t var = 0;
	// The high successor
	int_t sh = 0;
	// The low successor
	int_t sl = 0;

	static void form(std::pair<int_t, int_t> &p);
	static void form (int_t& fst, int_t& snd);
	static int_t add(int_t v, int_t suc_high, int_t suc_low);
	static int_t update_root_dag(int_t root_id, int_t &component, int_t old_node, int_t new_node);
	static int_t update(int_t old_node, int_t new_node, int_t component);
	static int_t find (int_t root_id, int_t elem);
	static int_t find(int_t root_id, int_t elem, std::vector<int_t>& visited);
	static int_t
	analyze_component(int_t set_id, int_t fst, int_t snd, int_t dag_root,
			  std::vector<int_t> &sings, std::vector<int_t> &eqs);
	static int_t find_in_dag(int_t component_set, int_t elem);
	static int_t plain_insert_edge(int_t node_id, int_t suc_id, int_t dag_root, int_t &component);
	static int_t insert_root_node (int_t dag_root, int_t& component, int_t node_id);
	static int_t insert_component(int_t root, int_t fst, int_t snd);
	static int_t insert_suc(int_t node_id, int_t suc_id);
	static int_t connect_components(int_t dag_root, int_t &comp_source, int_t comp_dest, int_t fst, int_t snd);
	static int_t add_to_component(int_t component, int_t v, int_t w);

	static void create_graph_G(int_t component);
	static void create_graph_non_extended(int_t component, std::map<int_t,int_t,abs_cmp_> &graph);
	static int_t make_persistent_G(int_t dag_id, int_t component);
	static void get_component_roots_G(int_t var, std::vector<int_t> &visited, int_t &roots);
	static int_t make_persistent_node(int_t var, int_t &eq, int_t rep);
	static void all_suc_G(int_t var, std::vector<int_t> &sucs);
	static void all_pred_G(int_t var, std::vector<int_t> &preds);
	static bool existsPath_G(int_t origin, int_t dest, std::vector<int_t>& visited);
	static bool existsPath_G(int_t origin, int_t dest);
	static int_t is_singleton_G(int_t component, std::vector<int_t> &suc_snd, int_t fst, int_t snd);
	static void set_var_G(int_t var, std::vector<int_t> &sings);
	static void transitive_reduction_G(int_t fst, const std::vector<int_t> &suc_snd);
	static bool find_path_G(int_t origin, int_t dest, std::vector <int_t> &visited, std::vector<int_t> &path);
	static void remove_loop_G(int_t origin, int_t dest, std::vector<int_t> &eqs);
	static void print_G();
	static int_t intersection_preds(int_t val1, int_t val2);
  public:
	persistent_dag() = default;
	persistent_dag(int_t v, int_t suc_high, int_t suc_low) :
		var(v), sh(suc_high), sl(suc_low) {}

	static void init();
	friend std::hash<pd>;
	bool operator==(const pd&) const;

	static int_t insert(int_t dag_id, std::pair<int_t, int_t> &elem,
			    std::vector<int_t> &sings, std::vector<int_t> &eqs);
	static int_t
	insert(int_t dag_id, int_t fst, int_t snd, std::vector<int_t> &sings,
	       std::vector<int_t> &eqs);
	static int_t set_var(int_t root_id, int_t var, std::vector<int_t> &sings);
	static int_t remove(int_t dag_id, std::pair<int_t, int_t> &elem);
	static bool is_leaf(int_t dag_id);
	static bool contains(int_t dag_id, std::pair<int_t, int_t> &elem);
	static std::map<int_t,int_t,abs_cmp_> get_graph(int_t dag_id);

	static pd get(int_t dag_id);
	static void print(int_t set_id, std::ostream &os);
	static void print_eqs(int_t dag_id, std::ostream &os);
	static void print_G(std::ostream& os);
};

#endif //TML_PERSISTENT_DAG_H