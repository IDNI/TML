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

/*
 * A canonical and persistent graph data structure
 * to be used to store transitively reduced implication graphs
 * while containing no loops and constants. Loops and constants will automatically
 * be extracted in the insert function.
 *
 * The basic structure of a graph node is (v, high, low),
 * where v denotes the current variable, high is the set of graph nodes that are
 * implied by v and low is the set of graph nodes that are implied by -v.
 *
 * The root has the form: (0, components, 0), where components is a set of
 * graph nodes (0, component_roots, 0). The components are the weakly connected
 * components of the implication graph. Further, component_roots is the set of
 * graph nodes that represent the roots of the implication graph stored in this
 * component.
 *
 * A variable that can be found in a graph node on one component cannot
 * be found on another component.
 *
 * Each component has a canonical union find data structure attached
 * which can be found using the get_elements map. This union find data structure
 * is used to save and retrieve all the variables which can be found on the weakly
 * connected component.
 */

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

	// Turns the implication into the canonical form
	static void form(std::pair<int_t, int_t> &p);
	static void form (int_t& fst, int_t& snd);
	// Canonically add a node to the universe
	static int_t add(int_t v, int_t suc_high, int_t suc_low);
	// Replace old_node with new_node in the graph represented by root_id
	// We assume that old_node is found within component
	static int_t update_root_dag(int_t root_id, int_t &component, int_t old_node, int_t new_node);
	// Replace old_node with new_node on component
	static int_t update(int_t old_node, int_t new_node, int_t component);
	// Find elem on the graph represented by root_id
	static int_t find (int_t root_id, int_t elem);
	static int_t find(int_t root_id, int_t elem, std::vector<int_t>& visited);
	static int_t
	// Given a set of components represented by set_id, find the correct component
	// to insert the implication fst --> snd and perform all actions needed to
	// keep the implication graph canonical. The process extracts constants
	// and equalities created by inserting fst --> snd.
	analyze_component(int_t set_id, int_t fst, int_t snd, int_t dag_root,
			  std::vector<int_t> &sings, std::vector<int_t> &eqs);
	// Return the component on which elem is found, otherwise return 0
	static int_t find_in_dag(int_t component_set, int_t elem);
	// Insert an edge into component on the implication graph represented by
	// dag_root without checking if the insertion breaks canonicity
	static int_t plain_insert_edge(int_t node_id, int_t suc_id, int_t dag_root, int_t &component);
	// Insert node_id as a new root into the weakly connected component represented by
	// component
	static int_t insert_root_node (int_t dag_root, int_t& component, int_t node_id);
	// Add a new weakly connected component containing fst --> snd to the
	// graph represented by root
	static int_t insert_component(int_t root, int_t fst, int_t snd);
	// Return a graph node that has suc_id as an outgoing edge
	static int_t insert_suc(int_t node_id, int_t suc_id);
	// Merge two weakly connected components
	static int_t connect_components(int_t dag_root, int_t &comp_source, int_t comp_dest, int_t fst, int_t snd);
	// Each component has a canonical union find data structure attached as explained
	// in the summary of this class. This method is used to place the new
	// equality v=w into the union find data structure belonging to component.
	static int_t add_to_component(int_t component, int_t v, int_t w);

	// Create a map representation of the implication graph represented by component.
	// This implication graph has for a --> b both edges a --> b and -b --> -a.
	static void create_graph_G(int_t component);
	// Create a map representation of component stored in graph. Implications
	// appear only in their canonical form in this graph.
	static void create_graph_non_extended(int_t component, std::map<int_t,int_t,abs_cmp_> &graph);
	// Create a canonical graph from the map representation of a component stored in G
	static int_t make_persistent_G(int_t dag_id, int_t component);
	// Find the roots of a component in G
	static void get_component_roots_G(int_t var, std::vector<int_t> &visited, int_t &roots);
	// Create a graph node from the node var in G
	static int_t make_persistent_node(int_t var, int_t &eq, int_t rep);
	// Find all successors of var on G
	static void all_suc_G(int_t var, std::vector<int_t> &sucs);
	// Find all predecessors of var in G
	static void all_pred_G(int_t var, std::vector<int_t> &preds);
	// Find a path in G from origin to dest
	static bool existsPath_G(int_t origin, int_t dest, std::vector<int_t>& visited);
	static bool existsPath_G(int_t origin, int_t dest);
	// Find constants which are created on G by inserting fst --> snd
	static int_t is_singleton_G(int_t component, std::vector<int_t> &suc_snd, int_t fst, int_t snd);
	// Evaluate the implication graph represented by G on var and extract constants
	static void set_var_G(int_t var, std::vector<int_t> &sings);
	// Apply the transitive reduction algorithm to G
	static void transitive_reduction_G(int_t fst, const std::vector<int_t> &suc_snd);
	// Find a path in G from origin to dest and save it in path
	static bool find_path_G(int_t origin, int_t dest, std::vector <int_t> &visited, std::vector<int_t> &path);
	// Extract loops in G that would be created by inserting dest --> origin
	static void remove_loop_G(int_t origin, int_t dest, std::vector<int_t> &eqs);
	static void print_G();
	// Return the intersection of the predecessors of val1 and val2 on G
	static int_t intersection_preds(int_t val1, int_t val2);
  public:
	persistent_dag() = default;
	persistent_dag(int_t v, int_t suc_high, int_t suc_low) :
		var(v), sh(suc_high), sl(suc_low) {}

	static void init(int_t n);
	friend std::hash<pd>;
	bool operator==(const pd&) const;

	// Insert implication into graph represented by dag_id
	// sings will hold extracted constants, eqs will hold extracted equalities
	static int_t insert(int_t dag_id, std::pair<int_t, int_t> &elem,
			    std::vector<int_t> &sings, std::vector<int_t> &eqs);
	static int_t
	insert(int_t dag_id, int_t fst, int_t snd, std::vector<int_t> &sings,
	       std::vector<int_t> &eqs);
	// Evaluate the implication graph represented by root_id on var and
	// extract constants in sings
	static int_t set_var(int_t root_id, int_t var, std::vector<int_t> &sings);
	// Remove fst --> snd from graph represented by dag_id
	static int_t remove(int_t dag_id, int_t fst, int_t snd);
	// Check if the graph represented by dag_id has outgoing edges
	static bool is_leaf(int_t dag_id);
	// Check if the graph represented by dag_id contains fst --> snd
	static bool contains(int_t dag_id, int_t fst, int_t snd);
	// Check if v1 and v2 are weakly connected in the (directed) graph represented by
	// dag_id.
	static bool weakly_connected(int_t dag_id, int_t v1, int_t v2);
	// Converts the persistent graph data structure into a map
	static std::map<int_t,int_t,abs_cmp_> get_graph(int_t dag_id);
	// Return the number of nodes in the implication graph
	//TODO: Calculation of size is linear, not constant
	static int_t size(int_t dag_id);
	// Return the graph node which dag_id represents
	static pd get(int_t dag_id);
	// Print the implication graph represented by set_id to os
	static void print(int_t set_id, std::ostream &os);
	// Print the equality set associated to dag_id to os
	static void print_eqs(int_t dag_id, std::ostream &os);
	// Print the map G
	static void print_G(std::ostream& os);
};

#endif //TML_PERSISTENT_DAG_H