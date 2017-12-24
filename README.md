For now this repository contains an ongoing work on TML (Tau Meta-Language), a
Partial Evaluator (Futamura's style) to PFP (Partial Fixed Points, those logics
that capture PSPACE over finite ordered structures).

To build the code simply run `make` and then to run the example simply do
`./tml < example`

Can find us on ##idni @freenode

# TML Tutorial (Unfinished Draft)

We introduct TML (Tau Meta-Language). The language is quite similar flavors of
Datalog with negation.

One major aspect in TML is recursion. In general, recursion is made of an
iteration together with a stopping condition, but on TML we don't have an
arbitrary stopping condition as in usual programming languages. A TML program
defines what happens with every teration, and the backend then iterates the
program until one of the two happens:

1. Two consequetive iterations returned the same result, means that the state of
the computation hasn't changed. This is called a Fixed-Point, and indeed TML is
a fixed-point logic language. If this situation happens, then this result is
considered as the final result.

2. Or, two nonconsequetive iterations returned the same result, then the program
fails.

There are only those two possibilities because the state space is finite, as we
shall see. In both cases we actually detect a loop, we just consider it as fail
if the loop has length greater than zero, and accept the result otherwise.
Those conditions characterize TML's fixed-point operator as what known as PFP
or Partial Fixed Point. In Finite Model Theory (resp. Descriptive Complexity) it
has been shown that PFP captures precisely all problems solvable in PSPACE.

Every iteration is a map from a relational structure to itself, under the same
vocabulary. Well, I didn't mean it to sound so bad, but it's really simple. A
relational structure is a set of relations, and a relation is just a table. As
in a table, each row is a tuple, and all rows have same number of cells. If a
relation is a table, then the width of every row, is what we call the Arity of
the relation, as in binary (width 2), monadic (width 1), ternary, k-ary (width
k) etc. Last, every table has a name.

So the following is a just fine relational structure:
```
	uncle(jim, joe)
	uncle(joe, jill)
	begins_with_j(joe)
	begins_with_j(jim)
	begins_with_j(jill)
```
which defines two relations, one binary called "uncle" and one unary called
"begins_with_j". To make things even more clearer, let's write down the matching
tables:
```
	|Table A: uncle	|Table B: begins_with_j	|
	|	 arity=2|	 arity=2	|
        ----------------------------------------|
Row 1:	|jim	|joe	|Row 1:	|joe		|
Row 2:	|joe	|jill	|Row 2:	|jim		|
			|Row 3:	|jill		|
```
The vocabulary of this structure is contains uncle, begins_with_j, joe, jim, and
jill. But of course it contains more information than just the vocabulary: it
contains information about how the terms relate to each other. We could have
many different tables and relational structures using the same vocabulary. And
this is what each iteration in a TML (or PFP) program is doing: is taking a
relational structure and returns a relational structure with the same
vocabulary. In other words, it changes the tables, just keeping the words that
are allowed to appear in the rows and in the table names. It keeps iterating
until one of the two stopping conditions above reaches. In fact, the vocabulary
should have the same second order symbols (relational symbols, begins_with_j and
uncle) but not necessarily same first order symbols. We'll get back to this
point.

Remark: we numbered the tables' rows just for conveinece, but in TML and in math
in general, a relation is an unordered set of tuples. So tables are considered
totally identical if all they differ at is the order of rows. This is not true
at all when it comes to the columns, where the order matters. Also note that our
table's columns don't have names. Indeed by that we differ from common relational
databases where columns typically have names. Here they are identified by their
order only.

Each iteration is written as update conditions, of the form "if the current
state satisfies ... then update the state to be ...". By "state" (or sometimes
"stage") we refer to the relational structure evolving with each iteration.

We will now demonstrate the above in a more detailed example. The canonical
example in texts dealing with fixed-point logics is the Transitive Closure (TC)
operator. Take a piece of paper, draw some points, then draw arrows between
the points. That'd be a directed graph (digraph). The points are called vertices
and the arrows are called edges. Note that arrows are directed: an arrow from
vertex 1 to vertex 2 isn't the same as from vertex 2 from vertex 1. If they'd
be considered the same, we'd call it an undirected graph.
All directred graphs are all binary relations and vice versa. In other words,
every digraph can be written as a table with two columns, and every such table
represents a digraph. The transitive closure of a digraph is simply another
digraph representing paths in the original graph. In other words, B=T(A) if
and only if every two path-connected vertices in A are edge connected in B.
Take the example graph G with vertices numbered 1,2,3,4:
```
	1---->2
	^ \   |
	|  \  |
	|   _|⌄
	4<----3
```
Or explicitly, denoting the edge relation by E, we have five tuples:
```
	E(1,2)
	E(2,3)
	E(3,4)
	E(4,1)
	E(1,3)
```
The transitive closure of the graph contains the following tuples in addition
to the above five:
```
	T(1,2) // the original edges
	T(2,3)
	T(3,4)
	T(4,1)
	T(1,3)

	T(1,4) // the new edges
	T(2,1)
	T(2,4)
	T(3,1)
	T(3,2)
	T(4,2)
	T(4,3)
```
On our case, the transitive closure forms a clique graph. The following TML
TML defines the transitive closure of a binary relation E:
```
	E(?x,?y)	 -> T(?x,?y)
	T(?x,?y) E(?y,?z)-> T(?x,?z)
```
The arrow sign means to update the relational structure as we mentioned above
and will demonstrate later on. The question mark in front of x,y,z denotes that
they are [first-order] variables.This program is equivalent to the logical
formula:
```
	∀x,y,z E(x,y)->T(x,y) & [T(x,y)&E(y,z)->T(x,z)]
```
taken under the partial fixed point semantics as mentioned and will be detailed
more. Observe that this formula has all its first-order variables bound, but all
its second-order (relational) variables (T,E) free. What bounds then is the
fixed point operator. So the formula is evaluated to "true" once the relations
(or tables) are not changed if we apply the program again.
In pseudocode we could write a single iteration as:
```
	for (x : vertices)
		for (y : vertices)
			for (z : vertices) {
				if (E(x,y)) set T(x,y):=1;
				if (T(x,y) && T(y,z)) set T(x,z):=1;
			}
```
and the iteration is repeated as long as either the "set" operations don't
change anything (a "pass" case), or when we repeat to a previous state and
therefore will loop if will continue the same way (a "fail" case).

Remark: Note that the definition of T is recursive, as it depends on T as well.
Further, on our example graph we have a cycle, so without any care, the
recursion will never halt. We will demonstrate how PFP termination conditions
avoid infinite loops.

Our example contains no negation, or more precisely, it is made of Horn clauses
only. It demonstrates a weaker case than PFP's being LFP or IFP. To demonstrate
the full power of TML we add negation to our example. Suppose we're interested
only on the new edges created by the transitive closure process, namely we
remove from the relation T all edges from the original graph E. We denote this
relation by S. In addition we explicitly remove from S the edge 1->4. So S is
given by:
```
	S(3,1)
	S(3,2)
	S(4,2)
	S(4,3)
```
and our program becomes:
```
	E(?x,?y)	 	-> T(?x,?y)
	T(?x,?y) E(?y,?z)	-> T(?x,?z)
	T(?x,?y) !E(?x,?y)	-> S(?x,?y)
	S(1,4)			-> !S(1,4)
```
Note the negation operator '!' in the third and fourth line. The fourth line
further looks like a contradiction, but a close look shows it has a well-defined
meaning: if on some iteration `S(1,4)` is set, then we unset it. Note that on our
case, `S(1,4) is concluded only in an iteration where the third line yields
it (as `T(1,4) & !E(1,4)`). Then iteration after the fourth line can be
activated, and `S(1,4)` is unset. Our program is therefore satisfiable. If we
had contradicting updates at the same iteration, then the relation must be empty
which in turn means going back to a previous nonconsequetive state (precisely
the first step), therefore is evaluated as "fail".

TODO on this README, partial list:
	1. fix and finish
	2. explain how partial evaluation works here
	3. explain how to input/output strings/trees
