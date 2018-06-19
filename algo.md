We show how to convert a k-ary Datalog program into a sequence of binary Datalog
programs (i.e. in which each relation is of arity 2), or equivalently for our
case, into MSO.

Given a Datalog program involving k-ary relations over a finite universe A, we
basically have two kinds of data to maintain: the facts and the rules. The facts
are k-ary tuples of numbers from 1 to |A| (otherwise we transform the program
to admit this structure). We look at a k-ary tuple over 1..|A| as a set of
k pairs over 1..k|A| and we assume that every tuple has an id (e.g. its location
in memory, or some unique numbering for all tuples in the database). We do this
in two mental steps. First we add to the i'th element of the tuple, the quantity
k\*i. By that, all the tuple's elements become distinct, and we can recover their
order by comparing integers. Therefore it's enough to use an unordered set rather
an ordered tuple. It should become much clearer with an example: if |A|=5 and k=4
and we got the k-ary tuple (1,3,4,6) and its tuple id is 1000, we first look at
it as (1, 3+5=8, 4+2\*5=14, 6+3\*5=21), so the resulted set of pairs is
{(1000,1), (1000,8), (1000,14), (1000, 21)}.

We convert our Datalog program in the very same fashion. Take for example
the rule

	T(1,1,1,?x,?y) :- R(1,3,?x,7,?y) S(?y,2,4,5,?z)

where |A| = 10, and k=5 as we can see. We first mentally convert it into the
rule:

	T(1,6,16,?x,?y) :- R(1,8,?x,22,?y) S(?y,7,14,20,?z)

then we write down

	(?t, 1) (?t, 6) (?t, 16) (?t, ?x) (?t, ?y) :-
	(?r, 1) (?r, 8) (?r, ?x) (?r, 22) (?r, ?y)
	(?s, ?y) (?s, 7) (?s, 14) (?s, 20) (?s, ?z)

Note that the variable ?t in the head should be interpreted as existentially
quantified, as it defines a new tuple. Moreover, we'd prefer to interpret it as
"exists unique" rather just "exists". Also note that this conversion is into a
single binary relation. We could make it into multiple monadic relations, and by
that get MSO. So it is really a description of a single graph, as any binary
relation is a directed graph. However on our case we can say more about the graph:
it is a bipartite graph, as an edge from a k-ary tuple-id to its k components,
where the latters are labeled in a way that preserves their ordering, as above.
It is also a k-regular graph, as every tuple id has precisely k outgoing edges,
for fixed arity. In short, it is a biregular graph
( https://en.wikipedia.org/wiki/Biregular_graph ).

Since our graph is bipartite, we represent it by MxN matrix where M is the number
of tuples currently in the database, and N=k|A|. Call this matrix C. Then C[i,j]
is 1 if the i'th tuple contains the element `j%|A|` in the `j/|A|` notation (to
be interpreted as in C, namely % is the remainder and / is the quotient).
Otherwise C[i,j]=0. We now interpret the resulted binary logic program
as statements about the matrix C.


