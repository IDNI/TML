For now this repository contains an ongoing work on TML (Tau Meta-Language), a
Partial Evaluator (Futamura's style) to PFP (Partial Fixed Points, those logics
that capture PSPACE over finite ordered structures). Nothing here is ready yet.

Materials about PFP and Datalog can be found in any Finite Model Theory (or
Descriptive Complexity Theory) book. PFP was originally introduced by Abiteboul
and Vianu (1989).

Can find us on ##idni @freenode

# TML Tutorial (Unfinished Draft)

We introduce TML (Tau Meta-Language). The language is quite similar to flavors
of Datalog with negation. It is intended to define other languages (hence Meta-
Langauage) in a logical fashion. Our explanation comes in a top-down manner:
Globally speaking, a TML program is a loop. We first describe the higher level
behavior of the loop and then turn to describe what happens in every iteration
together with actual input and output of TML programs. This tutorial attempts to
assume no math background and attempts to be self-contained.

## Recursion

Maybe the most major aspect in TML is recursion. In general, recursion is made
of an iteration with a stopping condition, however on TML we don't have an
arbitrary stopping condition as usual in programming languages. A TML program
defines what happens within a single iteration, while evaluator then iterates
the program until one of the two happens:

1. Two consecutive iterations returned the same result, means that the state of
the computation hasn't changed. This is called a Fixed-Point, and indeed TML is
a fixed-point logic language. If this happens, then this result is considered as
the final result.

2. Or, two nonconsecutive iterations returned the same result, in which case we
consider the program ending with status "fail", or "no result" (this is not same
as "empty result").

There are only those two possibilities because the state space is finite, as we
shall see. In both cases we actually detect a loop, we just consider it as fail
if the loop has length greater than one, and accept the result otherwise. Those
conditions characterize TML's fixed-point operator as what known as PFP (or
Partial Fixed Point).

*Remark: In Finite Model Theory (resp. Descriptive Complexity) it
has been shown that PFP logic over finite ordered structures captures precisely
all problems solvable in PSPACE.*

## Models

Every iteration is a map from a relational structure to itself, under the same
vocabulary. A __relational structure__ (or a relational model, or just a
"__model__" here sometimes) is a set of *relations*, while we think of relations
as tables. As in a table, each row is a tuple, and all rows have same number of
cells. If a relation is a table, then the width of every row, is what we call
the Arity of the relation, as in binary (width 2), monadic (width 1), ternary,
k-ary (width k) etc. Last, every table has a name, still two relations with the
same name but with different arity are treated as if they had a different name.
A relation over a set S is therefore a subset of a power of S (wrt Cartesian
product).

So the following is a just fine relational structure:

	uncle(jim, joe)
	uncle(joe, jill)
	begins_with_j(joe)
	begins_with_j(jim)
	begins_with_j(jill)

which defines two relations, one binary called "uncle" and one unary called
"begins_with_j". To make things even more clearer, let's write down the matching
tables:

		|Table A: uncle	|Table B: begins_with_j	|
		|	 arity=2|	 arity=2	|
	        ----------------------------------------|
	Row 1:	|jim	|joe	|Row 1:	|joe		|
	Row 2:	|joe	|jill	|Row 2:	|jim		|
				|Row 3:	|jill		|

The vocabulary of this structure is contains uncle, begins_with_j, joe, jim, and
jill. But of course it contains more information than just the vocabulary: it
contains information about how the terms relate to each other. We could have
many different tables and models using the same vocabulary. And this is what
each iteration in a TML (or PFP) program is doing: it takes a model and returns
a model with the same vocabulary. In other words, it edits the tables, just
keeping the words that are allowed to appear in the rows and in the table names.
It keeps iterating until one of the two stopping conditions above reaches, so a
"pass" run will determine a set of tables such that if we iterate the program
again, we'll get the same tables untouched.

*Remark: we numbered the tables' rows just for conveinece, but in TML and in math
in general, a relation is an unordered set of tuples. So tables are considered
totally identical if all they differ at is the order of rows. This is not true
at all when it comes to the columns, where the order matters. Also note that our
table's columns don't have names. Indeed by that we differ from common relational
databases where columns typically have names. Here they are identified by their
order only.*

Each iteration is written as update conditions, of the form "if the current
state satisfies ... then update the state to be ...". By "state" (or sometimes
"stage") we refer to the relational structure evolving with each iteration.

*This "update-based" presentation of PFP/Datalog semantics is taken from [2].*

## Example: Transitive Closure

We will now demonstrate the above in a more detailed example. The canonical
example in texts dealing with fixed-point logics is the Transitive Closure (TC)
operator. Take a piece of paper, draw some points, then draw arrows between
the points, and that'd be a directed graph (__digraph__). The points are called
vertices and the arrows are called edges. Note that arrows are directed: an
arrow from vertex 1 to vertex 2 isn't the same as from vertex 2 from vertex 1.
If they'd be considered the same, we'd call it an undirected graph.

*Remark: All directred graphs are all binary relations and vice versa. In other
words, every digraph can be written as a table with two columns, and every such
table represents a digraph.*

The __transitive closure__ of a digraph is simply another digraph representing
paths in the original graph. In other words, B=TC(A) if and only if every two
path-connected vertices in A are edge connected in B. Take the example graph G
with vertices numbered 1,2,3,4:

	1→2
	↑↘↓
	4←3

Or explicitly, denoting the edge relation by E, we have five tuples:

	E(1,2)
	E(2,3)
	E(3,4)
	E(4,1)
	E(1,3)

The transitive closure of the graph contains the following tuples in addition
to the above five:

	TC(1,2) // the original edges
	TC(2,3)
	TC(3,4)
	TC(4,1)
	TC(1,3)

	TC(1,4) // the new edges
	TC(2,1)
	TC(2,4)
	TC(3,1)
	TC(3,2)
	TC(4,2)
	TC(4,3)

On our case, the transitive closure forms a clique graph. The following TML
TML defines the transitive closure of a binary relation E:

	E(?x,?y)	  -> TC(?x,?y)
	TC(?x,?y) E(?y,?z)-> TC(?x,?z)

The arrow sign means to update the relational structure as we mentioned above
and will demonstrate later on. The question mark in front of x,y,z denotes that
they are [first-order] variables. This program is equivalent to the logical
formula:
	
	∀x,y,z E(x,y)->TC(x,y) & [TC(x,y)&E(y,z)->TC(x,z)]

taken under the partial fixed point semantics as mentioned and will be detailed
more. Observe that this formula has all its first-order variables bound, but all
its second-order (relational) variables (TC,E) free. What bounds them is the
fixed point operator, namely they are meant to be calculated iteratively as
above. The formula is evaluated to "true" once the relations (or tables) are not
changed if we apply the program again.  In pseudocode we could write a single
iteration of our TC program as:

	for (x : vertices)
		for (y : vertices)
			for (z : vertices) {
				if (E(x,y)) set TC(x,y):=1;
				if (TC(x,y) && TC(y,z)) set TC(x,z):=1;
			}

and the iteration is repeated as long as either the "set" operations don't
change anything (a "pass" case), or when we repeat to a previous state and
therefore will loop if will continue the same way (a "fail" case).

*Remark: Note that the definition of TC is recursive, as it depends on TC as
well.  Further, on our example graph we have a cycle, so without any care, the
recursion will never halt. We will demonstrate how PFP termination conditions
avoid infinite loops.*

## Negation

Our example contains no negation, or more precisely, it is made of Horn clauses
only. It demonstrates LFP or IFP being weaker logics than PFP. We now add
negation to our example. Suppose we're interested only on the new edges created
by the transitive closure process, namely we remove from the relation TC all
edges from the original graph E. We denote this relation by S. In addition we
explicitly remove from S the edge 1->4. So S is given by:

	S(2,1)
	S(2,4)
	S(3,1)
	S(3,2)
	S(4,2)
	S(4,3)

and our program becomes:

	E(?x,?y)	 	-> TC(?x,?y)
	TC(?x,?y) E(?y,?z)	-> TC(?x,?z)
	TC(?x,?y) !E(?x,?y)	-> S(?x,?y)
	S(1,4)			-> !S(1,4)

Note the negation operator '!' in the third and fourth line. The fourth line
further looks like a contradiction, but a close look shows it has a well-defined
meaning: if on some iteration `S(1,4)` is set, then we unset it. Note that on our
case, `S(1,4)` is concluded only in an iteration where the third line yields
it (as `TC(1,4) & !E(1,4)`). Then iteration after the fourth line can be
activated, and `S(1,4)` is unset. Our program therefore doesn't contain a
contradiction, nevertheless it fails because it has no fixed point, as it keeps
adding and removing S(1,4) with every iteration, which is a loop of length 2. If
we had contradicting updates at the same iteration, then the relation must be
empty which in turn means going back to a previous nonconsecutive state
(precisely the first step), therefore is evaluated also as "fail". Removing the
fourth line completely gives an example of a program with both fixed point and
negation. This is however still a weak case of negation called Stratified
Negation. PFP further negations that allowed to appear everywhere including
recursive statements.

## Bits and Bytes

A bitstring is a monadic relation where the universe is the string's positions.
If we have a string of N bits, our monadic relation will be the set of the
universe elements corresponding to the location of the bits that are set to one.
So for the bitstring 01000110 we'll have a monadic relation, call it M, having:

	M(2)
	M(6)
	M(7)

A bytestring is a binary relation where the first argument is the string's
position as in bitstrings, and the second argument represent the value of that
byte, from -127 to 128. The built-in predicates +-\*\<=/ on those elements
(chars and positions) will behave as usual and will overflow. A byte will
overflow at 8 bits and length will overflow at 64 bits. A relation may be
initialized from a string:

	S"hello world"

represents the set of literals:

	S(1, 'h') 	// we use 'h' as a shorthand to h's ASCII code
	S(2, 'e')
	...
	succ(1, 2) 	// builtin successor relation, using it can determine
	...		// the first, last, and next character. note that we
			// don't need it per string but just once globally

## Input and Output

What a TML program really defines is a set of second-order variables, aka
relations aka tables. On our TC example we had two relations, E and TC. We
considered E as input and TC as output, but we could have take the same program
and consider them the other way around. A TML program doesn't come with
prescribed input and output relation names, but they come afterwards. But in
order to continue from here we need to get a little deeper into the our fixed-
point mechanism.

When we ran the TC example we assumed that the table E has some information in
it but the table TC begins empty and being filled during the execution of the
program. Indeed, the fixed-point operator in PFP is defined to begin with the
empty set. And this points to some asymmetry between input and output: it
amounts to the initial state of the tables being "filled" for inputs and empty
for outputs, and from there the program runs as usual. We therefore need TML's
evaluator to be able to initialize relation before running the program, and to
mark which relations are desired as output. Note that this is in contrast to
most logic or database languges in which the output may be more flexible than
whole tables.


*Remark: A TML program has a fixed number of relation symbols which are the ones
mentioned explicitly in the program, as the language deliberately offers no means
to dynamically create new relations. Therefore per program one can define a fixed
number of input and output relations.*

## Combining Programs

*On this section we follow terminology from [1]*

The input-output design in the last section yields natural means of composing 
rograms. The input which is a starting condition for the PFP iteration can be
the output of another TML program. It would mean to run the first program, and
then run the second program with the output of the first's. Apparently, this
might not end with a PFP program, as we will have two loops instead of one.
But turns out it is possible to combine two PFP programs into one program
indeed. This is referred in the literature as the Transitivity property of PFP.

First, we have to consider the case that the first program doesn't even have a
fixed point, on which case the composition fails disregarding the second
program. But we might be interested in cases where even if the first program
fails, the second program continues with empty input. A program that always has
a fixed point is called *totally defined*.

## Partial Evaluation (PE)

Partial evaluation is about a program that takes several inputs, and we're
concerned with updating the program given part (but not all) of the inputs. In
other words, consider a TML program involving 3 tables, where we're interested
in two of them being input and the third being output. Further we'd like to
specify only the first input, and generate a *reduct* (or *residue*) program
that'd take one input relation but will perform the same computation as the
original function over the two inputs.

The canonical example of a program that takes two inputs at the scope of PE is
an interpreter, and is very relevant to TML being a meta-language. An
interpreter takes two parameters, a program and its input, and evaluates the
program wrt the input. Partially-evaluating the interpreter wrt a given program
yields a compiled program, and that'd be the first Futamura projection.

## Formal Syntax

The set of all TML programs can be defined by the following context-free grammar
(in fact a regular grammar):

	program		:= clause+ .
	clause		:= [literal ws]* [->] [literal ws]*.
	literal		:= snd([fst[,fst]*]) | fst snd fst | snd'"'identifier'"'
	fst		:= [?]identifier
	snd		:= [!]identifier // can be '=' and '!='
	wchar 		:= <any UTF-8 char>
	ws		:= <whitespace>
	identifier	:= wchar-{ '-', '>', '!', '(', ')', ',', '.', '"', ws }

A model (as input or output of TML programs) is specified using the syntax:

	model		:= clause+ .
	clause		:= [equality|inequality ws]* [->] [literal ws]*.
	literal		:= snd([fst[,fst]*]) | fst snd fst | snd'"'identifier'"'
	fst		:= identifier // ground only
	snd		:= [!]identifier | '"'identifier'"'

*(TODO: quoted strings and single chars)*

Note that TML supports both triple notation "subject predicate object" for
binary predicates as well as and list notation "predicate(subject, object)".
However the latter offers unbounded arity.

## References

[1] "Finite Model Theory" by Ebbinghaus and Flum.
[2] "Finite Model Theory and Its Applications" by Gradel et al.
[3] "Partial Evaluation of Computation Process – An Approach to a Compiler-
    Compiler" by Futamura.
