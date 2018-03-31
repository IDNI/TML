This is a forward reasoner (not ready yet). It computes the full closure of
given set of rules, and allows to efficiently add new data and compute the next
closure. For now it's designed to support Datalog-like rules. As in Prolog/
Datalog terminology, every rule has a body and a head, separated by the
implication arrow sign =>, and each being a list of terms separated by commas. A
term is a sequence of strings. Variables begin with a question mark. So
transitive closure rules may look like:

	E ?x ?y => T ?x ?y
	T ?x ?y, T ?y ?z => T ?x ?z

It is also possible to use a different encoding, using integers, and in fact
given string encoding we convert it to integers. The transitive closure example
can be written in integer encoding as:

	1 -1 -2 => 2 -1 -2
	2 -1 -2, 2 -2 -3 => 2 -1 -3

As can be seen, negative integers encode variables, while positives encode
constants.  Integers need not be sequential, altough internally we rename
variables to be so.

Aside such rules we also supply facts which are tuples of strings (of arbitrary
varying arity). For example we could seed our edge relation E with

	E 1 2
	E 2 3

and so on.

The purpose of the forward reasoner is to calculate all ground tuples. Ground
means that they contain no variables, and can be derived from the rules. On
our little example, it'll come up with the additional relation

	E 1 3

and no more. As usual, we'll refer to the facts supplied at the beginning as
edb or extensional database, and to derived facts as simply derived facts, or
idb as intensional database. Although we don't look at this implementation as
database-oriented, even quite the opposite: we preprocess the rules for repeated
usage, not the facts.

The implementation design of the reasoner is as follows. After normalizing
variables as above, we equip each term in body with a set of "env"s. An
environment, or context or substitution (all common terminology for the same
thing), is a set of pairs of the form "?x=?y" or "?x=y", namely holds variable
substitutions. We could encode them as

	map<int_t, int_t> env;

but we prefer to simply have

	int_t *env;

where the length of the array is as the number of variables in the rule that the
env is referring to. So the substitution of variable number 6 would be at env[6].
This is why variable normalization is essential. Substitutions are then managed
using "representatives" and "path compression" as in the Union-Find data 
structure.

Back to our sets of envs per body term, which we call "bins", can be written
simply as:

	set<env> **bins;

where the two-dimensional array indices indicate the rule # and body term #.
Further we equip each head term with a set of pairs of positive integers,
indicating the rule # and the body # of body terms that can possibly match this
head term. We call those "links":

	set<pair<size_t, size_t>> **links;

where the array indices refer to rule # and head #. Note that links, unlike
bins, are known before we see the facts, and indeed are precomputed from the
rules. Our code exposes a single class, `fwd`, in which its constructor takes
the rules and creates the links and normalize variables, where `operator()`
takes facts one or many times and returns the closure of the "immediate
consequence" operator (commonly written as T<sub>p</sub>).

We also must keep track of the extents of the arrays, so we got:

	size_t nrules, *nvars, *bnterms, *hnterms;

Now move to the "join" step. We go over all body items of all rules in order,
and try to match them against all facts. If match succeeds, we keep the env that
makes that body term into a fact, inside that term's bin. Then, per each rule,
we have to join the sets of envs per body such that they don't contradict each
other. In more elaboration, a rule with `k` body terms will need a `k`-tuple of
facts in order to activate its body. Those facts need to match to the body items
without collision of variables. For example, a body of:

	T ?x ?y, T ?y ?z

can have "?x=1 ?y=2" in the first term's bin and "?y=3 ?z=4" in the second
term's bin. Since the substitutions for ?y are contradictory, this pair of envs
need to be filtered out of our join. So our "join" step is about to merge all
bins in each single rule, into one set of envs. (Recall that each env is
relative to a whole rule, not a single term.)

We do so by first ordering the bins in a rule in ascending order according to
their size (numer of envs being number of matching facts). Then we merge two
consecutive bins at a time, in a straight-forward way. We finish with a set of
envs, each env representing a `k`-tuple of facts, if substituted in all `k` body
terms.

This resulting set of envs then activate the heads, yielding new facts (this
time, idb). We could repeat everything we said so far until no new facts are
derived, and this will be a correct forward reasoner. Still we'd like to not
repeat computations. This is done by two main optimizations:

1. The use of "links" above: when an idb fact comes out of a head term, we know
which bodies to look at and don't need to go over all of them.

2. Join is performed in a selective manner for idb facts, rather as described
for edb facts. Specifically, per a single new idb fact, and per body item to
"activate" (namely for all body terms listen in "links"), we temporarily replace
the activated body's bin with a bin that contains a single env, the env that
encode the new fact. We then perform the join step as before, with the temporary
bin in place. Afterwards we restore the original bin and add to it the new fact.

3. The bins share a subset relation in case where body items are special cases
of each other. We therefore maintain the bins incrementally. Note that the
amount of such "splittings" is boudned by the size of the rules, independently
of the data. Our bins now look like:

	set<pair<size_t, size_t>> **sc;

where sc[i][j] has a set of pairs representing the rule # and the body # of the
terms that are supercases.

4. The sc relation can guide the join step in the following way. First we join
all most special cases. Whatever fails we pass to the next supercases. If no
supercase is left, the join is done.

That's basically all.

The scope of this in TML is to have a forward machine as a backend for backward
reasoning and Earley parsing. But it is a very general purpose tool, therefore
packed in short and lightweight single header and single source file.
