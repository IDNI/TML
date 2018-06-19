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

	```
	T(1,1,1,?x,?y) :- R(1,3,?x,7,?y) S(?y,2,4,5,?z)
	```

where |A| = 10, and k=5 as we can see. We first mentally convert it into the
rule:

	```
	T(1,6,16,?x,?y) :- R(1,8,?x,22,?y) S(?y,7,14,20,?z)
	```

then we write down (note that the variable ?t in the head should be interpreted
as existentially quantified, as it defines a new tuple):

	```
	(?t, 1) (?t, 6) (?t, 16) (?t, ?x) (?t, ?y) :-
	(?r, 1) (?r, 8) (?r, ?x) (?r, 22) (?r, ?y)
	(?s, ?y) (?s, 7) (?s, 14) (?s, 20) (?s, ?z)
	```

