# Branchers

The following are the branchers (objects that suggests improvements according to a given strategy) required in the optimization process:

* minimize (using z3 and memoization): minimization each rule independently. Given a program of n rules produces n possible optimizations, one for each rule. It could be applied to one rule.

	* It could be applied to one rule only.
	* We use memoization to cache the results .
	* Could be splitted in two branchers: 
		- one for the trivial (no cost cases: all term symbols are different), and 
		- another for the hard ones (using z3 and memoization).		

* cqc (using z3 and memoization): solves the query containment problem for each pair of rules. Given a program of size n produces n^2 possible optimizations, one for each pair of rules. 

	* It must be applied to a pair of rules.
	* We use memoization to cache the results .
	* Could be splitted in two branchers: 
		- one for the trivial (no cost cases: no shared term symbols), and 
		- another one for the hard ones (using z3 and memoization) .

* split_bodies: given a rule with m terms, produce 2^m new rules one possible subsetof the body. 
	
	* It could be applied to one rule.
	* No need to cache intermediate results as seem very difficult to have collisions among the produced results.
	* All cases are fairly simple but the complexity is expònential in the number of terms of the body.

* squaring: squares the given raw program. The complexity is high as the result stands for several applications of the given program. 

	* Only make sense to be applied to the whole program.
	* High complexity as the result could grow exponentially on the number of terms of the body.
	* Maybe memoization could be of interest.

We also would need a new additional brancher:

* join_heads: this brancher propose join different rules with unifiable heads.

	* It could be applied to several rules. It's a formal transformation linear in the size of the inputs

# Optimization algorithm

The optimization algorithm should proceed as follows:

* invoke the branchers on the FLAT PROGRAM, the proposed changes represent the actual operations to be performed and also the affected rules.
* select a set of non clashing changes (i.e. the maximal set of changes that affect different rules) and perform the indicated changes.
* for the remaining changes, iterate over the power set: for a given set of changes, applied them and go to first step.

# Squaring + optimization

Regarding squaring, the process would be as follows:

* first optimize the given program,
* square the program and optimize again, if the program does not grow to much (let say linear) repeat this step.
