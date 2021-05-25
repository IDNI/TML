This is work-in-progress and still not performing what is written below.

Rudeanu is a logic language which allows to define what we call Conditional
Boolean Functions (CBF). CBFs are Boolean Functions (BFs) enhanced with conditionals.
For example, "x & (y | z)" is a BF, and "if x=0 then x&y else ~x|y" is a CBF.
Over the 2-element Boolean Algebra (BA), CBFs are exactly BFs. However conditionals
can never be expressed in BFs over other BAs (cf [1], example ...). CBFs are
therefore a strict extension of BFs.

Rudeanu is named after the great Boolean Algebraist Sergiu Rudeanu. His books
"Boolean Functions and Equations" and "Lattice Functions and Equations" are
indispensible.

Evaluating a CBF requires solving Boolean Equations and Inequations, namely
systems of the form "f(x)=0 and g(x)!=0" where f,g are BFs. Without inequations,
they can readily be solved either by the method of successive elimination or by
general reproductive solutions, cf. [1] and [2]. With inequations, the picture
becomes way more complex, and in its full generality, remains an open problem.
However much is known for the case of infinite BAs. cf. [2] for a discussion
about GSBE (Generalized Systems of Boolean Equations).

The conditionals in CBF actually represent GSBE and not simply Boolean Equations,
due to the "else" part.

The class of all CBFs form an infinite BA indeed. A Rudeanu program is a CBF
interpreted of the BA of all CBFs. By that it is completely homoiconic. A program
takes as inputs other programs, and outputs another program.

The syntax is as follows. A BF is written in the form
`and(1,not(2),or(2,3))`, which reads `x1 & ~x2 & (x2 | x3)`. Conditionals
are of the form `leq(1,2,3,4)` which reads `if x1<=x2 then x3 else x4`. The
set of available commands is

Keyword | Meaning
---|---
`and`|Conjunction. Can take many arguments.
`or`|Disjunction. Can take many arguments.
`not`|Negation.
`xor`|`xor(1,2)` is `or(and(1,not(2)),and(not(1),2))`.
`leq`|Containment of the first argument in the second, see below.
`geq`|Containment of the second argument in the first, see below.
`lt`|Strict containment of the first argument in the second, see below.
`gt`|Strict containment of the second argument in the first, see below.
`eq`|First argument equals the second, see below.
`neq`|First argument not equals the second, see below.
`q`|Quantification, see below.
`T`|The distinguised 1 of the BA.
`F`|The distinguised 0 of the BA.
`this`|The current program, see below.
`<int>`|Variable number.
`_<int>`|Program argument number.

Conditionals, i.e. `leq,geq,lt,gt,eq,neq`, take four arguments. The first two
represent the conditional itself, namely the `if` part of an `if-then-else`
statement.  The other two arguments are the `then` and `else` parts of the
conditional, respectively.

The syntax for quantification is as follows: `q(_,...)` quantifies of the
first argument wrt the rest of the arguments in their specified order as if they
were written as a prefix of a logical formula. Negative variable numbers represent
existential quantification, and positive represent universal quantification.
So `forall x1 exists x2 s.t. x3(x1,x2)` is written as `q(3, 1, -2)`.  For example,
`gt(1,F,1,2)` means that if x1 is not identically zero then take x1 else take x2.

References:

[1] Rudeanu, "Boolean Functions and Equations"

[2] Rudeanu, "Lattice Functions and Equations"
