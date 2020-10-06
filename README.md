# Introduction

TML (Tau Meta-Language) is a variant of Datalog. It is intended to serve as
a translator between formal languages (and more uses, see under the Philosophy
section). The main difference between TML and common Datalog implementations is
that TML works under the Partial Fixed-Point (PFP) semantics, unlike common
implementations that follow the Well-Founded Semantics (WFS) or stratified
Datalog. By that TML (like with WFS) imposes no syntactic restrictions on
negation, however unlike WFS or stratified Datalog it is PSPACE complete rather
than P complete.  TML's implementation heavily relies on BDDs (Binary Decision
Diagrams) in its internals. This gives it extraordinary performance in time and
space terms, and allowing negation to be feasible even over large universes. In
fact negated bodies, as below, do not consume more time or space than positive
bodies by any means, thanks to the BDD mechanism.

## Not Implemented Yet
Not everything on this document is implemented though implementation is ongoing
and everything is expected to be implemented in a matter of weeks. Besides there
is no release yet as tests and final finishes have not been done yet.

Specifically:
* Proof extraction needs a rewrite.
* Proof extraction for programs that contain negation.
* Tree extraction is not fully working and is a very preliminary implementation,
specifically:
  * Cycle detection
  * Node omission
  * Testing
* Queries need a rewrite.
* String from trees.
* Strings are encoded in a different style than described here.
* Symbol for length of strings.
* Support binary input files and UTF-8 charset.
* Parsing error messages and bugs.
* First order formulas.
* Comprehensive tests of everything.

# Universe

The size of the universe (or domain of discourse) of a TML program is:
* The number of distinct non-relation symbols in the program, plus
* The maximum nonnegative integer that appears in the program (where the length
of input strings counts as appearing in the program), plus
* 256 if at least one character symbol is used in the program (or at least one
string appears in the program).

# Fixed Points

TML follows the PFP semantics in the following sense. On each step, all rules
are executed once and only once, causing a set of insertions and deletions of
terms. If the same term is inserted and deleted at the same step, the program
halts and evaluates to `unsat`. Otherwise it continues to the next step
performing again a single evaluation of every rule. This process must eventually
halt in either of the following forms:

1. The database obtained from the current step is equal to the database resulted
from the previous step. This is a Fixed-Point. When this happens, the resulted
database is considered as the final result.

2. Or, the database obtained in one step equals to the database state in some
previous, not immediate predecessor, state. In this case the program will loop
forever if we wouldn't detect it and halt the program, and is therefore
evaluated to `unsat`, as no fixed point exists.

Note that only one of the two options can happen because the arity and the
universe size are fixed. Ultimately, for universe size n and maximum arity k,
they will occur in no more than 2^n^k steps.

# Facts and Rules

A TML program consists of initial terms (facts) and rules that instruct the
interpreter which terms to derive or delete at each step, as described in the
previous section.

## Facts

Facts take the form of

    a(b c).
    a(b(c)).
    a(1 2 3).
    rel('t' 1 2).
    b(?x).
    r.

Each term begins with a relation symbol (which is not considered as part of the
universe). It is then possibly followed by parenthesis (or any balanced sequence
of them) containing symbols. A term like `b(b)` is understood as containing two
different symbols, one `b` stands for a relation symbol, and the second one for
a universe element. Symbols may either be alphanumeric literals (not beginning
with a digit), or a nonzero integer, or a character. Additionally a term may
contain variables, prefixed with `?`. A fact that contain variables,
like `b(?x)`, is interpreted where ?x goes over the whole universe. So the
program

    a(1).
    b(?x).

is equivalent to

    a(1).
    b(0).
    b(1).

## Rules

Rules are terms separated by commas and one update operator `:-`. For example:

    e(?x ?y) :- e(?x ?z), e(?z ?y).

what is left to the update operator (which may be several terms separated by
commas) is called the `head` of the rule, while the rhs is called the `body`
of the rule. This latter example therefore instructs to add to the next-step
database all facts of the form e(?x ?y) such that e(?x ?z) and e(?x, ?y) appear
in the current-step database, for some value of ?z. So for example the following
program

    e(1 2).
    e(2 1).
    e(?x ?y) :- e(?x ?z), e(?z ?y).

will result with:

    e(1 2).
    e(2 1).
    e(1 1).
    e(2 2).

Note that the order of facts and rules does not matter. Also note that all
facts and rules must end with a dot.

## Negation and Deletion

Bodies may be negated using the negation symbol `~`, for example:

    e(?x ?y) :- e(?x ?z), e(?z ?y), ~e(?x ?x).

The variable ?x will bind to all values such that e(?x ?x) does not appear in
the current-step database.

Heads may also contain the negation symbol, in which case it is interpreted
as deletion. For example the rule:

    ~e(?x ?x) :- e(?x ?x).

Will make the next-step database to not include all terms of the form e(?x ?x)
included on the current step database.

For performance reasons it is advised to better not have variables appearing
in negated bodies that do not occur in any positive head (in the same rule),
or variables that appear in positive heads and do not appear in bodies (also in
the same rule). However this is only a performance advice. TML should work
correctly either way, where variables (implicitly) range over the whole
universe.

## Sequencing

It is possible to sequence programs one after the other using curly brackets.
For example the program

    {
      e(1 2).
      e(2 3).
      e(3 1).
      e(?x ?y) :- e(?x ?z), e(?z ?y).
    }
    {
      ~e(?x ?x) :- e(?x ?x).
    }

will result with

    e(1 2).
    e(1 3).
    e(2 1).
    e(2 3).
    e(3 1).
    e(3 2).

More generally, the output of one program is considered the input of the other.
It is possible to filter the output before passing it to the next program as in
the section "Queries".

Nested programs are unsupported as they make no difference from flat sequences.

# Trees

Terms of certain form are interpreted as trees. This does not affect the rules
at all, but only as means of inputting and outputting facts, as below. Trees are
expressed by constructing a directed graph of terms. For example the following
term

    b((a(1 2)) (a(2 2)) (c(2 3)))

indicates two edges in a graph named `b`, where a vertex labelled `a(1 2)` has
two [ordered] outgoing edges, one to the term `a(2 2)` and one to the term
`c(2 3)`. Terms as labels of vertices need not be proper terms in the sense
that we could also have

    b((a 1 2) (a 2 2) (c 2 3))

Either way, `a` and `c` are interpreted as universe elements rather relation
symbols. In general having a relation symbols and then parenthesized sequences
of elements is interpreted as denoting ordered outgoing edges.

We can construct trees in the normal way using rules. For example, a proof
tree of a program consisting of the rule

    e(?x ?y) :- e(?x ?z), e(?y ?z).

may be constructed by adding the rule

    proof((e(?x ?y)) (e(?x ?z)) (e(?y ?z))) :- e(?x ?y), e(?x ?z), e(?y ?z).

We can then extract the proof tree by querying, as in the section "Queries".
However as in that section there's a shortcut syntax for extracting proofs.

Note that as we indeed construct a directed graph rather a tree, it is
interpreted as a packed representation of a forest. Further this graph may
contain loops. They are avoided during the traversal by simply skipping
previously visited nodes.

Terms that appear in double parenthesis, like `a 2 2` in:

    b((a 1 2) ((a 2 2)) (c 2 3))

will be omitted when converting a tree to a string, as in the next section.

# Strings

It is possible to input strings to the database. The line

    @string mystr "abc".

will add the following fact to the database:

    mystr(((0))('a')((1))).
    mystr(((1))('b')((2))).
    mystr(((2))('c')((3))).

More generally, `@string relname "str"` will use the relation symbol relname
to declare a tree where each string position has first successor to the
character on that position, and a second successor to the next position.
Observe that the positions appear in double parenthesis. This is because of the
following:

It is possible to construct a string by specifying a root of a tree. The backend
will then traverse the tree depth-first left-first (Pre-Order) and stringify its
content. It will omit from the output string nodes that appear in double
parenthesis. For example the program

    @string str T((1 2)).
    T((1 2) (2 3) (a b)).
    T((a b) (c d)).
    T((2 3) (4 5)).

will result in having the relation symbol `str` represent the string:

    "122345abcd"

while if we had:

    @string str T((1 2)).
    T((1 2) ((2 3)) (a b)).
    T((a b) ((c d))).
    T(((2 3)) (4 5)).

the string `str` would be:

    "1245ab"

This relation `str` is then transferred to the next sequenced program, or
emitted as the output of the program if no sequenced program is present.

Note that the double-parenthesis omission is denoted on the successor nodes.

Now we can see why strings create trees with double parenthesis: the following

    @string str1 "abc".
    @string str2 str1(((0))).

will result with `str2="abc"`.

It is also possible to output a string to `stdout` by using it as a relation
symbol:

    @stdout str1(((0))).

or arbitrary tree:

    @stdout T((1 2)).

In addition a string can refer to command line arguments:

    @string str $1.

or to be taken from `stdin`:

    @string str stdin.

or from a file:

    @string str <filename>.

Finally it is possible to refer to the length of the string by the symbol
`len:str`.

# Queries

TML features three kinds of queries: filtering, proving, and tree extraction.
Filtering and tree extraction replace the resulted database with their result,
namely deleting everything unrelated to them. Their result is then outputed
or passed to the next sequenced program.

Filtering is done by:

    ! e(1 ?x).

which will leave on the database only the results that match the term `e(1 ?x).`
Tree extraction is done by supplying the root (which may possibly contain
variables) after `!!`:

    !! T((?x ?y)).

Proof extraction is done by adding a single directive specifying a relation
name:

    @trace relname.

which will construct a forest with relation symbol `relname` that contains
all possible witnesses to all derived facts, in a fashion that was described
above: if we have a rule

    e(?x ?y) :- e(?x ?z), e(?y ?z).
    @trace P.

then the trace tree will have the form

    P((e(?x ?y)) (e(?x ?z)) (e(?y ?z))).

# Grammars

It is possible to supply a context free grammar as a syntactic shortcut for
definite clause grammars. For example Dyck's language may be written as:

    S => null.
    S => '(' S ')' S.

and will be converted to the rules:

    S(?v1 ?v1) :- str(((?v1)) (?v2) ((?v3))).
    S(?v3 ?v3) :- str(((?v1)) (?v2) ((?v3))).
    S(?v1 ?v5) :- str(((?v1)) ('(') ((?v2))), S(?v2 ?v3),
        str(((?v3)) (')') ((?v4))), S(?v4 ?v5).

where `str` is some string defined in the program. Grammars are allowed in
programs that contain only one string. If multiple strings require parsing it
is possible to define them in sequenced programs.

Extracting the parse forest can be done by extracting a proof of the start
symbol:

    !! parseForest S(0, len:str).

which also defines the start symbol.

The grammar supports fow now the builtins `alpha`, `alnum`, `digit`, `printable`
, and `space`. For example a sequence of one or more whitespaces can be defined
by the productions

    ws => space ws1.
    ws1 => space ws1.
    ws1 => null.

# First Order Formulas

It is possible to supply a first order formula which is then transformed into
a TML program. The valid symbols are:
 - quantifiers: forall, exists, unique.
 - connectives: `&&`, `||`, `->`, `<->` and `~` for negation.
 - punctuation: balanced `{` , `}` for matrix and sub-formula specification.
 - variables and relationships.
 - constraints: `+`, `<`, `=`.  

Attaching a formula to the head of a rule will make true in case of satisfiability otherwise false.

Example 1:

    A(0).
    A(1).
    B(0).
    ALL_B_IS_A(1) :- forall ?x { B(?x) -> A(?x) }.

    will result with:
    ALL_B_IS_A(1).

Additionally, if variables are set on the head, besides checking satisfiability TML will evaluate the solution for such formula.

Example 2:

    A2(1 0).
    A2(1 1).
    B2(1 0).
    B2(1 1).
    B2(0 1).
    AND_B2_A2(?x ?y) :- { B2(?x ?y) && A2(?y ?x) }.

    will result with:
    AND_B2_A2(1 1).
    AND_B2_A2(0 1).

Notice that variables in the head of the rule are existentially quantified, so above formula is equivalent to:  

    ALL_B2_IS_A2(?y ?x) :- exists ?x exists ?y { B2(?x ?y) -> A2(?y ?x) }.

TML first order logic also allows to set arithmetic constraints to the variables by a conjunction with an arithmetic expression as below.

Example 3:

    s0(0).
    s1(1).
    s2(2).
    A(?x ?y) :- { s2(?x) && ?x + 1 = ?y } .
    B(?v1 ?v3) :- exists ?v2 { A(?v2 ?v3) && s1(?v1) && ?v1 + 1 = ?v2 } .

    will result with:
    A(2 3).
    B(1 3).


# Finitary Arithmetic

TML currently provide support for integer addition and multiplication. It also includes support for bitwise boolean operations (AND, OR, XOR, NOT) and shift operations (SHL, SHR). Additionally the arithmetic primitives are defined in two modes: (1) pre-computed and (2) ad-hoc, according to how they are computed.

1. Pre-computed mode involves the generation of the relationship `?x op ?y = ?z` where `op` can be `+, *, &, |, ^, <<, >>`.
The range for the arguments is `(0,MAX)` where `MAX` is equal to the maximum number in the program.
Pre-computed stands for how TML is actually handling the unification of the arithmetic relationship with the values of the arguments; starting with a global relationship for any possible value in the universe it will get constrained depending on the arguments.

Example 1:

    U(4).
    A(1).
    A(3).
    adder_0(?x ?y ?z) :- e(?x), e(?y), ?x + ?y = ?z.
    adder_1(?x) :- e(?x), ?x + 1 = 3. # unsat
    adder_2(?x) :- e(?x), ?x + 2 = 3.

    output:
    adder_0(3 1 4).
    adder_0(1 3 4).
    adder_0(1 1 2).
    adder_2(1).

This mode is the most expressive one, meaning that i.e. allows to solve equations like in rule setting `adder_C` in Example 1. It will be in general the most convenient one for programs involving any operation other than multiplication.
On the other hand, when doing multiplication with numbers larger than 2^10, pre-computed mode shows a performance bottleneck due a exponential execution time dependence on the number of bits. For this reason, an additional mode for arithmetic support has been developed.


2. Ad-hoc mode computes arithmetic operations with alternative strategy. TML will first evaluate the possible values for the input operands and then compute the set of results of the binary operation. It provides reduced capability compared to pre-computed mode, specifically it won't preserve the relationship between the operands but just evaluate the right hand side of the expression. On the other hand it allows  to handle multiplication of larger numbers.

Example 2:

    U(15).
    A(?x) :- ?x = 5.
    B(?x) :- ?x <= 2.
    adhoc_mult(?z) :- A(?x), B(?y), pw_mult(?x ?y ?z).

    will result with:
    ad_hoc_mult(10).
    ad_hoc_mult(5).
    ad_hoc_mult(0).

Table below summarizes current arithmetic operator support:

| Operation | Contractive Mode | Expansive Mode |
| --------- | ---------------- | -------------- |
| addition | ?x + ?y = ?z | pw_add(?x ?y ?z) |
| multiplication | ?x * ?y = ?z | pw_mult(?x ?y ?z) |
| bitwise AND | ?x & ?y = ?z | bw_and(?x ?y ?z) |
| bitwise OR | ?x  \| ?y = ?z | bw_or(?x ?y ?z) |
| bitwise XOR | ?x ^ ?y = ?z | bw_xor(?x ?y ?z) |
| bitwise NOT | TBD | bw_not(?x ?z) |
| shift-left | ?x << const = ?z | - |
| shift-right | ?x >> const = ?z | - |


Finally, special attention deserves the precision of the arithmetic operations. By default they will operate modulo 2^n, where n is the number of bits required for MAX (maximum number in the program), this means that any overflow will be discarded.

Example 3:

    U(7).
    mult_mod8(?x) :- ?x * 2  = 2.

    will result with:
    mult_mod8(1).
    mult_mod8(5).

Alternatively, if the user requires extended precision to keep all information on the right side of the equality (the ?z variable in the examples above), both addition and multiplication can be used as below:

    U(15).
    ext_prec(?zh ?zl) :- ?x = 6, ?y = 4, ?x * ?y = ?zh ?zl.

    will result with:
    ext_prec(1 8). #notice: 1*2^4 + 8 = 24

where ?zh accounts for the most significant bits (MSBs) of the operation and ?zl for the least significant bits (LSBs).


# Misc

Comments are either C-style /* \*/ multiline comments, or # to comment till
the end of the line.

# Philosophy

TBD

# Future Work

* Support !=, <, >, min, max.
* Backward chaining and focused goal resolution.
* More grammar and string builtins.
* BDD level garbage collection.
* Improved syntax.
* TBD

# Further Examples

TBD
