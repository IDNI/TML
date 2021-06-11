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

## Fact deletion

It is also possible to use negated facts. These are deleted right after
non-negated facts are added and right before rules are being executed.

    a(2). b(?x).
    ~b(1). ~a(?x).
    a_copy(?x) :- a(?x).
    b_copy(?x) :- b(?x).

will result with

    b(2).
    b(0).
    b_copy(2).
    b_copy(0).

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

# Nested programs

It is possible to nest programs (actually whole sequences). Sequence of nested
programs is run after the current (parent) program reaches its fixed point.

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

# Macro feature.

TML allows using macro that can be expanded internally. To define macro,  := is used.
For example, atc macro is  defined as:

    e(1 2).
    e(2 3).
    e(3 4).
    atc(?a ?b ?c) := e(?a ?b), e(?b ?c).
    tc(?x ?y ?z) :- atc(?x ?y ?z).

This will expand to tc to

    tc(?x ?y ?z) :- e(?x ?y), e(?y ?z)

The variables in the body of the macro are replaced with that at the point of call, and then the body is expanded.

Another variation is where the variables are partially specified in the macro term, that itself is an argument.

    atc(?a ?b ) :=  e(?a ?b).
    ttc(?x ?y) :- ntc(atc(?x)).
    ntc(?a ).
 
This will expand macro atc as

    ttc(?x ?y) :- 
            ntc(?0f10),
            e(?x ?0f10).

Here a new fresh variable ?0f10 is introduced.

# EBNF support

TML grammar can take EBNF syntax as well. It supports { } for zero or more occurrence, [ ] for optional, and ( ) for grouping terms. Further  * and +  are postfix operators that can be applied.

    @string str "aabbccdd".
    A => ('a')*. 
    B => 'b'+.
    C => 'c'*.
    D => 'd''d'
    S => A B C D

Here 'a' can occur zero or more times and 'b' can occur one or more time. Internally, TML shall replace it with fresh production symbols that would do recursion. A more complex example is

    A => { [ 'a' { [ 'a' ] } [ 'f' ] ] } .
    C => 'c' + .
    B => 'b' [ B ] .          # B occurs one or zero time.
    D => ( 'd' 'd' ) * .      # ( ) allows * operator to be applied to all terms as a whole.
    S => A * B + C * D + | A + ( B * ) .
    K => ( C + ) * [ B + ] .

# Grammar Constraints 

TML allows adding constraints to a simple grammar production. 
These constraints refer to the properties of symbols through their relative position 
in the right hand side, starting from 1. Internally, TML translates them into terms. 
There are two types of constraints supported .  
- len(i) is the size of the string derived from symbol at position i. 
- substr(i) is the substring content derived from a symbol at position i.

Example 1:
Consider the following grammar.

    @string str "aabbcc".
    A => 'a' A 'b' | "ab" .
    C => 'c'C .
    C => 'c' .
    S => A C ,  len(2) + len(2) = len(1) .

Here the constraints are specified for S production where the length of the derived string from A should be twice the length derived from C. 
Note that due to constraints it would not accept "abc".

Example 2
Another example using string comparison.

    @string str "cccaccc".
    C => 'c' C .
    C => 'c' | 'z'.
    A => 'a' A | 'a'.
    S => C A C, substr(1) = substr(3), len(2) = 1.

Here the derived content of both Cs should match.  

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

| Operation | Pre-computed     | Ad-hoc         |
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

# Counting number of records in relations

For getting number of records in a relation TML provides count builtin. It is
usable in bodies. It has no input argument and it has one output argument which
is the number of records matching rule's body.

Result of the count builtin is not accessible in the same rule's body, it can be
only passed to terms in head. If it is necessary to use the count result in
a body it has to be stored into the db first (use head term) and then the value
can be accessed in a body in a next step.

Example:
```
	A(1). A(2). A(3).

	# wrong because ?l can be passed only to head
	len_is_3  :- A(?x), count(?l), ?l = 3. 

	# length of A is stored in A_len and in another rule it is checked
	A_len(?l) :- A(?x), count(?l).        
	len_is_3  :- A_len(?l), ?l = 3.
```

# Fixed point detection programatically

TML programmer can enable fixed point step by `-fp` (`-fp-step`) command line
option. This option makes TML interpret to add a `__fp__` fact into program's
database when it reaches a fixed point and it continues with execution until
another fixed point. If `__fp__` fact exists in the database already it halts
the execution.

This way a TML programmer can have a rule depending on the `__fp__` fact.
To continue execution of the program remove the `__fp__` fact.

This fact is filtered out when printing the database data.

# Rule guards

To enable or disable a rule we can use additional term in rule's body. Existence
of such a term guards execution of the rule.

```
	guard.                      # guard fact is required for execution of
	a_copy(?x) :- a(?x), guard. # this rule
```

# Transform guards

By using `-guards` (`-g`) command line option we can transform a TML program
containing nested programs or **if** or **while** statements into a single TML
program which uses rule guards to control execution of each program's state.

To properly guard execution of nested programs it is required to transform
all statements into a guarded rule. Because adds, dels, rules execution, and
**if** and **while** conditions need to happen in a sequence we need to
transform each program into several consecutive states (`N` is an id of the
program): start state: `__N__start__`, adds state: `__N__add__`, deletions
state: `__N__del__`, rules state: `__N__rule__`, conditions state: `__N__cond__`
and a fixed point state: `__N__fp__`.

`__N__start` state is the beginning state of the program if it is a **while**
guarded program, so its execution can be breaken before other states of the 
program happen. if the program is guarded by **while** it also adds a
`__N__curr__` fact. This fact guards the breaking condition of the **while**
command.

Not all states are always present in each program.

Program containing an adding of a fact will have `__N__add__` state.
If program contains a deletion of a fact it will have `__N__del__` state.
Program with at least a rule will have `__N__rule__` state.
If there is an **if** condition it will have `__N__cond__` state.
Program guarded by a **while** condition will have `__N__start__` state and it
will also keep the `__N__curr__` fact existing while the program is running.
So far only `__N__fp__` is the only state which is always present even in an
empty program. (It is expected that this state would be optimized out too.)

Transitioning from one state to another is done by state transitioning rules:

```
	~__previous_state__, __new_state__ :- __previous_state__.
```

All program states take only a single step of the resulting TML program but the
`__N__rule__` state. Rules state needs to run until the current program
(rules guarded by `__N__rule__`) reaches its fixed point.
To detect a fixed point of the program (in `__N__rule__` state) programatically
we enable the [fp step](#fixed-point-detection-programatically) (`-g` enables
`-fp` automatically) feature.

With `__fp__` internal fact we can detect fixed point of a nested program and we
can end the `__N__rule__` state and continue to the `__N__fp__` state:

```
	~__1__rule__, __1__fp__, ~__fp__ :- __1__rule__, __fp__.
```

The last state of the program is `__N__fp__` state. Existence of this fact
guards execution of the program which follows in the sequence.

Example: a simple program
 
```
	 fact1, fact2.
	~fact2.
	 rule1         :- fact1.
```

becomes:

```
	 __0__fp__.   # initial state of a TML program
	 fact1, fact2                    :- __1__add__.
	~fact2                           :- __1__del__.
	 rule1                           :- __1__rule__, fact1.
	~__0__fp__,   __1__add__         :- __0__fp__.
	~__1__add__,  __1__del__         :- __1__add__.
	~__1__del__,  __1__rule__        :- __1__del__.
	~__1__rule__, __1__fp__, ~__fp__ :- __1__rule__, __fp__.
	~__1__fp__                       :- __1__fp__.
```

A nested program:

```
	{ a(3). { a(2). } a(1). }
```

transforms into:

```
	 __0__fp__.
	~__0__fp__,  __1__fp__  :- __0__fp__.
	~__1__fp__              :- __1__fp__.
	 a(3)                   :- __2__add__.
	 a(1)                   :- __2__add__.
	~__1__fp__,  __2__add__ :- __1__fp__.
	~__2__add__, __2__fp__  :- __2__add__.
	~__2__fp__              :- __2__fp__.
	 a(2)                   :- __3__add__.
	~__2__fp__,  __3__add__ :- __2__fp__.
	~__3__add__, __3__fp__  :- __3__add__.
	~__3__fp__              :- __3__fp__.
```

To see the `-g` transformed program use `-t` command line option.

# Guarding statements

Guard transformation also enables usage of **if** and **while** statements.
First order formula is used as a condition. Guarded code is always nested
eventhough it does not have to be surrounded by '{' and '}' if it is just
a single rule or another guarding statement.

## if then (else)

Syntax of **if** statement is:

```
	if FORM then STATEMENT.                   # or
	if FORM then STATEMENT else STATEMENT.
```

FORM is a first order formula and STATEMENT can be another guarding statement,
a nested program or a rule (note that STATEMENT is always nested. It is parsed
as a nested program, ie. `rule.` is parsed as `{ rule. }`).

Example program:

```
	A(10).
	if exists ?x { A(?x) } then A_not_empty. else { A_empty. }
```

is equivalent to:

```
	A(10).
	if exists ?x { A(?x) } then { A_not_empty. } else A_empty.
```

produces result:

```
	A(10).
	A_not_empty.
```

**if** is implemented by transformation of a condition (FO formula) into a rule
which is executed (condition is decided) when fp of the current program is
reached.

For above example such a rule would be.

```
	__1__2__guard__ :- { __1__cond__ && { exists  ?x  { A(?x) } } }.
```

Execution of each respective (true/false) nested program block is guarded by
existence or non-existence of the `__1__2__guard`.

Full example program transformed:

```
	 __0__fp__.
	 A(10)                        :- __1__add__.
	~__0__fp__,       __1__add__  :- __0__fp__.
	~__1__add__,      __1__cond__ :- __1__add__.
	~__1__cond__,     __1__fp__   :- __1__cond__.
	~__1__fp__                    :- __1__fp__.
	 A_not_empty                  :- __2__add__.
	~__1__2__guard__, __2__add__  :- __1__fp__,  __1__2__guard__.
	~__2__add__,      __2__fp__   :- __2__add__.
	~__2__fp__                    :- __2__fp__.
	 A_empty                      :- __3__add__.
	 __3__add__                   :- __1__fp__, ~__1__2__guard__.
	~__3__add__,      __3__fp__   :- __3__add__.
	~__3__fp__                    :- __3__fp__.
	 __1__2__guard__
		:- { __1__cond__ && { exists  ?x  { A(?x) } } }.
```

## while do

Syntax of **while** statement:

```
	while FORM do STATEMENT.
```

FORM is a first order formula and STATEMENT can be another guarding statement,
a nested program or a rule.

Example program:

```
	a(0). a(1). a(2). a(3). a(4).
	i(0).
	while ~ { b(1) } do {
	        b(?x), i(?x1), ~a(?x), ~i(?x) :-
	                a(?x),  i(?x), ?x + 1 = ?x1.
	}
```

outputs following

```
	a(4).
	a(3).
	i(3).
	b(2).
	b(1).
	b(0).
```

Note that while the guard rule for the **if** statement is executed when the
parent program enters its fixed point state, condition of the **while**
statement is checked each step of the nested program even before the add state.

**while** condition is negated into a breaking rule. When the rule becomes true
it breaks the execution of the current program and reaches the fixed point.

Condition `~ { b(1) }` is transformed into this breaking rule:

```
	~__2__curr__, ~__2__start__, ~__2__rule__, __2__fp__
	        :- { __2__curr__ && ~ ~ { b(1) }   }.
```

Full transformation of the above program:

```
	__0__fp__.
	a(0), a(1), a(2), a(3), a(4), i(0)            :- __1__add__.
	~__0__fp__,    __1__add__                     :- __0__fp__.
	~__1__add__,   __1__fp__                      :- __1__add__.
	~__1__fp__                                    :- __1__fp__.
	b(?x), i(?x1), ~a(?x), ~i(?x)
	        :- a(?x), i(?x), ?x+1=?x1,               __2__rule__.
	~__1__fp__,    __2__start__, __2__curr__      :- __1__fp__.
	~__2__start__, __2__rule__                    :- __2__start__.
	~__2__rule__,  ~__fp__, __2__fp__             :- __2__rule__, __fp__.
	~__2__curr__                                  :- __2__fp__, __2__curr__.
	~__2__fp__                                    :- __2__fp__.
	~__2__curr__, ~__2__start__, ~__2__rule__, __2__fp__
	        :- { __2__curr__ && ~ ~ { b(1) }   }.
```
# Types and Type checking

One can specify types for arguments of terms and predicates in the program. There are three primitive types **"int", "char" and "sym"** with default size of 4 bits each. The int can be further specialized with bit size like **int:2**, which says it is a type which holds only 2 bits ( possible four values).

The predicates type signature can be specified with keyword **predtype** preceding relation/predicate name and by including types of the arguments as in example, 

```

predtype father( sym ?b).
record edge (int:3 ?c, int:2 ?c ).
record pair(int ?a, char ?b).

```

Here, father predicate can take argument of type sym, symbols. "edge" takes first argument of type 3 bit size and second as type 2 bits size.

## Running checker for type errors
The type checking will check for various type errors in the TML program for example. Running following program with "tml --bitunv " option will invoke the typechecking on the TML rules. ( the flage option would be removed in future, though currently specific)

The following program has type mismatch for ?x in first rule. Running it with -bitunv option produces error
```
predtype e( int:5 ?a,  int:5 ?b).
predtype tc( int:6 ?a, int:5 ?b).
e(1 2 ).

tc(?x ?y) :- e(?x ?z), tc(?z ?y).
tc(?x ?y) :- e(?x ?y).

Type error: "Type int:6 of ?x does not match expected type int:5 in predicate e(?x ?z)" close to "?x ?z), tc(?z ?y)."
```

Here ?x has expected type of int:6 as per "tc" signature, while int:5 as per "e". This results in type mismatch. 

## Complex types with Struct

One can specify complex types with **struct** key word like. 

```
struct person {
    char ?y.
    int ?age.
}.
```

The total size of this person type is now the sum of all primitive types. One can also nest struct within a struct type like this.
```
struct address {
    int ?num
    person ?p.
}.
```
At the moment, the individual members of struct are not accessible (in future).

## Type Errors

Other examples of type errors are wrong arity, undefined types, exceeding max bit sizes etc. For example, for program below, we get
```
struct sttyp2 {
    char ?y.
    sttyp2 ?recursive_not_Allowed.
}
struct styp {
    int:2 ?c, ?z .
    sttyp2 ?inner, ?in3.
}
predtype father( sym ?b).
predtype canFly( sym ?c ).
predtype edge (int:3 ?c, int:2 ?c ).
predtype night( int:2 ?A).
predtype pair(int ?a, char ?b).
predtype school ( undeftype ?name,  sttyp2 ?l ).

father(fff wrongargcount).
#father(Tom Amy).  
canFly(bird).      
#canFly("bird").
edge('c' 1).         # typemismatch
night(4).             # It's night.
pair(1 2).         # typemismatch
edge(?x ?y) :- edge(?x ?z), edge(?z ?y).
school( notyet notyet).

Type error: "Expected arity for father(fff wrongargcount) is 1" close to "father(fff wrongargcount)."
Type error: "Expected type for argument 1:c is int:3 in predicate edge('c' 1)"
Type error: "Expected type for argument 2:2 is char in predicate pair(1 2)" close to "2).         # typemismatch"
Type error: "Type int:2 of ?z does not match expected type int:3 in predicate edge(?z ?y)" close to "?z ?y)."
Type error: "Type undeftype of notyet is undefined" close to "notyet notyet)."
Type error: "4 exceeds max size for int:2 in predicate night(4)" close to "4).             # It's night."

```

# Conjunctive Query Containment (CQC)
This section lists the optimizations based on CQC tests that have been
implemented in the interpreter, what exactly they do to TML source code,
the command line flags required to enable them, and their potential
drawbacks. Note that the flag `--3pfp` should be enabled when using any
of these optimizations because their internals sometimes cause
alternating fixpoints. Note also that the results of a program obtained
by applying these optimizations to another should be indistinguishable
from those of the original.

## Subsumption without Negation
This pair of optimizations is based on the CQC test as described on
section 1.1 of "Information Integration Using Logical Views" by Ullman.

The first of the optimization pair tries to identify redundant conjunctive
rules in a TML codebase. It does this by iterating through all unordered
pairs of conjunctive rules corresponding to the same relation and formally
checking whether the facts derived by one rule are necessarily derived by
the other rule. If this is the case, then it follows that the former rule
is redundant.

The second of the optimization pair tries to identify redundant terms in
conjunctive rule bodies by checking whether a rule is contained by one
obtained by removing a body term. If this is so then the body term can be
removed to obtain an equivalent rule since this rule's derivation set would
both be a subset and superset of the original's.

This optimization can be enabled using the flag `--cqc-subsume`.
## Subsumption with Negation
This pair of optimizations is based on the Conjunctive Query Containment
(CQNC) test as described in section 1.2 of "Information Integration Using
Logical Views" by Ullman.

The details of this optimization pair are the same as those of the
negation-less case as described above, except this pair additionally works
on conjunctive rules containing terms with negation. This optimization pair
is strictly more general than those for the negation-less case, however
this comes at a cost: this optimization pair is much slower than the one
for the negation-less case. This can be seen from the Ullman paper where
the containment checker must iterate through partitions of a given set and
amongst other operations, iterate through the powerset of the set of terms
formed by taking the cartesian power of some set of atoms.

This optimization can be enabled using the flag `--cqnc-subsume`.
## Factorization
This algorithm shares a similar spirit to the CQC test in that it
searches for homomorphisms between different rules. The difference here
though is that rule heads are not included in the homomorphism checks.
This exclusion allows us to check whether certain body parts of a rule
are contained by the body parts of another. And when containment is
verified, we simply create another rule corresponding to the intersection
of the original rules and make the original rules point to this newly
created rules.

This optimization can cause the TML program to slowdown so when it
is desired to increase the speed of a TML program, one should try running
it both with and without this optimization and proceed accordingly. The
potential slowdown can be attributed to the fact that additional terms
and rules are required to correctly sequence the temporary rules in the
case that the original program used negation.

This optimization can be enabled using the flag `--cqc-factor`.

# Self Interpretation
This section lists the directives provided to support
self-interpretation, how to invoke them, and what they do at runtime.
The flag `--3pfp` should be used in conjunction with these dirrectives
because their internals sometimes cause alternating fixpoints. Note
that anything that can be achieved using these directives can also
be achieved without them in pure TML.

## Domain
The domain directive creates a domain over which a quoted program can
be defined and executed. Conceptually it is necessary to allow quoted
programs to manipulate terms of arbitrary arities without requiring
changes/extensions to the quotation schema nor the quotation operator
nor the evaluation operator. Concretely it is required to instantiate
quotations, evaluators, and codecs.

This directive has the following syntax:
`@domain <domain_sym> <limit_num> <arity_num>.`. Here `<domain_sym>` is
the prefix that all relations generated for the domain should have.
`<limit_num>` is the tuple element domain size. And `<arity_num>` is the
maximum length of the tuples generated for this domain.

An example of usage:
```
@domain dom 7 3.
```

## Quote
The quote directive takes a literal TML program and creates a relation
that when correctly interpreted produces the same facts that would have
been produced by the literal program. Conceptually it is required to
enable TML programs to manipulate and inspect other TML programs.
Concretely it is required to instantiate evaluators.

This directive has the following syntax:
`@quote <quote_sym> <domain_sym> <quote_str>.` Here `<quote_sym>` is the
prefix that all relations generated for the quotation should have.
`<domain_sym>` is the domain over which arbitrary length fragments (like
terms) in the quotation are defined. Additionally the `<limit_num>` of
the domain must be more than or equal to the maximum number of distinct
variables used in a rule of `<quote_str>` because variables are encoded
as numbers. Also the `<limit_num>` of the domain must be more than the
largest number occuring in `<quote_str>`. Also, the `<arity_num>` of the
domain must be more than or equal to the maximum of the term arities
occuring in `<quote_str>` because term tuples are represented by lists.
(This setup is what allows us to encode arbitrary arity terms without
modifications to the schema.) `<quote_str>` is a literal TML program
surrounded in backquotes to quote.

An example of usage:
```
@quote quote dom `
  u(0).
  d(0).
  c() :- forall ?x {u(?x) -> d(?x)}.`.
```

Currently the quote operator only supports TML programs with facts,
rules, and formulas utilizing only variables and numbers. There are
plans to extend this to symbols, arithmetic, and eventually the rest of
TML.
## Eval
The evaluate directive takes a relation containing a quotation and a
relation containing a domain and creates a relation containing the facts
that would have been derived by the original program that was quoted.
Conceptually it is required to see what the program represented by a
(potentially statically unknown) relation would produce at runtime.
Concretely it is required to instantiate codecs.

This directive has the following syntax:
`@eval <eval_sym> <domain_sym> <quote_sym> <timeout_num>.` Here
`<eval_sym>` is the prefix that all relations generated for the
interpreter should have. `<domain_sym>` is the relation name of the
domain representing the universe over which the quoted program should be
interpreted. `<quote_sym>` is the relation containing the quoted program
to run. Additionally, the `<arity_num>` of `<domain_sym>` must be more
than or equal to the maximum number of variables used by a rule in
`<quote_sym>` because the value of each variable is stored in a list
during interpretation. `<timeout_num>` is the number of steps of the quoted program
that should be simulated.

An example of usage:
```
@eval out dom quote 50.
```
## Codec
The codec directive takes a relation containing a domain, a relation
containing an interpreter, and a maximum term arity; and produces a
relation containing a decoding of the facts produced by the interpreter.
Conceptually it is necessary because the evaluator's lack of dependence
on specific arity maximums forces it to produce outputs that are encoded
and hence are hard to debug/use.

This directive has the following syntax:
`@codec <codec_sym> <domain_sym> <eval_sym> <arity_num>.` Here
`<codec_sym>` is the prefix that all relations generated or the codec
should have. `<domain_sym>` is the relation name of the domain that will
be used to decode the encoded outputs of an evaluator. `<eval_sym>` is
the relation name of the evaluator whose outputs are being decoded.
`<arity_num>` is the maximum arity of the terms being decoded.

An example of usage:
```
@codec cdc dom out 3.
```

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
