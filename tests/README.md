# Regression testing

Be in the `tests` directory and run: `./tests_runner.sh <dir>` to run all *.tml
files from the dir and compare its outputs with expected ones.

Example: `./tests_runner.sh ./regression`
or `./tests_runner.sh ./intro`

To save tests' outputs as expected after adding or changing a test program
append the `--save` argument to the command. Be sure your programs are working
fine before storing their outputs as expected.

Example: `./tests_runner.sh ./regression --save`

#Macro feature.

TML allows using macro that can be expanded internally. To define macro,  := is used.
For example, atc macro is  defined as,

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
D => 'd''d'.
S => A B C D

Here 'a' can occur zero or more times and 'b' can occur one or more time. Internally, TML shall replace it with fresh production symbols that would do recursion. A more complex example is

A => { [ 'a' { [ 'a' ] } [ 'f' ] ] } .
C => 'c' + .
B => 'b' [ B ] .          # B occurs one or zero time.
D => ( 'd' 'd' ) * .      # ( ) allows * operator to be applied to all terms as a whole.
S => A * B + C * D + | A + ( B * ) .
K => ( C + ) * [ B + ] .