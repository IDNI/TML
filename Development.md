# Introduction

Note: types mentioned here are actually 'kinds' (as in type theory).

# Universe

# Builtins

There're two types of builtins at the moment from the implementation perspective: 
a) head/left-hand-side (lhs) and  
b) right-hand-side (rhs).  

> there're a good deal more: external/internal; then bdd-s, terms or raw terms 
(I guess compressed/decompressed too) - frankly I'm not really sure of the actual 
details here till we implement some examples for each.
  
##### How to implement 

- `str_bltins` (input.h) - add your builtin to the set.  
(TODO: we should reorg this to support externally loaded builtins)
- `alt` contains the builtin data (alt is the holder of the builtin data) - 
for the rhs builtins.  
- builtin is a term, but initially it was decided to allow only 
**one builtin per alt** (I can't find it but I'm pretty sure:). I'm not sure if 
this is wise, but it's a limitation atm (technically speaking there's no 
reason why we couldn't keep a list of builtins per alt). However, you can have 
one builtin in the head (lhs) and one on the rhs, as those are kept separately 
(more below).  
- `a.idbltin` (i.e. `alt.idbltin`) - is `>=0` if a term is a builtin. And 
`lexeme bltintype = dict.get_bltin(a.idbltin)` to get the type/name.   
- `a.bltinargs` - has all the builtin args.
- `a.bltinsize` - has # of vars.
- `bltinout = a.bltinargs.back()` - e.g. to get the last `?out` var (in case 
builtin has one). And `a.vm.at(bltinout)` to get the arg position in the alt. 
Then you can use that (alongside `a.varslen`, `a.bm`) for any bdd ops needed.
- rhs builtins are typically implemented inside the `alt_query()` 
(see `count, rnd`).
- head/lhs builtin info is kept with the table (as it's a rule), same members.
- best place to implement it is within `fwd()` (e.g. `lprint, halt, fail`). 
- lprint implementation details: this depends on what we want to achieve, but 
basically we're watching the builtin table's bdd for any changes (or when done), 
then decompressing, filtering for any new items and outputing (in this case). 
Decompressing is slow so do it only if something changes (or when done), not on
each step (it's required here so we can't avoid it).
- TBD.
  
##### Type Inference & Builtins

You also need to implement *type inference* for any new builtin.  

See `count` specifics in the *infer_types.cpp* (`get_alt_types`).  
This is a bit more involving (more below) but simply put if the builtin 
influences or adds a new arg/type, then builtin is the one responsible for it. 
Typically that involves calling the `bitsmeta::sync_types` with the alt/arg +
also with the table/arg (behind the alt), if arg is in the head.   

This makes sense for `count` as count introduces the `?out` var, which is 
numeric.  

##### Type Inference and Ops

This also goes for any new ops/features.   

Similarly this should be done for arithmetics (or any new operators etc.), as 
depending on the op the type needs to be set (whether that's the result or 
whatever).  


# Variable Bits

- fixed `bits` (and universe counters `nums chars syms`) is no longer defined. 
So everything that uses bits (which is bdd-s or related to it) needs to use 
*variable bits* now.  

- `bits` were used under the hood, as it was global. `variable bits` need to 
be specified and passed into each relevant call.  

- bdd-s (and args, types) are typically defined either at a) alt level, or at b) 
table level. Also any custom handling (like arithmetics) defines it's own bdd-s.
I call those *bdd-holders* (or *bdd-context* is better probably?).  

- for each of those we need to have a *variable-bits* structure properly 
initialized - which is `bitsmeta`. The `bitsmeta` keeps all the relevant data 
about arguments and types. Where you used `bits` before, you need to pass 
`.bm` now (loosely speaking).  

- `bits` equivaluent is `bm.types[arg].bitness` - i.e. you need an argument,
bits is meaningful only 'per arg'. One consequence is that you always have to 
iterate over args first, get the bits then iterate over bits (e.g. arithmetics).  

- `args * bits` equivalent (of total # of bits) is `bm.args_bits`.  

- `bm.get_args()` to get # of arguments, which is equivalent to either 
`a.varslen` or `table.len`.

- When you call `from_sym | from_sym_eq | leq_const ...` you need to pass to 
it a `bitsmeta`. `bitsmeta` is sort of a *context* for any bdd-related call. 
Similarly for any low-level bdd op you'd need to use `bitsmeta::pos()`. I.e. 
anything you do with bits, bdd-s, requires a `bitsmeta` instance (or two). 
~~There's an overload variant for most functions (i.e. you can pass either `a.bm`
or just `a`, usually the last param)~~. Ideally this should e.g. go into a 
base (template) for alt/table, so you won't need to pass anything, but the code 
reshuffling needed was just too much for this pass (needs some more thinking).  

- which .bm (bitsmeta) to use: it's usually clear from the context, if you're
dealing with a table (if `arg` is tbl arg or `args` is tbl.len) use `tbl.bm`,
if `a.vm` was used or `a.varslen` is passed - use `a.bm` (total # of args is
usually a very good indicator).  

- for ex/perm it's a slightly different story. To use ex/perm, you don't need 
anything special (and chances are that's all you'll ever need to do). To 
initialize ex/perm of any kind you always need to pass two `.bm` structs, as
you're mapping from one set of arguments to another (varying in #, positions, 
bitness<sup>[1](#foot1)</sup> etc.). **This may be of interest to arithmetics**, as there we have 
neither tbl nor alt args/bits, but a custom arrangement (so ex/perm will 
probably have to be made from scratch). Note: this changes for compounds.  

- when creating a custom table, i.e. if it's not done automatically in 
`from_raw_term` (as is the case for `load_string`, `transform_grammar` or 
`transform_bin`, `tml_update`...), types / args need to be specified properly 
(e.g. arithmetics again, see those implementations for more).  

- *variable bits* also affect how things need to be initialized, and in which 
order. **All `bitsmeta`** structs (tbl or alt) **need to be constructed & 
initialized before any bdd op** is done (i.e. before the first bdd call). If any
changes are made to the `bitsmeta` (type, bitness, # of args, ordering) => we
need to permute all bdd-s for that bdd-context (tbl, alt or custom). That is 
supported too (`AddBits` and `add_bit`, `permute_type`, more below) but it's 
costly (and needed only in special cases). That's the reason for added 
complexity in `add_prog` initialization (we first init bitsmeta for all, grammar
too, do type inference, init tables/alts, and only then proceed w/ get_rules).
This doesn't affect custom bdd contexts (like arithmetics) as long as you init 
before doing any bdd ops.  

- `nums` in `bitsmeta`: what was `nums` before, it's now 'per arg'. When 
creating custom bdd context (or custom table) you need to supply both `types` 
and `nums`. Nums is basically the upper limit of the universe for that arg, only
for numerics (i.e. the max numeric value, per arg). Chars is known, and syms 
(for symbols) is still not implemented properly yet, all syms share one universe.
Note: this changed slightly, num is now saved with the type itself.


### Types  

Types are essential for `bitsmeta` (there's a type for each arg).  
  
- `arg_type` - is the base type structure for predefined or built-in types 
(sort of primitives + symbols + strings). Naming will change, to be renamed to
(`type`, ~~`builtin_type : type`~~). That'd be extended further with e.g. 
something like `sub_type`, `record_type` etc. to support custom types.  

- we need to define how custom types will be specified (parser).  

- types have to match (for related arguments), see readme.md also.  

- bitness is either specified (`:type[bitness]`), inferred (from related args),
or calculated from consts used (for numerics mostly, syms also to come).  

- symbols are not finished yet properly, all share the same universe (due to the 
`dict` dependency). We need to split symbols 'per arg' instead. TBD.  

- symbols vs strings - and `str | sym` - TBD.   

- dependent args/types are matched (inference) but we still keep copies of 
all those identical types all over the place. Couple reasons: a) laziness; b)
types have very small footprint (could go into one int if needed) and we rarely
change them (once set up, only in `add_bit`); c) if we add *casting* dependent
types will no longer be 'equated' and we can have similar types but with 
differences. So, I'm unsure if we really want to 'compress' that any further.  

- there's one difference in output and universe handling from fixed to variable. 
Universe can no longer be anything, like both numeric and char and sym at the 
same time (for one arg). That rarely showed up before but it can be seen with 
`transform_bin` (and `tml.g`), temp `r` tables have final output with 'mixed 
universe'. With types and current variable bits, universe is 'strongly typed' 
and an arg can have only one specific type (num, chr or str). If we'd really 
need to have it 'mixed' then we can add a `union_type` to specifically enable 
it.

**note**:  `type` is now the base type, support for compound terms was added, 
more info coming up. TBD.

### Type Inference  

- Inference is done via `sync_types` (bitsmeta) and `map_type` (infer_types) 
(`sync_types` syncs similar arg/types, while `map_type` builds dependency maps 
and `propagate_types` makes sure all args have the latest / best type).  

- Inference is quite detailed, it goes and matches alts, bodies/tables, takes all
ops (e.g. relational `< <= ==`) & builtins specifics into account. That was 
necessary to be able to run any old TML w/o any manual typing.  

- some things are assumed (which may not always be desired), e.g. if we have 
`r(?v1 ?v1)` we assume that type(r, 0)==type(r, 1), as that's logical. Also,
if same vars are used in different places, we assume that those arguments have
the same type. That is simplifed, helps, but may not always be what we want
(though I don't see how to avoid it, it's a logical issue of such tml - or we 
may be missing some advanced features, but given current scope we can't do more
IMO). 

- `minvtyps` - is a full dependency list of args/types. Keys hold all 'root' 
types (usually there're only a few of those) and `minvtyps[root]` holds all 
dependent types. `mtyps` is inverse of that, `get_root_type` etc. This 
dependency doesn't imply 'direction' or tables dependency, it's not like `deps`. 

- inference maps (the above) are now used for add_bit (AddBits) as well (which
is more optimal).  

TBD.

### Dynamic Universe

This was the trickiest of all. We can now basically add bits (expand universe),
or change bits order, change vars order etc.

##### bits order
- we can order args/bits in any way we like, at compile time, or at runtime.
E.g. (0..bits0)(0..bits1)...(0...bitsN), or like it is now, args-together 
(same-bit):

|0 | 1 | 2 | 3 |  args |
|:---:|:---:|:---:|:---:|:---:|
|0 | 0 | 0 | 0 | |
|1 | 1 | 1 | 1 | |
|2 | 2 | 2 |   | |
|3 | 3 | 3 |   | |
|4 | 4 | 4 |   | |
|5 | 5 | 5 |   | |
|  | 6 | 6 |   | |
|  | 7 | 7 |   | |
|  | 8 | 8 |   | |
|  | 9 | 9 |   | |
|  |   | 10|   | |
|  |   | 11|   | 0-bit (goes up) |


TBD.

##### addbit

- it can be tested with `--addbit`, one bit will be added (on arbitrary 
tbl/arg), universe will increase and all should go on as before.  

- it is called like `AddBits.permute_type({tab, arg});` in `fwd` or similar. 
Also, some more details in tables_ext.cpp (commented out) and in `fwd`.  

- it adds a bit, propagates the change (to all depending type/args), reinits all
bitsmeta-s, tbl-s, alt-s - and permutes all bdd-s. 

- ~~currently supported is `addbit(1)` (one bit at the time)~~, addbit(n-bits) 
is fully supported, also sequences which change bits and practically anything we
may want to do (rotating, changing var order and so on).  

- to change var positions we need to set the `vargs` and call the same routine
(see `init_bits` for more, there we change bits and call addbit 'after the 
fact' just to re-permute things, we can do the same w/o any bits added, just 
having the order of vars changed - not tested well though).

##### addbit and sequences

- There were some tricky issues with previous (fixed bits) implementation (bits 
/ nums that changes with new sequence, also `consts bit-encoding` vs `addbit` 
direction didn't match, `from-left` or `from-right`). This should now be fully 
stable and supporting any bits change, layout, order etc.  

- This also solves the 'universe overflow' issue that was reported.  
`{a(1).m(120).} {m(128).}`  

- ~~`get_facts` overwriting / anulling for new sequences~~ - fixed.

### Compound terms

Note: 'term' has 2 uses here, in tml code term is `A( a(b(c)) 1).` as a whole 
(or `A(?x 1), ...` where A is a table), while in this case compound term is 
just an argument within it.

Compounds is a special type of argument (somewhat like prolog's compound terms / 
structures) that allows us to build lists, trees (and graphs to be) from the
primitive arguments (and variables). E.g. in `A( a(b(c)) 1).` `a(b(c))` 
is a compound argument (while 1 is still a primitive, A is a table of arity 2).

Compounds can be used like any other primitive argument and can be substituted,
e.g. if we do `... :- A(?x 1).` ?x will become `a(b(c))`. All ops and basic
bdd functions are implemented and should work transparently on primitives or 
compounds alike (e.g. EQ should work, as from_sym does).

Compounds also support 'inside' variables (with limitations), so you can 
substitute the compound as a whole, or one of its parts. So, supported is 
`A(?x)` (?x represents full compound) but also `A(a(?x))` (?x is the 'rest').
It could also be in the middle but only for fixed-length/known compounds.
For recursive (potentially large / unknown size scenarios) we need to use couple
supported builtins to compose, decompose etc.
As a rule of thumb, a) 'lone' variable represents the compound as a whole; b) 
variable at the beginning represents the head/first primitive value; c) variable
at the end represents whatever is left of the compound (i.e. the 'rest').

Compound is also a list or array - e.g. a string of chars. At the moment we can 
load and search within a string (only a prototype at the moment), more & details 
coming up (TBD).

Compounds are not tables but only arguments within tables. This is different 
from what prolog supports (where compound terms are also used to define rules 
and are in that sense more powerful). This was by specs/design but is also the 
limitation of tml's tables design and strongly-typed implementation (we need to
have 'bits' defined ahead of time, even with varbits). IMO that's something to 
think about and try to define it well and make it future proof.

Performance is largely related to possible # of bits involved. Also, compounds 
are not yet optimized for large arrays (like loading a file) but that's expected
to work fine (providing bdd size is not an issue).

##### Compounds and Types

Types are updated to support compounds natively.
I.e. any argument (of any function or an op, e.g. from_sym or from_sym_eq, 
leq_const etc.) could equally be primitive (num, chr, sym) or a compound.
As a consequence, all arguments that were previously of `size_t` - are now 
multi dimensional - i.e. the `multi_arg` struct (which could be just an arg of
size_t or arg + subarg, or a `path` within a compound hierarchy). All ops 
already support (and require) that, and expect multi_arg. There's in an easy
conversion for simple arg cases.

##### How to iterate complex arguments / types
TBD
 
##### Examples

(you can also run most of these tests under `./tests/varbits`. Tests that fail 
, if not on purpose, may require additional flags, noted in the tests)

```
C1(a((b c d) (e f g))  1).
D1(?x) :- C1(?x ?y).
D2(?x ?x1 ?n) :- C1(a((?x ?y ?z) (?x1 ?y1 ?z1)) ?n).
```

```
A(b(c 1) b(c 1)).
A(b(c 1) a(a 2)).
A(a(c1 1) a(c1 1)).
A(a(c1 1) b(c 3)).
A(f(g 2) f(g 1)).
B(?x) :- A(?x ?x).
```

```
A(b(c 1) 1).
A(b(c 1) 2).
A(a(c1 1) 1).
A(a(c1 1) 3).
A(f(g 2) 1).
B(?y) :- A(b(?x ?y) ?y).
```

```
e(1).
e(2).
A(?x) :- e(?x).
B(?x ?y) :- e(?x), e(?y).
C(A(?x) B(?y ?z)) :- A(?x) , B(?y ?z).
B(3 3).
```

```
# this produces an error (type error) ?x can't possibly be equal to ?x
A(b(c 3) 1).
B(?x) :- A(?x ?x).
```

```
# negation and universe test (produces all other combinations)
A(b(c 1) 2).
A(a(c1 1) 1).
A(f(g 2) 3).
B(?x ?y) :- ~A(?x ?y).
```

```
A( 0 1 B(1 0) C(1 0) ).
B(?x ?y) :- A(?y ?x B(?x ?y) C(?x ?y)).
```

```
# recursively decomposes a 'string' 
# (decompose helps w/ the table signature and types in this complex case)
# we could also load any real string from disk...
# @string str <tml.g>.
# A( @@str ). # only needs some parser support for this
A( a(b(c(d(e(f(g)))))) ).
B(?x ?y) :- A(?x(?y)). 
B(?x ?y) :- B(?p ?comp), decompose(?x ?y ?comp). 

# produces
...
B(a b(c(d(e(f(g)))))).
B(b c(d(e(f(g))))).
B(c d(e(f(g)))).
B(d e(f(g))).
B(e f(g)).
B(f g)).
B(g ()).
```

```
# composes a new compound a(b(c d))
A(b(c d)).
A(a(?x)) :- A(?x).
```
  
# Performance

TBD  

***

<a name="bitness">1</a>. 
**bitness** is to be renamed to **bitwidth**.    


