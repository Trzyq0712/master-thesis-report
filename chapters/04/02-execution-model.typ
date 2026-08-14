#import "../../macros.typ": *

== Execution Model <sec:impl-execution>

The execution model of the new verifier is strongly based off of the symbolic
execution model of Silicon. The main difference is that in this new verifier, it
is us who is responsible for managing the symbolic state, rather than Z3. On one
hand this means that there is a lot more bookkeeping we have to do, but on the
other hand, it means we have a lot more control over the symbolic state, giving us
the opportunity to optimize the process for the common case.

#viper[```viper
var x: Bool
var y: Bool := x ? false : true
assert y == !x
```]

While this example is actually a case where we need to do functional reasoning,
we can still use it to illustrate the execution model. In this case, we can
actually coincidentally discharge this due to structure, but this will not hold
in general. Let us now look how this method will look when translated down to VMIR.

#vmir[```vmir
e0: Bool := fresh             // x == e0
e1: Bool := e0 ? false : true // y == e1
e2: Bool := e0 ? false : true // !x is desugared to a ternary
e3: Bool := e1 == e2          // y == !x
assert e3
```]

The verifier will execute this method line by line, and at each step update the symbolic state.
When it eventually reaches the assertion, it will check if the obligation is satisfied.
More concretely, it will verify that the value #vm[e3] is in the same e-class as #vm[true].

#para[Symbolic state] There is no separate store of what the verifier knows. The
e-graph _is_ the symbolic state, and a VMIR temporary is nothing more than a
handle into it: executing an instruction adds the term it names and returns the
e-class that term landed in. A method body is walked once, in order, and the state
after $n$ instructions is the graph after $n$ additions.

This is what makes the last line of the listing above a lookup rather than a
query. #vm[`e1`] and #vm[`e2`] name the same term, so hash-consing puts them in one
e-class as the second is added; #vm[`e3`] is then #vm[`e1 == e1`], which
reflexivity folds to #vm[`true`], and the assertion is discharged by comparing two
class identifiers. Nothing was proven, in the sense of a search — the structure
was already there and the representation made it visible.

Equalities enter the same way. A fact the program assumes is merged into the
graph, and congruence closure propagates it: merging two argument classes merges
every application over them, without any of those applications being revisited.
This is the operation the design bets on, and the reason the state is an e-graph
rather than a substitution or a formula set. The bet is that Prusti's obligations
are mostly equalities between terms the program already built, and
@sec:prusti-needs is the evidence for it.

#para[Path conditions] Not every fact is unconditional. An instruction inside a
branch arm carries a _path condition_: a conjunctive cube of literals over values
already in the graph, each a boolean temporary with a polarity. The cube is
attached to the instruction at lowering time and is exact — @sec:impl-cfg
describes the algebra that builds it — so at execution the verifier never has to
reconstruct where in the control-flow graph it is.

What a cube is _for_ differs by direction. A fact assumed under a cube must not
escape to a sibling path, so it enters the graph guarded: what is merged with
#vm[`true`] is the implication $"pc" => "fact"$, not the fact. An obligation raised
under a cube need only hold on that path, so what has to be proven is likewise
$"pc" => "goal"$. Both are the same shape, which is why one operation covers them.

Silicon takes the other route and forks: a branch produces two symbolic states,
each with its own decider and its own path conditions, and a fact assumed in one
is simply absent from the other. Keeping one graph with guarded facts instead is a
trade. What it buys is that a term built before the branch is shared by both arms
rather than duplicated, that no state has to be copied at a fork, and that a join
is a merge of two heaps rather than a pair of independent continuations. What it
costs is that facts are no longer unconditional, so the guards have to be carried
and discharged, and reasoning under a cube needs an explicit mechanism rather than
being free. That mechanism is next.

#para[Discharging an obligation] <para:impl-tiers> An obligation is a goal e-class
and a path condition, and the verifier answers it by escalating through tiers,
cheapest first. Each tier is a strictly larger amount of work than the last, and
the great majority of obligations never leave the first two.

The first tier asks whether the implication is _already_ #vm[`true`] — either
trivially, or because an identical obligation was proven earlier and the result
recorded. This costs one comparison of class identifiers. Discharging an
obligation by merging it with #vm[`true`] is what makes the record; the second
occurrence of an obligation is therefore free, which matters because a Prusti
encoding raises the same framing obligation at every one of a long run of
statements.

Failing that, the graph is _saturated_: the rewrite rules are run to a fixpoint
and the implication re-checked. Saturation runs on the live graph and adds no
assumption, so it proves whatever holds unconditionally — which is most of what
a heap operation asks for.

Only if that fails does the path condition get assumed, and assuming it is what
costs. The cube cannot be merged into the live graph, since it holds on this path
only; so a copy of the graph is taken, the literals are fixed in the copy, and the
copy is saturated. Inside a method body the copy is amortised — one _scratch_ graph
per block, built on the block's first hard obligation and reused by the rest of
it, since every instruction of a block shares the block's cube (@sec:impl-cfg).
Outside one — in a function or a resource body, which have no branch structure to
share — each such obligation clones.

Two further tiers exist and are deliberately narrow. The first decomposes a goal
that is itself a guarded implication, assuming the one condition that the goal's
own shape names and re-checking the surviving arm; it does not fork, and it
telescopes a chain of nested guards one assumption at a time. The last is a
genuine case split, and it is the only place the verifier reasons by cases at all.
Its candidate conditions are read off the goal term rather than searched for,
because the obligations that need it come from _branching pure functions_ — a
function whose two arms establish its postcondition differently — and a function
goal nests only a handful of conditions. Method control flow does not reach here:
a join is discharged structurally by the block walk, which is the subject of
@sec:impl-cfg and the reason the split stays rare.

#para[The reasoning core] Underneath every tier is one rule set, always on.
Congruence and hash-consing come from the e-graph itself. Constant folding is an
analysis attached to each e-class: a class whose term folds to a literal carries
that literal, and a class forced to carry two different literals is a
contradiction — which is how an inconsistent state is detected, and why an
unreachable path discharges anything asked of it.

On top of those sit the rewrites. The arithmetic ones are identities rather than
a theory: adding zero, multiplying by one, and the two cancellation shapes
$(x - p) + p$ and $x - x$, which are exactly what a permission consumed and given
back leaves behind. The boolean ones normalise ternaries, since VMIR has no
negation or conjunction of its own and spells both as #vm[`?:`] — an assumed branch
literal reduces a gated permission #vm[`b ? p : 0`] to #vm[`p`] by the same rule
that simplifies any other conditional. And a proven equality is turned back into a
merge: an #vm[`==`] node whose class is known #vm[`true`] unions its two arguments,
which is what lets an assumed equality participate in congruence rather than
sitting inertly as a fact.

What is absent is as deliberate. There is no decision procedure for linear
arithmetic, so an obligation like $i < n |- i + 1 <= n$ is not discharged, and
@sec:beyond-fragment says where that bites. There is no disequality store either:
an e-graph records that two terms are equal and has no way to record that they are
not, so distinctness is derived where it can be derived — from a constant-folding
collision, or from the contrapositive of congruence — and is otherwise deferred
(@sec:impl-adts).

#para[Joins] The one thing this section has passed over is what happens when two
paths meet. A branch produces two heaps as well as two bindings for every variable
the arms disagree about, and reconciling them is where both the path-condition
machinery and the symbolic heap are put under real pressure. That is
@sec:impl-cfg, and it deliberately comes after the heap has been introduced: the
heap of @sec:impl-heap is presented straight-line first, precisely so that a join
can be shown as the thing that forces every piece of conditional structure it
carries.
