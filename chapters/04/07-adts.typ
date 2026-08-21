#import "../../macros.typ": *

== ADTs <sec:impl-adts>

An #vi[`adt`] is a datatype with constructors that a verifier is expected to
know something about, and Prusti uses it heavily and for one purpose: one per
struct or enum. The guiding example declares two — a struct's and an enum's —
in @lst:example-viper.

An #vi[`adt`] does not introduce anything into the IR. Its constructors, its
field projections and its discriminator are all ordinary function applications,
and what makes them mean something is a side table the verifier keeps: which
function is a constructor of which datatype, at which variant index, and which
function projects which field of it. Nothing in the instruction language grew a
case for datatypes, and no match site in the verifier had to learn about them; a
constructor application is executed exactly as any other application is.

What the side table buys is a family of rewrite rules — the reductions the
ladder of @sec:impl-proving runs underneath every tier — created once per
datatype as it is first encountered, and it is why ADTs are introduced here,
immediately before Predicates: a snapshot is an #vi[`adt`] value, and a fold and
its unfold cancel by a reduction stated in this section rather than by anything
the heap does.

#para[Constructors and projections] The first rule is the projection reduction:
a projection applied to a matching constructor gives the field back,

$ "proj"_i (C(a_0, ..., a_n)) => a_i $

which is what makes the fold–unfold round trip of @sec:impl-predicates exact, and
what makes a snapshot readable without an axiom relating the two. In the guiding
example that rule is what reads a field back: #vi[`snap_Account`] builds
#vi[`Account_cons(b0, b1)`], and a later
#vi[`.. .Account_1`] over the same value is the projection at index one, which
reduces to #vi[`b1`] rather than needing anything proved about the constructor.

The rule also commutes into a conditional. Where the argument's class does not
hold the constructor directly but a ternary over two constructions, the
projection is pushed inside and applied to each arm. This is not a convenience:
an enum discriminator's body is a tower of ternaries over boxed values — one
level of it in #vi[`Transaction_discr`], more as a Rust enum widens — and a
program comparing the _unboxed_ value never sees a constructor under the
projection unless the rule descends. Because the argument is typically a shared
graph rather than a tree, the descent memoises per class; without that, a graph
with $d$ shared classes is walked along up to $2^d$ paths.

#para[Discriminators] Viper's #vi[`x.isC`] tests which variant a value is, and it
is the enum snapshots of @lst:example-viper that a Prusti encoding asks it of —
#vi[`Transaction_discr`]'s body is #vi[`self.isTransaction_1_cons`] under a
ternary, and #vi[`AccountList_discr`]'s is the same shape. The obvious encoding gives each
variant its own predicate function and each pair of variants a rule relating them,
which is quadratic in the number of variants, and Prusti's enums are wide.

Instead each datatype gets _one_ discriminator function into the integers, and
#vi[`x.isC`] is lowered to an ordinary equality against the variant's index:

$ "tag"(C_i (...)) => i $

One rule per constructor, not per pair, and the comparison that remains is a
plain equality between integers. Where the scrutinee is a known constructor the
rule fires, the equality's two sides fold to literals, and constant folding
decides it — so a discriminator test on a known value is answered by the analysis
that is running anyway rather than by any datatype reasoning.

Constructor distinctness then comes for free. If a program ever forces two
distinct constructors of one datatype into the same class, congruence merges their
discriminators, and two different integer literals collide in one e-class. That is
a constant-folding contradiction, which records the state as inconsistent —
and an inconsistent state discharges every obligation asked of it, which is
exactly the treatment an unreachable path should get. No disequality edge, no
axiom, and no case split.

Injectivity is stated rather than derived, and it is stated because congruence
runs only forwards. Congruence gives that equal arguments make equal
applications; the converse — two applications of one constructor in a single
e-class force their arguments together, pairwise — is a rule of its own, and it is
sound precisely because constructors are free. This is information that is
otherwise unreachable: the projection rule recovers the same equalities, but only
where an application of the projection already exists, and two constructor terms
can meet with no projection over them anywhere. The contrast with a location
function is worth stating: those get no such rule, because nothing says a
field's location function is injective, and @sec:impl-heap derives what a program
needs about distinct locations from permission arithmetic instead.

#para[Refuting an equality] <para:impl-refuting> Everything above runs _forwards_,
from a known constructor or a known discriminator value to its consequences. The
inverse direction — refuting an equality, so that a variant can be ruled _out_ —
needs something more, because an e-graph stores equalities and has no place to put
a disequality. What it does have is enough structure to _derive_ one, and two rules
do exactly that.

Both rest on the same notion. A class carries a _fingerprint_ when its value is
pinned: either a folded literal, or the identity of a constructor it was built by.
Two fingerprints separate when they cannot denote the same value — two different
literals, or two distinct constructors of one datatype at one instantiation, which
is free-constructor distinctness and the same premise that folds a
constructor-to-constructor comparison to #vm[`false`]. The comparison is
conservative in every direction it is unsure about: the same constructor at
different arguments never separates, since the fingerprint is the constructor's
identity and not the whole term, and a literal against a constructor never does.

The first rule uses that to _pin a condition from its arms_. Where a ternary's own
class has a fingerprint and one arm's fingerprint separates from it, that arm
cannot be the one taken, so the condition is pinned the other way — with no
knowledge of the condition itself. This is what inverts a Prusti snapshot tower.
After a #vi[`&mut`] round trip the recovered link is an equality between the old
snapshot and the new, and the snapshot function's body is a nested ternary over
constructor arms: each non-matching arm pins its guard false, ternary reduction
exposes the next level, and the ground constructor at the bottom pins the matching
guard true — recovering the discriminant equality that gates the variant's
footprint (#pararef(<para:impl-gate-split>, [Conditional footprints])).

The second walks from applications back to arguments. Congruence gives that
$a = b$ implies $f(a) = f(b)$; contrapositively, if some unary $f$ has $f(a)$ and
$f(b)$ in classes whose fingerprints separate, then $a = b$ is #vm[`false`]. This
is the contrapositive of congruence and not of injectivity, so it is sound for any
$f$ — which is what makes it reach the case the rule exists for. Prusti encodes a
primitive snapshot not as an #vi[`adt`] but as a domain with a
constructor--retraction pair, so its constructions carry no free-constructor
distinctness of their own; the retraction axiom nonetheless puts the two
underlying literals in the graph, and those separate the constructions. The rule
mirrors the contrapositive that walks the other way, from an already-refuted
application equality to a disequality between arguments, and together they close
the loop between arguments and applications.

One cost is worth recording, because it was the dominant one. The rule's _failing_
scan is the hot path: it finds nothing and, without a memo, repeats in full on
every saturation iteration for every undecided equality — 65% of a payload-enum
file's wall clock. It is memoized on the pair together with the number of parents
each side has, which is a free monotone version stamp, since parent lists only
grow: a pair is re-scanned exactly when a side has gained a parent, which is when a
new observation can have appeared. That trades completeness and not soundness — a
fingerprint can sharpen without either side gaining a parent — and a missed
refutation only fails to prove something.

#para[What we still do not decide] Two gaps survive, and both are about the
discriminator rather than about constructors.

The first is exhaustiveness: from "not this variant and not that one" to "then it
is the remaining one". The discriminator is an ordinary integer-valued function and
nothing constrains its range, so a scrutinee ruled out of every variant but one is
not thereby known to be that one.

The second is inversion _through the tag_, as opposed to through a term: nothing
states that a discriminator value determines the constructor, and in general it
does not, since two applications of one constructor with different arguments share
a tag. For a nullary variant it does, and that is the case Prusti's enums are full
of. Where the tower's structure is available the pinning rule above recovers the
same conclusion; where only the tag is, it does not.

Two directions would close them. The cheaper is to state what is missing as
ordinary axioms at the declaration: that the discriminator ranges over the
declared variants, and that its value determines the constructor for each nullary
variant. Neither needs new machinery — they are facts of the kind the axiom
mechanism already handles — and a finite tag range is what would let a snapshot
tower's arms be mutually exclusive by construction, rather than by the
telescoping split whose cost @sec:results-enum-scaling measures. The more invasive
is to give the e-graph native disequality edges, so that distinctness is stored and
detected at a merge rather than reconstructed. That is a change to the engine
rather than to the encoding, and it is the one that would also make a program's own
#vi[`assume a != b`] first-class under a path condition.

#para[What we record] A discriminator test that cannot be decided is left as an
equality between an application and a literal, in the state, with both sides
intact. Nothing is approximated: the term the verifier could not fold is the term
the program wrote, and a procedure with a theory of datatypes would find it
exactly where it was left.
