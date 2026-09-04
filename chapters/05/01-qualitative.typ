#import "../../macros.typ": *

== Qualitative Evaluation <sec:results-qualitative>
This section evaluates the pipeline without measurement. We first describe what
the intermediate representation contributes, which is the set of obligations
VMIR settles by construction rather than leaving to the backend. We then
delimit the supported fragment, separating a construct VMIR does not represent,
which the lowering rejects, from one it represents but about which Helium
proves nothing. The corpora of @sec:results-quantitative are confined to the
boundary the second establishes.

#para[Impact of VMIR] Each departure from surface Viper removes an obligation
from the backend, and together those removals make
equality reasoning sufficient for the proof obligations a frontend such as Prusti
generates. Four of them carry the design.

First, every expression has exactly one form. VMIR retains a single boolean
connective, the ternary, so #vi[`a && b`] lowers to #vm[`a ? b : false`] and
#vi[`a || b`] to #vm[`a ? true : b`], and it states explicitly what surface Viper
leaves implicit, such as the #vi[`write`] amount an #vi[`acc(x.f)`] carries.
Consequently two occurrences of one expression are structurally identical, and
the e-graph of @sec:impl-execution observes their equality when it constructs
them rather than deriving it afterwards.

Second, one representation covers every heap object. Viper distinguishes a field
of a reference from an instance of a predicate, and a verifier for it carries a
representation and a set of rules for each. VMIR gives both the same form, a
location: a field declaration becomes a function from a receiver to a location,
a predicate instance becomes a location holding the snapshot of its footprint,
and a heap is a set of chunks pairing a location with a permission amount and a
value. The heap is itself an ordinary operand, named by the instructions that
consume and produce it, so #vi[`x.f`] and #vi[`old(x.f)`] are the same
dereference at two different heaps. Helium therefore implements one heap and one
set of heap instructions, whatever surface construct put a chunk there
(@sec:impl-heap).

Third, one declaration form stands behind three Viper constructs. A predicate, a
method contract and a function precondition each pair a heap delta with an
assertion about that delta, so the lowering emits a VMIR resource for all three.
Verification of a resource at its declaration, and its use at a fold, an unfold, a
call and a heap-dependent function application, is implemented once
(@sec:impl-predicates).

Fourth, the lowering decomposes the constructs that would otherwise each need
a rule of their own in the backend. A recursive function is replaced by a
bodyless twin carrying the same postcondition, with the recursive call retargeted
to the twin and one axiom relating the two, so no VMIR function depends on itself
and Helium needs no bound on unfolding (@sec:impl-functions). A loop is cut at
its back edges into ordinary basic blocks, with its invariant exhaled before the
header and inhaled at it, so Helium implements neither a loop nor a rule for an
invariant (@sec:impl-cfg). A fold becomes an exhale of the predicate body
followed by an addition of the folded chunk, and a call becomes an exhale of the
precondition resource followed by an inhale of the postcondition
(@sec:impl-methods). Helium consequently implements a small set of primitives,
each serving several surface constructs, and every high-level construct is
decomposed once, in the lowering, rather than interpreted at each occurrence.

Three costs accompany these decisions, and the remainder of the chapter reports
all three. The lowering absorbs the work the backend no longer performs, so
support for a Viper construct is a problem for the lowering before it is one
for the verifier. Representing every heap entity as one abstract location
discards a guarantee Viper attaches to fields, which is the incompleteness
described at the end of this section. Holding one e-graph for every arm of a
conditional, finally, makes a branch cheap for Helium and a permission moved
across a branch expensive, a trade @sec:results-discussion measures.

#para[Unsupported constructs] VMIR and Helium are early work, and the fragment
they cover is incomplete against mature Viper backends such as Silicon and
Carbon. Four
families of Viper construct have no counterpart in VMIR, so the lowering
rejects an input that uses one.

The first is the built-in collection types, #vi[`Seq[T]`], #vi[`Set[T]`],
#vi[`Multiset[T]`] and #vi[`Map[K, V]`], together with their operations and
constructors. We deferred them in order to prioritise the constructs Prusti's
encoder emits. The second is the existential quantifier #vi[`exists`], which we
deferred because neither corpus of @sec:results-quantitative contains one.

The third is quantified permissions, described in @sec:bg-viper. Without them an
encoding states permission to an unbounded set of locations with a recursive
predicate instead, which fixes a traversal order on every proof about the
structure and consequently suits a list or a tree better than an array or a
graph.

The fourth is magic wands, and its consequences are the widest of the four.
Prusti emits a wand for every borrow that outlives the statement or the call
creating it, so a Rust program reaches the construct without carrying a single
functional specification, as @sec:bg-prusti describes. The lowering therefore
rejects Prusti's encoding of any program whose borrows are not confined to the
statements that create them.

One construct is accepted with its meaning changed. The lowering parses a
termination measure and drops the #vi[`decreases`] clause, on the assumption that
every function terminates, so no termination check runs anywhere in the pipeline:
#vi[`function bad(n: Int): Int decreases n { bad(n) + 1 }`] is verified, where
Silicon rejects it and reports that the measure might not decrease.

One restriction is deliberate rather than an omission. A VMIR resource is
verified once at its declaration, which requires the dependency graph over
resources to be acyclic, so the lowering rejects an input holding a recursive
or mutually recursive predicate. Viper admits such a cycle, and our two test
cases for it are a predicate whose body opens an instance of itself with
#vi[`unfolding`], and a predicate whose body calls a function whose own
precondition is that same predicate. Silicon verifies both.

#para[Verification incompleteness] Helium is aimed at the verification conditions
a compiler-generated encoding produces rather than at general-purpose
verification: that permission to a location is held wherever the program reads or
writes it, that the permissions a predicate's body names are held wherever the
program folds it, and that an instance is held wherever the program unfolds one.
Helium carries a decision procedure for none of boolean, integer or rational
algebra, so it fails on an obligation whose remaining content is an algebraic
fact rather than a fact about the heap. Five such gaps are worth naming.

Helium discharges exactly those boolean obligations that constant folding or one
of its rewrite rules resolves. De Morgan's laws are the smallest example:
#vi[`assert !(a && b) == (!a || !b)`] fails, although the two sides are
tautologically equal for every #vi[`a`] and #vi[`b`].

Arithmetic support is limited to identity elements, zero elements, and
telescoping addition and subtraction. Helium discharges no relational obligation
over uninterpreted variables, which surfaces when a loop invariant is
re-established,
$ i gt.eq 0 arrow.r.double i + 1 gt.eq 0 , $
and when the arithmetic precondition of a recursive call is discharged,
$ n gt.eq 0 and n eq.not 0 arrow.r.double n - 1 gt.eq 0 . $

Helium performs no case analysis on a guard. Consider the function

#no-numbers[```viper
function abs(i: Int): Int
  ensures result >= 0
{ i < 0 ? -i : i }
```]

whose postcondition holds on each arm of the conditional separately. The two arms
rewrite to different, incomparable terms, so no single rewrite step over the
conditional discharges the obligation. Verifying the function requires a case
analysis on #vi[`i < 0`], and, given one, the arithmetic obligation that remains
on each arm.

Exhaustiveness over the discriminants of an algebraic datatype is unsupported.
Helium reduces a discriminator applied to a visible constructor, so
#vi[`circle(n).iscircle`] is discharged, and it does not close a disjunction over
every discriminant of a value no constructor visibly built, such as
#vi[`s.iscircle || s.issquare`] for an opaque #vi[`s`]. A value built from a
known constructor on each arm of a conditional falls under the same gap, since
the join carries a ternary rather than a tag and closing the disjunction needs
the reduction pushed through it, which is the case analysis above. Tagging the
constructors with integers would give the discriminants a concrete
representation without closing the gap, because exhaustiveness then becomes a
disjunction of equalities over a bounded range, which needs either range
arithmetic or the same case analysis.

The last gap is the relation between a field and its receiver. VMIR represents
every heap entity, a field and a predicate alike, as one abstract location, and
that uniformity discards a structural guarantee Silicon enforces: positive
permission to a field implies that its receiver is not #vi[`null`]. Because a
field and a single-argument predicate share one mathematical representation, VMIR
has no per-kind mechanism to state the guarantee, and Helium consequently fails
to reason about non-nullity in either direction. It does not derive
#vi[`x != null`] from #vi[`acc(x.f)`], and it grants positive permission to a
field of a receiver already known to be #vi[`null`] where the two facts should
contradict each other and collapse the state. @sec:future-work develops the design that would close the gap, in which a field's
location carries the fact as an axiom of its own rather than the engine
hardcoding the rule.
