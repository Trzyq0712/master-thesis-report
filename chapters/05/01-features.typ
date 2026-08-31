#import "../../macros.typ": *
#import "../../generated/features-counts.typ": *

== Feature Completeness <sec:results-features>
As an early, experimental verifier, Helium's feature set is naturally incomplete when compared to mature Viper verifiers such as Silicon and Carbon. This section examines these limitations from two perspectives. First, we outline the core Viper constructs that VMIR and Helium do not yet support. Second, we analyze instances of verification incompleteness, specifically cases where Helium fails to verify programs built entirely from the subset of constructs it does support.

=== Unsupported Viper constructs <sec:results-unsupported>
Several Viper constructs are currently unsupported by Helium. The first major
omission is the set of built-in collection types, which includes #vi[`Seq[T]`],
#vi[`Set[T]`], #vi[`Multiset[T]`], and #vi[`Map[K, V]`], along with their
associated operations and constructors. We chose to defer their implementation
to prioritize the core language constructs more frequently relied upon by
current frontends.

In the domain of quantifiers, Helium lacks support for the existential quantifier
#vi[`exists`]. We decided against implementing it for now because it is used very
rarely in practice. The absence of quantified permissions, however, is a more
consequential limitation. In Viper, quantified permissions provide a powerful
mechanism for reasoning about an unbounded number of memory locations, such as
all elements within an array or all nodes in a disjoint data structure, without
imposing a rigid traversal order. Without them, users must rely on recursive
predicates to model unbounded permissions. While predicates are sufficient for
many data structures (like linked lists or trees), they are less ergonomic for
structures that require random access, making the verification of certain
array-heavy or graph-like patterns more cumbersome in Helium.

Perhaps the most significant gap is the absence of magic wands. This omission is
particularly relevant because Prusti relies on wands even for programs without
functional specifications: wands are Prusti's general mechanism for borrows that
outlive a statement or a call. They are generated from the borrow checker's
unblock graph whenever a borrowed place is unblocked, together with any pledge
attached to it. For instance, when a returned mutable reference dies, the
associated wand is packaged and exhaled to hand back full permission to the
underlying object, thus modeling Rust's borrow semantics.

Another divergence from existing verifiers involves termination measures. Helium
does not reject them during parsing; it successfully parses termination
specifications but subsequently ignores #vi[`decreases`] clauses during analysis.
Operating under the assumption that all functions terminate, Helium omits
termination checking entirely. Consequently, a function with a non-decreasing
measure, such as #vi[`function bad(n: Int): Int decreases n { bad(n) + 1 }`],
is accepted. In contrast, Silicon correctly rejects the same function, warning
that the #emph[termination measure might not decrease].

Finally, our design takes a stricter stance on recursive predicate definitions. Helium
requires the dependency graph over predicates to be acyclic,
and it rejects files containing recursive or mutually recursive
predicate definitions outright. Although Viper admits these cycles, allowing a
predicate to unfold itself within its own body, we consider them to be a very
rare occurrence and a construct of limited practical utility. Consequently, while
Silicon verifies our test cases for this behavior, Helium rejects the entire file.

=== Verification incompletenesses <sec:results-incomplete>
At this stage, Helium is not aimed at being a general-purpose verifier like
Silicon and Carbon. Instead, its rewrite engine is optimized for the fast,
structured discharge of verification conditions typically produced by
compiler-generated encodings, such as framing and fold/unfold operations. It
carries no decision procedure for boolean, integer, or rational algebra;
consequently, it naturally fails on obligations where the remaining content
is an algebraic fact rather than a fact about the heap.

*Boolean algebra.* Helium can only discharge boolean obligations that can be
resolved via constant folding or the direct application of its existing rewrite
rules. A prime example of this limitation is De Morgan's laws:  @lst:demorgan fails to verify, even though
both sides are tautologically equal for all #vi[`a`] and #vi[`b`].

#viper(
  caption: [Helium cannot discharge general boolean obligations, such as De Morgan's laws.],
  label: "lst:demorgan",
)[```viper
assert !(a && b) == (!a || !b)
```]


*Integer and real arithmetic.* Support for arithmetic is currently minimal,
limited primarily to identity elements, zero elements, and basic telescoping
addition and subtraction. In general, Helium cannot discharge relational
obligations (such as $<$, $lt.eq$, or $=$) involving uninterpreted variables.

This limitation surfaces when re-establishing loop invariants, such as:
$ i gt.eq 0 arrow.r.double i + 1 gt.eq 0 , $
or when discharging the arithmetic preconditions of a recursive call:
$ n gt.eq 0 and n eq.not 0 arrow.r.double n - 1 gt.eq 0 . $


*Reasoning by cases.* Helium currently lacks a mechanism for case splitting.
While the postcondition in @lst:abs-postcondition holds on each arm of the
conditional separately, the two arms rewrite to different, incomparable terms.
Consequently, discharging the obligation cannot be achieved in a single rewrite
step over the conditional.

#viper(
  caption: [A postcondition true on each arm of a conditional body, closed by
    neither arm's rewrite alone.],
  label: "lst:abs-postcondition",
)[```viper
function abs(i: Int): Int
  ensures result >= 0
{ i < 0 ? -i : i }
```]

Verifying this function requires reasoning by cases on the guard #vi[`i < 0`],
which the current rewrite engine does not support. Even with reasoning by cases,
the above would still require Helium to discharge the arithmetic obligation, and
thus fail.

*Algebraic datatypes.* Exhaustiveness of discriminants is currently unsupported.
While Helium can evaluate discriminants for *concrete* constructor applications
(e.g., #vi[`circle(n).iscircle`] successfully verifies given the datatype in
@lst:incomplete-shape), it cannot discharge a disjunction over all possible
discriminants for an arbitrary value, such as
#vi[`s.iscircle || s.issquare || s.isrect`] for an opaque #vi[`s: Shape`].

#viper(
  caption: [A datatype whose constructors are tagged by declaration order.],
  label: "lst:incomplete-shape",
)[```viper
adt Shape {
  circle(r: Int)
  square(side: Int)
  rect(w: Int, h: Int)
}
```]

What is missing is propagating that fact to values the program only knows
indirectly. @lst:incomplete-shape-branch builds #vi[`s`] from a known
constructor on each side of a conditional, #vi[`circle`] or #vi[`square`], and
still fails to close the disjunction of discriminants once the two branches
have joined.

#viper(
  caption: [A value built from a known constructor on each branch, whose tag
    the join no longer carries.],
  label: "lst:incomplete-shape-branch",
)[```viper
var s: Shape
if (b) { s := circle(n) } else { s := square(m) }
assert s.iscircle || s.issquare
```]

Closing this needs the tag reduction pushed through the join's #vi[`ite`], the
same reasoning by cases the previous gap is missing.

One potential solution is to assign each constructor an integer tag
($"circle" arrow.r.double 0$, $"square" arrow.r.double 1$,
$"rect" arrow.r.double 2$) and restrict the discriminant function's range to
that finite set. However, this encoding alone would not discharge the obligation.
For an opaque #vi[`s`], this reduces exhaustiveness to:
$ "tag"(s) = 0 or "tag"(s) = 1 or "tag"(s) = 2 , $
This is a disjunction of equalities that still requires either bounded-range
arithmetic or a case split to verify—both of which represent existing gaps in
Helium's capabilities. While such an encoding is worth adding to give
discriminants a concrete representation, it does not bypass the need for a more
comprehensive decision procedure.

*The field/receiver relation.* VMIR represents every heap entity—whether a field
or a predicate—uniformly as an abstract *location*. However, this uniformity
discards a structural guarantee that Silicon enforces: possessing positive
permission to a field implies its receiver is non-null. Because VMIR maps both
fields and single-argument predicates to the same mathematical representation,
it lacks a per-kind mechanism to encode this property.

Consequently, Helium fails to reason about non-nullity in both directions. In
the forward direction, holding permission to a field should suffice to prove the
receiver is not null (as shown in @lst:field-nonnull-forward), but Helium fails
to verify this.

#viper(
  caption: [Positive permission to a field, alone, should be enough to know its
    receiver is non-null.],
  label: "lst:field-nonnull-forward",
)[```viper
inhale acc(x.f)
assert x != null
```]

Silicon successfully verifies this because the held permission inherently
guarantees #vi[`x`] is not #vi[`null`]. In the reverse direction, this missing
property leads to an inconsistency: a receiver already known to be #vi[`null`]
can still be granted positive permission to a field, as seen in
@lst:field-nonnull-inconsistent, whereas it should instead trigger a
contradiction and collapse the state.

#viper(
  caption: [A null receiver and a positive permission to one of its fields
    contradict each other.],
  label: "lst:field-nonnull-inconsistent",
)[```viper
assume x == null
inhale acc(x.f)
assert false
```]

Silicon catches this contradiction, while Helium does not. We revisit this
gap in @sec:future-work, where we sketch how a field's location could be
designed to carry this fact as a self-axiom, rather than requiring the
verifier's engine to hardcode the rule.
