#import "../../macros.typ": *

== Qualitative Evaluation <sec:results-qualitative>
This section answers two questions that the timings of
@sec:results-quantitative presuppose, and that no measurement settles. The first
asks what the intermediate representation contributes, meaning how VMIR simplifies
Viper's surface constructs and how that makes a backend's implementation easier.
The second concerns the limitations of the proposed system in two distinct
senses: which Viper constructs the new representation leaves unsupported, and
which programs the backend fails to verify.

#para[Impact of VMIR] Every departure VMIR makes from Viper reduces the surface
that a backend must support. First, VMIR drops redundant operators.
For example it retains the ternary operator as the sole boolean connective,
so #vi[`a && b`] lowers to #vm[`a ? b : false`] and
#vi[`a || b`] to #vm[`a ? true : b`]. The lowering also makes explicit what in
surface
Viper is left implicit, such as the #vi[`write`] amount that an #vi[`acc(x.f)`]
carries.

Second, VMIR represents every heap object as a location. A field declaration
becomes a function from a receiver to a location, and a predicate instance
becomes a location holding the snapshot of its footprint. Viper instead
distinguishes a field from an instance of a predicate, so a verifier for Viper
carries a representation and a set of rules for each. Under the single form the
heap is an ordinary operand, named by the instructions that consume and produce
it, so #vi[`x.f`] and #vi[`old(x.f)`] are the same dereference operation at two
different heaps.

Third, VMIR represents predicates, method contracts and function preconditions
alike as resources, a heap delta paired with an assertion about that delta, so
the backend implements one verification path for all three. Having these as separate declarations allows
for improved proof reuse compared to Viper.

Fourth, the lowering decomposes the constructs that would otherwise each need
a rule of their own in the backend. A recursive function is replaced by a
bodyless twin carrying the same postcondition, with the recursive call retargeted
to the twin and one axiom relating the two. A loop is cut at
its back edges into ordinary basic blocks, with its invariant exhaled before the
header and inhaled at it. A fold becomes an exhale of the predicate body
followed by an addition of the folded chunk, and a call becomes an exhale of the
precondition resource followed by an inhale of the postcondition.

#para[Unsupported constructs] VMIR and Helium cover less of Viper than the mature
backends Silicon and Carbon do. VMIR does not currently support the built-in
collection types #vi[`Seq[T]`], #vi[`Set[T]`],
#vi[`Multiset[T]`] and #vi[`Map[K, V]`], with their operations and constructors.
In addition, VMIR and Helium do not allow existential quantifiers.

On top of that, quantified permissions are out of scope. An encoding must state
permission to an unbounded set of locations with a recursive predicate instead.
That predicate fixes a traversal order on every proof about the structure, which
suits a list or a tree better than an array or a graph.

The missing support for magic wands has the widest consequences of the four.
Prusti emits a wand for
every borrow that outlives the statement or the call creating it, so a Rust
program reaches the construct without carrying a single functional specification.

One construct is accepted with its semantics omitted. The lowering parses a
termination measure and then drops the #vi[`decreases`] clause, assuming instead
that every function terminates. No termination check runs anywhere in the
pipeline. Helium therefore verifies
#vi[`function bad(n: Int): Int decreases n { bad(n) + 1 }`], which Silicon
rejects.

One restriction is deliberate rather than an omission. A VMIR resource is
verified once at its declaration, which requires the dependency graph over
resources to be acyclic. The lowering therefore rejects a predicate whose body opens an
instance of itself with #vi[`unfolding`]. The restriction leaves ordinary
recursive predicates untouched, since a body that mentions an instance of a
predicate is only a dependency on the snapshot type.


#para[Verification incompleteness] Helium is aimed at the verification conditions
a compiler-generated encoding produces rather than at general-purpose
verification. Those conditions concern framing: that permission to a location is
held wherever the program reads or writes it, that the permissions a predicate's
body names are held wherever the program folds it, and that an instance is held
wherever the program unfolds one. Helium carries a decision procedure for neither
boolean, integer nor rational algebra, so an obligation whose remaining content is
algebraic rather than structural is not discharged.

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

Exhaustiveness over the discriminants of an algebraic datatype is unsupported, for
the reason given in @sec:impl-data: Helium reduces a discriminator against a visible
constructor and states no counterpart of exclusivity, so
#vi[`s.isCircle || s.isSquare`] fails for an opaque #vi[`s`].

The last gap is the relation between a field and its receiver. Silicon enforces
the guarantee that positive permission to a field implies a non-#vi[`null`]
receiver, and the uniform representation of every heap entity as one abstract
location discards it. A field and a single-argument predicate share one mathematical
representation, so VMIR has no per-kind mechanism to state the guarantee. Helium
consequently fails on it in either direction. It does not derive
#vi[`x != null`] from #vi[`acc(x.f)`], and it grants positive permission to a
field of a receiver already known to be #vi[`null`], where the two facts should
contradict each other and collapse the state. @sec:future-work develops the design
that would close the gap, in which a field's location carries the guarantee as an
axiom of its own rather than the engine enforcing it as a built-in rule.
