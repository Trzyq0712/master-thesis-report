#import "../macros.typ": *
#import "../generated/perf-rust-scalars.typ": *
#import "../generated/perf-viper-scalars.typ": *

= Conclusion

This thesis presented VMIR, a mid-level intermediate representation for Viper,
and Helium, a verifier that consumes it. Together they show that a core proof
can be discharged without an SMT solver, and faster than Silicon discharges it.

VMIR reduces the surface a backend has to support. Method contracts,
heap-dependent function preconditions and predicates all become one declaration
form, the resource, so the backend implements one verification path instead of
three. Operations Viper leaves implicit become explicit instructions over heap
locations and resources. A call, a fold and an unfold are ordinary exhales
and inhales rather than rules of their own. What reaches the verifier is a flat,
explicitly typed instruction sequence over a small operator set.

Helium verifies that representation with an e-graph as its only reasoning
engine. A resource is walked once, at its declaration, and each later use
replays the recipes that walk recorded, so the side conditions of a contract or
a predicate body are discharged once however often it is used. Obligations are
attempted by a ladder of tiers, cheapest first, and the cheap tiers answer from
facts the e-graph already holds. Helium performs no case analysis and calls no
solver, which is why it targets programs whose obligations are structured rather
than arbitrary.

The concept is proven with measurements. Helium is #viper-ratio-total faster than Silicon
on the hand-written Viper corpus and #rust-ratio-geo faster on the
Prusti-generated one. Straight-line code gains most, reaching up to #rust-best-ratio,
where facts accumulate without any branch to reconcile.
Heap-heavy branching code gains least and approaches Silicon's times, since the
unified state has to reconcile conditional permission amounts at every join.

VMIR and Helium verify the idea of a lightweight verification backend that
can verify simple and structured obligations much faster than a full SMT-based
backend. It serves as a proof of concept verifier that can be expanded on in
the future to support more complex obligations.

== Future Work <sec:future-work>
This section collects the directions we think worth pursuing, ordered by how
much we expect each to matter.

#para[Missing Viper constructs] @sec:results-qualitative lists the Viper constructs Helium does not support.
Built-in containers, existential quantifiers and termination measures are each a
self-contained addition.

Magic wands and quantified permissions are the two that matter most. Both refer
to heap locations, so adding either means deciding first how it fits VMIR's
location and resource model.

#para[Location types] A location type records the stored value type, the group and the maximum
permission bound, as in #vm[`&[f] Int @ 1/1`]. It cannot relate the permission
held at a location to anything else about the state.
@sec:results-qualitative gives the consequence: nothing in VMIR says that
positive permission to a field implies a receiver that is not null.

Making a location a top-level declaration would let it carry that relation
itself. The sketch below gives a field its inverse function and one invariant
over the two.

#no-numbers[```vmir
function f#loc(e0: Ref): f     // Ref to location mapping
  ensures f#inv(result) == e0

function f#inv(e0: f): Ref     // location to Ref inverse mapping
  ensures f#loc(result) == e0

location f: Int @ 1/1
  perm >r 0/1 ==> f#inv(this) != null
```]

#vm[`f`] becomes a declaration of its own. It still names the stored type
#vm[`Int`] and the bound #vm[`1/1`], and it now also carries invariants that
hold wherever the location is in the heap. An invariant may use two keywords,
#vm[`this`] for the location and #vm[`perm`] for the amount held at it. The one
in the sketch reads that positive permission implies a receiver, recovered
through #vm[`f#inv`], that is not null. Silicon hardcodes that assumption, where
a location declaration would state it and leave the engine with one fewer
built-in rule.

#para[Branch isolation] Helium holds one e-graph for a whole verification unit, shared by every branch,
and branch pollution follows from that. Facts accumulate in the one graph,
so a branch verified later can observe a fact learned in a mutually exclusive
branch verified earlier. The facts stay guarded by their path conditions, so soundness holds, but the
order in which branches happen to be traversed can change the outcome.

To resolve this, we propose branching and joining the e-graph
state. Under this model, when the execution branches at a conditional, each arm
receives an isolated copy of the e-graph. The copy would stay assumption-free:
the path condition is never assumed globally, and a fact derived in a branch
stays guarded by it.

At a join the copies are merged, which is the union of the two graphs. Keeping
e-class identifiers stable across copies is the hard part. Execution then
resumes on the merged graph, holding the guarded facts of every predecessor, and
the result no longer depends on traversal order.

#para[Branching execution model] Branching the execution at a conditional would
remove branch pollution outright, and would put Helium on the same footing as
Silicon. Each branch would work in a state of its own, and that state would be
the smaller for it, since a branch encodes only the blocks it traverses and may
assume its path condition outright, which collapses the heap representation and
the e-graph together.

The approach reintroduces Silicon's costs, among them the exponential path count
on independently branching code. It is still worth exploring, because holding one
e-graph across a whole verification unit is itself difficult, and the cheap
e-graph underneath would keep its advantage on each individual path.

#para[Contextual resources] A resource is a global declaration. A loop invariant is a resource in every
respect except that it holds only inside its enclosing method, so Helium inlines
it at each of the three sites instead, and its side conditions are discharged
again at each of them.

Contextual resources would close that gap. An invariant would be walked once,
compiled to a recipe, and replayed at the pre-header, the body inhale and every
back edge.

#para[An SMT fallback] A fixed rule set bounds what Helium can prove. Rather than widen it until the
e-graph carries arbitrary obligations, an SMT solver could sit behind it. The
e-graph would answer the structural obligations, which are the bulk of them, and
the solver would take only what the e-graph fails on. Keeping the solver's state
in step with the e-graph would make those queries cheap when they come.

#para[VMIR preoptimizations] VMIR is a lower-level representation in SSA form,
which makes it a natural place to optimise a program before the verifier sees
it. A Viper program emitted by a frontend carries redundant and dead code,
because the encoding is generated mechanically rather than written by hand.
Dead code elimination and common subexpression elimination are cheap on an SSA
representation, and every instruction they remove is one the verifier never has
to reason about.

#para[Rewrite rules and scheduling] Helium applies the same rule set to every obligation, whatever the goal.
Refining the rules and selecting only those a goal can use should recover the
time spent on matches that cannot contribute.
The rules also run round-robin until a fixpoint. Running the rules that pay off
first would cut matching work across the whole saturation.

#para[Boolean permissions for functions] For heap-dependent functions, the default semantics in Viper rely solely on
wildcard and none permissions. We propose simplifying this reasoning further by
introducing a boolean permission model specifically for verifying
heap-dependent functions. Under this model, permissions would be strictly
binary, representing either the presence or absence of access.

Unfolding would become simpler under it. Instead of removing a wildcard amount,
the verifier would add the unfolded predicate body to the state. The gain is a
smaller reasoning burden inside functions, and a modest one.
