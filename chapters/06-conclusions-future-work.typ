#import "../macros.typ": *

= Conclusion

In this thesis, we presented a novel approach to verifying Viper programs by introducing the Viper Mid-level Intermediate Representation (VMIR) and an associated verifier, Helium. Our work successfully demonstrates that the complex, feature-rich Viper language can be significantly simplified and verified with much higher performance than the state-of-the-art Silicon verifier.

The introduction of VMIR plays a crucial role in simplifying Viper's semantics. By reducing method contracts, heap-dependent function preconditions, and predicates to a unified concept of a VMIR resource, we drastically decrease the conceptual surface area of the language. Complex, implicit operations in Viper, such as calling methods or folding and unfolding predicates, are elegantly expressed as simple, explicit operations on heap locations and VMIR resources. This transformation flattens the input into a straightforward, explicitly typed format, removing ambiguities and allowing the verifier to operate on a minimal instruction set without losing expressiveness.

Building on the simplicity of VMIR, Helium introduces an optimized verification architecture. By managing resources explicitly, Helium ensures that permissions and resources only need to be verified once. Furthermore, Helium employs an e-graph data structure for cheap proof discharging. By leveraging e-graph saturation to accumulate facts and permissions, the verifier handles the majority of proof obligations through highly efficient rewrite rules. Because Helium lacks extended reasoning capabilities, it is specifically designed to deal with spec-less programs, focusing on being exceptionally fast at discharging programs with highly structured obligations.

Our evaluation confirms that this architecture yields significant performance improvements. On hand-written Viper benchmarks, Helium achieves a 25#sym.times speedup over Silicon. Across the Prusti-generated corpus, Helium demonstrates an 18#sym.times average speedup. The performance gains are especially spectacular on straight-line code, where Helium reaches speedups exceeding 100#sym.times due to its ability to accumulate facts linearly without branching overhead. However, on heap-heavy, highly branched code, the advantage deteriorates, yielding performance similar to Silicon, primarily due to the computational cost of reconciling conditional permission chunks at control-flow merge points.

In summary, this work demonstrates that reducing permission-based verification to explicit resource management and e-graph saturation is a viable and highly performant architecture for structured, spec-less programs.

== Future Work <sec:future-work>
In this section we discuss relevant directions for future work, for further improving
Helium and VMIR. The list is ordered by our percpetion of the relevance of each item.

=== Adding Support for Missing Viper Constructs
As detailed in @sec:results-unsupported, several Viper constructs are currently
unsupported by Helium. Adding support for these missing features, such as
built-in containers, existential quantifiers, and termination measures, remains
an important goal for future work.

Magic wands and quantified permissions are also missing, but stand out as being
particularly significant. Considering them will require a careful evaluation of how they can be
integrated with VMIR's shared heap location abstraction, as both constructs
inherently entail them.

=== Extending Location Types
The current design of VMIR location types is insufficiently expressive for certain heap properties. While a location type encodes the stored value type, the location group, and the maximum permission bound (e.g., #vm[`&[f] Int @ 1/1`]), it lacks the structural capacity to express invariants regarding the relationship between the permission amount held and the underlying state.

As identified in @sec:results-unsupported, VMIR currently provides no mechanism to assert that possessing positive permission to a location implies its receiver reference must be non-null. To address this, we propose extending location types into full top-level declarations. This would allow locations to explicitly define the semantics necessary to support robust field reasoning. @lst:future-location-types provides a sketch of how this missing information could be encoded.

#vmir(
  caption: [A sketch of the proposed extension of location types into full declarations, enabling them to specify invariants relating the location to its held permission amount.],
  label: "lst:future-location-types",
)[```vmir
function f#loc(e0: Ref): f     // Ref to location mapping
  ensures f#inv(result) == e0

function f#inv(e0: f): Ref     // location to Ref inverse mapping
  ensures f#loc(result) == e0

location f: Int @ 1/1
  perm > 0/1 ==> f#inv(this) != null
  f#inv(this) == null ==> perm == 0/1
```]

In this proposed syntax, #vm[`f`] is elevated to a standalone location declaration. It continues to specify the stored type (#vm[`Int`]) and the permission bound (#vm[`1/1`]), but it may now optionally declare a set of invariants that are enforced whenever the location exists in the heap.

These invariants utilize two special keywords: #vm[`this`], representing the location instance itself, and #vm[`perm`], representing the permission amount held in the heap. The first invariant in the example dictates that if the heap holds positive permission to the location, the associated receiver reference, retrieved via the inverse function #vm[`f#inv`]), cannot be null. Conversely, the second invariant enforces that if the receiver is null, the corresponding permission amount must be exactly zero. By introducing these explicit invariants, VMIR can formalize the implicit assumptions about fields that are natively hardcoded into existing verifiers such as Silicon.

=== Improving Exhale Performance
Currently, the most significant performance bottleneck in Helium is proving
that sufficient permission is held at a location. We believe that the current
mechanism for checking sufficiency in non-trivial cases is suboptimal. This
inefficiency is particularly problematic when reasoning about conditional
permissions or branching logic, because the fallback mechanism attempts to
ensure sufficiency by traversing down the permission tree.

=== Parallel Branch Information Isolation
In the current implementation, Helium shares a single, global e-graph across
all parallel branches within a program. This design introduces branch pollution.
Because facts are accumulated globally, a branch verified later in the sequence
can inadvertently observe facts learned in a mutually exclusive branch that was
verified earlier. Although these facts remain guarded by their respective path
conditions, ensuring no soundness issues arise, this shared state can lead to
unpredictable verification behavior where the arbitrary order of branch
traversal influences the outcome.

To resolve this, we propose adopting a fork-join execution model for the e-graph
state. Under this model, when execution reaches a control-flow fork, each branch
receives an isolated copy of the e-graph to perform its verification. Crucially,
the e-graph remains assumption-free. The path condition itself is not globally
assumed to be true, and any facts derived within the branch remain explicitly
guarded by that path condition.

Upon reaching a join point, the independent e-graphs are merged. Conceptually,
this entails computing the union of the divergent e-graphs, although maintaining
stable e-class identifiers across the copies presents an implementation
challenge. Following the merge, the unified e-graph resumes execution with the
complete, conditionally guarded knowledge acquired from all predecessor paths.
This ensures that verification remains deterministic and independent of
traversal order.

=== Forking Execution Model
As an alternative to resolve the issues raised in the previous two sections, it
may be beneficial in certain cases to completely fork the execution state at a
branch point. This strategy would align Helium with how Silicon handles
branching and provide two immediate benefits. First, it addresses the exhale
performance bottleneck by reducing the individual state size within each
execution branch. The state only needs to encode the traversed blocks, and the
e-graph can be minimized by directly assuming the path condition, which in turn
collapses both the heap representation and the e-graph. Second, it resolves the
branch pollution problem by ensuring each branch operates within its own
completely isolated state.

However, this approach reintroduces the overhead typical of Silicon, including
a potential exponential state explosion on sequentially and independently
branching code. Given the difficulties of maintaining a single global e-graph
state across an entire verification unit, we strongly believe this alternative
is worth exploring. The performance advantages of the lightweight underlying
e-graph would still apply and help maintaining a performance edge over Silicon.

=== Contextual Resources
Currently, Helium's resources are only allowed to be global definitions. This
restricts their usefulness. Concretely, a loop invariant is essentially a resource
that is only valid within the context of the method it is defined in. Currently,
Helium simply inlines the invariant into the method body in multiple places, which
means that well-formedness of the invariant has to be re-checked in each of those places.

Adding the support for contextual resources would allow Helium to verify well-formedness
of the invariant once, compiling it into a recipe and then using it for cheaper at
every place it needs to be used.

=== Improving the Reasoning Capabilities of Helium
Helium's reasoning capabilities are currently limited by the rewrite rules it uses.
Instead of trying to force the e-graph to prove more complex obligations, we might
want instead to integrate an SMT solver into Helium. The idea would be to use the
e-graph as a preprocessor to discharge as many obligations as possible, and only
ever query the SMT solver when the e-graph is insufficient. One way to do this
would be to maintain the solver's state consistent with the e-graph, but only
actually query it when needed.

=== Improving the Rewrite Rule Set and Scheduling
The current rewrite rule set Helium employs is very basic. It always runs the
exact same set of rules, no matter the reason they are being applied. We believe
there might be some performance gains to be had by both adjusting the rewrite
rules present, as well as, picking which ones are relevant to run at the current goal.

Second, when the rules are run, they are run in a round-robin schedule, until the
fix-point is reached. We believe there might be some performance gains, if instead
we gave priority to some rules over others.

=== Boolean Permission Model for Functions
In heap-dependent functions, the default semantics of Viper is to use only wildcard
and none permissions. We could simplify the reasoning even further by introducing a
boolean permission model for verifying heap-dependent function. In this model, the
permission would be either present or absent. Additionally this simplifies the
unfolding expressions, to simply add the unfolded predicate body, without removing a
wildcard amount of permission. All in all, this would simplify the reasoning required,
and possibly make verifying functions a tiny amount faster.
