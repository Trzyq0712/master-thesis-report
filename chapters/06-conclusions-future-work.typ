#import "../macros.typ": *
#import "../generated/perf-rust-scalars.typ": *
#import "../generated/perf-viper-scalars.typ": *

= Conclusion

In this thesis, we presented a novel approach to verifying Viper programs by introducing the Viper Mid-level Intermediate Representation (VMIR) and an associated verifier, Helium. Our work successfully demonstrates that the complex, feature-rich Viper language can be significantly simplified and verified with much higher performance than the state-of-the-art Silicon verifier.

The introduction of VMIR plays a crucial role in simplifying Viper's semantics. By reducing method contracts, heap-dependent function preconditions, and predicates to a unified concept of a VMIR resource, we drastically decrease the conceptual surface area of the language. Complex, implicit operations in Viper, such as calling methods or folding and unfolding predicates, are expressed as simple, explicit operations on heap locations and VMIR resources. This transformation flattens the input into a straightforward, explicitly typed format, removing ambiguities and allowing the verifier to operate on a minimal instruction set without losing expressiveness.

Building on the simplicity of VMIR, Helium introduces an optimized verification architecture. By managing resources explicitly, Helium ensures that permissions and resources only need to be verified once. Furthermore, Helium employs an e-graph data structure for cheap proof discharging. By leveraging e-graph saturation to accumulate facts and permissions, the verifier handles the majority of proof obligations through highly efficient rewrite rules. Because Helium lacks extended reasoning capabilities, it is specifically designed to deal with spec-less programs, focusing on being exceptionally fast at discharging programs with highly structured obligations.

Our evaluation confirms that this architecture yields significant performance improvements. On hand-written Viper benchmarks, Helium achieves a #viper-ratio-total speedup over Silicon. Across the Prusti-generated corpus, Helium demonstrates a #rust-ratio-geo average speedup. The performance gains are especially spectacular on straight-line code, where Helium reaches #rust-best-ratio on #rust-best due to its ability to accumulate facts linearly without branching overhead. However, on heap-heavy, highly branched code, the advantage deteriorates, yielding performance similar to Silicon, primarily due to the computational cost of reconciling conditional permission chunks at control-flow merge points.

In summary, this work demonstrates that reducing permission-based verification to explicit resource management and e-graph saturation is a viable and highly performant architecture for structured, spec-less programs.

== Future Work <sec:future-work>
In this section we discuss relevant directions for future work, for further improving
Helium and VMIR. The list is ordered by our percpetion of the relevance of each item.

=== Adding Support for Missing Viper Constructs
As detailed in @sec:results-qualitative, several Viper constructs are currently
unsupported by Helium. Adding support for these missing features, such as
built-in containers, existential quantifiers, and termination measures, remains
an important goal for future work.

Magic wands and quantified permissions are also missing, but stand out as being
particularly significant. Considering them will require a careful evaluation of how they can be
integrated with VMIR's shared heap location abstraction, as both constructs
inherently entail them.

=== Extending Location Types
The current design of VMIR location types is insufficiently expressive for certain heap properties. While a location type encodes the stored value type, the location group, and the maximum permission bound (e.g., #vm[`&[f] Int @ 1/1`]), it lacks the structural capacity to express invariants regarding the relationship between the permission amount held and the underlying state.

As identified in @sec:results-qualitative, VMIR currently provides no mechanism to assert that possessing positive permission to a location implies its receiver reference must be non-null. To address this, we propose extending location types into full top-level declarations. This would allow locations to explicitly define the semantics necessary to support robust field reasoning. The sketch below shows how this missing information could be encoded, with a location type carrying an invariant relating it to the permission amount held.

#no-numbers[```vmir
function f#loc(e0: Ref): f     // Ref to location mapping
  ensures f#inv(result) == e0

function f#inv(e0: f): Ref     // location to Ref inverse mapping
  ensures f#loc(result) == e0

location f: Int @ 1/1
  perm >r 0/1 ==> f#inv(this) != null
  f#inv(this) == null ==> perm == 0/1
```]

In this proposed syntax, #vm[`f`] is elevated to a standalone location declaration. It continues to specify the stored type (#vm[`Int`]) and the permission bound (#vm[`1/1`]), but it may now optionally declare a set of invariants that are enforced whenever the location exists in the heap.

These invariants utilize two special keywords: #vm[`this`], representing the location instance itself, and #vm[`perm`], representing the permission amount held in the heap. The first invariant in the example dictates that if the heap holds positive permission to the location, the associated receiver reference, retrieved via the inverse function #vm[`f#inv`]), cannot be null. Conversely, the second invariant enforces that if the receiver is null, the corresponding permission amount must be exactly zero. By introducing these explicit invariants, VMIR can formalize the implicit assumptions about fields that are natively hardcoded into existing verifiers such as Silicon.

=== Improving Exhale Performance
Currently, the most significant performance bottleneck in Helium is proving
that sufficient permission is held at a location. We believe that the current
mechanism for checking sufficiency in non-trivial cases is suboptimal. This
inefficiency is most visible when reasoning about conditional permissions or
branching logic, where sufficiency is established by descending the permission
tree, which @sec:results-discussion measures.

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
Currently, Helium's resources are restricted to being global definitions, which
limits their utility. For example, a loop invariant is essentially a resource
that remains valid only within the context of its enclosing method. Presently,
Helium simply inlines the invariant into the method body at multiple locations,
requiring the well-formedness of the invariant to be repeatedly verified at each
instantiation.

Adding support for contextual resources would enable Helium to verify the
well-formedness of an invariant exactly once. The invariant could then be
compiled into a recipe, so that applying it wherever the method needs it costs
one replay of that recipe.

=== Improving the Reasoning Capabilities of Helium
Helium's reasoning capabilities are currently constrained by its reliance on a
fixed set of rewrite rules. Rather than forcing the e-graph to handle more
complex proof obligations, a promising direction would be to integrate an SMT
solver into Helium. Under this hybrid approach, the e-graph would serve as an
efficient preprocessor, discharging the majority of structural obligations,
while the SMT solver would only be queried as a fallback when the e-graph proves
insufficient. One potential implementation strategy involves continuously syncing
the solver's state with the e-graph, ensuring that queries are both precise and
efficient when they inevitably arise.

=== Improving the Rewrite Rule Set and Scheduling
The current set of rewrite rules employed by Helium is relatively rudimentary.
The verifier uniformly applies the exact same set of rules regardless of the
context or the specific obligation being discharged. We anticipate significant
performance gains could be achieved by carefully refining the available rewrite
rules and dynamically selecting only those relevant to the current proof goal.

Furthermore, these rules are currently executed using a naive round-robin
scheduling strategy until a fix-point is reached. Prioritizing the execution
of certain high-impact rules over others could reduce unnecessary matching
overhead and further optimize the saturation process.

=== Boolean Permission Model for Functions
For heap-dependent functions, the default semantics in Viper rely solely on
wildcard and none permissions. We propose simplifying this reasoning further by
introducing a boolean permission model specifically for verifying
heap-dependent functions. Under this model, permissions would be strictly
binary, representing either the presence or absence of access.

This approach would also streamline unfolding operations. Instead of removing a
wildcard amount of permission, the verifier could simply add the unfolded
predicate body to the state. Overall, adopting a boolean permission model would
reduce the reasoning overhead and potentially yield minor performance
improvements when verifying functions.
