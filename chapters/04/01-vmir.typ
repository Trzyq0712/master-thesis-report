#import "../../macros.typ": *

== VMIR: Viper Mid-Level Intermediate Representation <sec:impl-vmir>

Viper is a highly expressive language designed to be read and written by humans. Consequently, it incorporates syntactic sugar to improve readability and ease of programming. However, this is not ideal from a verification perspective, as the verifier must account for all implicit semantics in the surface language.

We propose a smaller, more focused intermediate representation, which we call VMIR (Viper Mid-Level Intermediate Representation). VMIR simplifies the verification process by modifying several key aspects of Viper:

- *Explicit Semantics:* All syntactic sugar is eliminated. For example, in surface Viper, access expressions like #vi[acc(x.f)] carry an implicit permission amount of #vi[write]. VMIR removes these assumptions, requiring all such details to be stated explicitly.

- *Self-Contained Representation:* While Silicon @silicon relies on the Silver project @silver to resolve implicit details, our verifier cannot directly depend on it due to the programming language boundary. Because VMIR explicitly encodes all semantics, it serves as a fully self-contained textual format, allowing any external verifier to process it independently.

- *Reduced Operator Set:* VMIR retains only a single boolean connective: the ternary operator. As a result, #vi[`a && b`] is rewritten as #vm[`a ? b : false`], and #vi[`a || b`] becomes #vm[`a ? true : b`]. This ensures there is only one canonical way to represent an expression.

- *Explicitly Typed Temporaries:* To simplify reasoning, VMIR eliminates mutable variables. This shifts the focus to the values themselves rather than their changes over time. It also flattens nested expressions, assigning every subexpression to an explicitly typed temporary. Consequently, the representation naturally assumes a Single Static Assignment (SSA) form.

- *Explicit Heap State:* In Viper, the heap has a temporal nature. It means reading a field #vi[`x.f`] implicitly reads from the current heap, while #vi[`old(..)`] evaluates expressions in some earlier version of the heap. In VMIR, the heap is treated as a special, explicit value that instructions produce and consult.

- *Unified Heap Objects:* VMIR unifies the concepts of predicates and fields. While Silicon treats fields and predicates stored in the heap separately, storing a predicate instance in VMIR is equivalent to storing an ADT (Algebraic Data Type) instance that describes the predicate's footprint. This allows the verifier to reason about all heap objects uniformly.

- *Instruction Decomposition:* VMIR breaks down Viper's complex operations into a minimal set of core instructions. For instance, a method call is decomposed into two distinct instructions: exhaling the precondition resource, and inhaling the postcondition. Similarly, a predicate fold is exactly equivalent to exhaling the predicate body and adding a heap chunk representing the folded predicate.

The following sections detail how different Viper constructs are lowered to VMIR, and how the verifier reasons about them.
