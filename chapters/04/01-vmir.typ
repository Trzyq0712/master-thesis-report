#import "../../macros.typ": *

== VMIR: Viper Mid-Level Intermediate Representation <sec:impl-vmir>

// Before a program reaches our verifier, it is first lowered to an intermediate
// representation, which we call _VMIR_. The main purpose of this translation is to
// rid of syntactic sugars of Viper, and break down complex constructs into a
// smaller core set of primitives. The main benefit of this is that the implementation of the verifier becomes significantly simpler.

Viper is a highly expressive language designed to be read and written by humans. Consequently, it incorporates syntactic sugar to improve readability. However, this is not ideal from a verification perspective, as the verifier must account for all implicit semantics within the surface language.

We propose a smaller, more focused intermediate representation, which we call VMIR (Viper Mid-Level Intermediate Representation). VMIR modifies several key aspects of Viper.

First, all syntactic sugar is eliminated. For example, access expressions like #vi[acc(x.f)] carry an implicit permission amount of #vi[write]. While Silicon @silicon relies on the Silver project @silver to fill in these missing details, our verifier cannot directly depend on it due to programming language differences. A major benefit of VMIR is that it serves as a fully self-contained textual representation, allowing any potential verifier to process it.

Second, VMIR simplifies the verification process by removing redundant operators. Specifically, it retains only a single boolean connective: the ternary operator. As a result, #vi[a && b] is rewritten as #vm[a ? b : false], and #vi[a || b] becomes #vm[a ? true : b]. This ensures there is only one canonical way to represent an expression in VMIR.

Third, VMIR adopts single static assignment (SSA) form. By eliminating the concept of mutable variables, we only have to reason about a value itself, rather than how it changes over time. Furthermore, VMIR flattens nested expressions, assigning each subexpression to a temporary variable with an explicit type. Consequently,any dependent of VMIR no longer needs to include any sort of type inference.

Fourth, VMIR makes the heap explicit. In Viper the heap has a temporal nature. Reading a field #vi[`x.f`] implicitly reads from the current heap, while #vi[`old(..)`] expressions are used to evaluate heap dependent expressions in some earlier version of the heap. In VMIR, the heap is a special value that can be produced and consulted by instructions.

Fifth, VMIR unionizes the concepts of predicates and fields. While in Silicon fields and predicates stored in the heap are treated separately, in VMIR a storing a predicate instance is equivalent to storing an ADT (Algebraic Data Type) instance that describes the predicate's footprint. This allows the verifier to reason about any heap objects in a uniform way.

Sixth, VMIR breaks down complex Viper's complex operations into a smaller set of core instructions. More concretely, a method call is broken down into two instructions: exhaling the precondition resource, and inhaling the postcondtion one. In the same way, a predicate fold is exactly equivalent to exhaling the predicate body and adding a heap chunk representing the folded predicate.

The next sections will describe how different Viper constructs are lowered to VMIR, and how the verifier reasons about them.


#viper(
  caption: [A method that takes permission to one field, writes through it, and
    gives half of it back.],
  label: "lst:vmir-glance",
)[```viper
field f: Int

method bump(x: Ref)
{
  inhale acc(x.f)
  var old_v: Int := x.f
  x.f := 42
  assert 0 <= old_v && 0 <= x.f
  exhale acc(x.f, 1/2)
}
```]

#lvmir(
  caption: [The lowering of @lst:vmir-glance — and the whole of what VMIR adds:
    a heap is a temporary like any other.],
  label: "lst:vmir-glance-lowered",
)[```lvmir
e0: Ref := fresh                // x
h0 := empty + f(e0) @ 1/1 with fresh

e1: Int := *[h0] f(e0)          // old_v
h1 := h0 assign(f(e0), 42)

e2: Int := *[h1] f(e0)
e3: Bool := 0 <= e1
e4: Bool := 0 <= e2
e5: Bool := e3 ? e4 : false    // 0 <= old_v && 0 <= x.f
assert e5

h2, _ := h1 - f(e0) @ 1/2
```]

The lowering does not start from source text. It starts from a typed abstract
syntax tree. The resolution that produces one is the same Silver @viper @silver
performs. The ambiguities of the surface language are thus settled before VMIR is
in question. Every intermediate expression carries its inferred type. The values
Viper allows a program to leave implicit have been filled in, such as the amount
in an #vi[`acc(x.f)`] written without one, which is #vi[`write`]. No lowering rule
therefore has to recover what a piece of syntax meant.

VMIR is in static single assignment form, and expressions
are flattened. Every operation is an instruction of its own. Its operands are
temporaries rather than expressions, and its result is a fresh temporary with the
type written out. The verifier therefore has one rule per operation, and an
operand is a name it already holds rather than a tree it has to walk again. The parameter arrives as a #vm[`fresh`] value and no more.
Nothing is assumed about it. There is no store mapping #vi[`x`] to anything, only
the temporary the name was lowered to. A declaration with an initialiser produces
no instruction of its own either. The name #vi[`old_v`] denotes the temporary
#vm[`e1`]. An assignment to a source variable rebinds the name rather than
building anything.

Three instructions in @lst:vmir-glance-lowered introduce nothing and are worth
naming once. #vm[`fresh`] produces an unconstrained value of its type.
#vm[`assert`] raises an obligation on a boolean. #vm[`assume`] adds one to what is
known without proving it, and appears from @sec:impl-execution onwards.

Temporaries come in three sorts. An #vm[`e`] temporary names a value in the
source language's sense. An #vm[`h`] temporary names a _heap state_. A #vm[`p`]
temporary names a permission amount, and is the subject of a later paragraph. The
sorts are kept apart in the IR itself, so nothing can route a permission into a
term a proof obligation is stated over.

An instruction that consults the heap says which one it consults. An instruction
that changes the heap returns the new one. The chain #vm[`h0`] through #vm[`h2`]
is thus the entirety of what a verifier over Viper would carry implicitly as "the
current heap". A heap on the left of the #vm[`:=`] means a state was produced. A
heap in brackets means one was consulted. The read #vm[`*[h0] f(e0)`] is the value
stored at location #vm[`f(e0)`] in #vm[`h0`], and #vm[`empty`] is the heap that
holds nothing.

Making the heap an ordinary SSA temporary is what removes the notion of a
"current" heap. A method's pre-state, a loop's frame and the heap an
#vi[`unfolding`] opens are all just heaps that something else still names. None of
the three needs a construct of its own. Scoping an effect is a matter of which
temporary an instruction reads.

This is what distinguishes the two reads in @lst:vmir-glance-lowered. Both lower
the same source expression #vi[`x.f`]. They differ only in the heap they name.
#vm[`e1`] reads #vm[`h0`], the heap the #vi[`inhale`] produced. #vm[`e2`] reads
#vm[`h1`], the heap the assignment produced. Framing is then a question about
which temporary an instruction mentions, rather than an argument the verifier has
to make. The rest of the chapter relies on this property the most.

Three further details are visible in that chain. Each is treated in a section of
its own.

The first is that the heap is addressed by #vm[`f(e0)`] rather than by
#vi[`x.f`]. What a program holds permission to is a _location_, and a field is a
function from a receiver to one (@sec:impl-fields). A location has a type of its
own, written #vm[`&[g] T @ p`]. It names the group the location belongs to, the
type of the value held there, and the largest permission anything may hold to it.
All three live in the type rather than in a table beside the program, so a
location describes itself. That is what allows a location to be computed. One may
be produced by a ternary or returned from a call, and no instruction that moves
permission needs a case for where it came from (@sec:impl-heap).

The second is that the instruction that adds permission carries a trailing
#vm[`with`], its _bind point_. It names where the value of the created chunk comes
from. There are three forms. #vm[`with fresh`] havocs the value, which is what an
#vi[`inhale`] wants, since it says nothing about what is at the location it hands
over. #vm[`with e1`] binds it to a term already in scope. #vm[`with self`]
declares a slot of the enclosing resource's own footprint, and belongs to a
resource body as #vm[`with fresh`] belongs to a method body
(@sec:impl-predicates). There is no default.
Producing a value is the operation with soundness consequences, so the dangerous
case is never the one a reader skips (@sec:impl-heap-interaction).

The third is that the subtraction on the last line yields a second result
alongside the heap. That result is the value found where permission was taken
away. Nothing here needs it, so it is bound to #vm[`_`] and never built. What an
instruction yields is part of what that instruction is, and not an accident of
what a later one happens to read. The blank is written by the translator, so no
pass over the program may introduce one.

A permission is not an expression. It is a small syntactic category of its own,
and only three things can be written in the position after an #vm[`@`]. An
amount, which is a rational term. A bare #vm[`wildcard`], which carries nothing
under it and stands for a positive but unspecified share. Or a ternary gating one
permission shape by a boolean. This is the same restriction Viper imposes. Keeping it in the
grammar lets a rule dispatch on the shape it was given, rather than on what the
amount turned out to equal (@sec:impl-wildcards). Where a permission needs building up, it is named by a
#vm[`p`] temporary. Every listing in this chapter writes its amounts out, so none
of them shows one.

An instruction may carry a _path condition_, written in angle brackets after the
#vm[`:=`]. A path condition is a _cube_: a conjunction of booleans already in the
graph, each taken with a polarity. It is computed at lowering time, where the
frontend still knows which branches lead to the instruction, and it is exact
rather than approximate. Not every instruction takes one. An instruction that only
builds a term needs none, so arithmetic and comparisons are emitted flat however
deeply nested in conditions they stand. Carrying the condition on the instruction
is what lets the verifier keep a single state where a forking symbolic execution
keeps one per path (@sec:impl-execution).

A predicate body, a method precondition, a method postcondition
and a function precondition are one construct in VMIR. We call it a _resource_.
A resource is a named parameterised pair: a heap delta, and a boolean claimed to
hold of it. Viper keeps these apart. A predicate is a declaration, and a contract
is syntax attached to a member. A verifier over Viper therefore needs its produce
and consume rules to know which of the two it is looking at. Collapsing them means
the operations that walk a footprint, take permission and give it back are written
once. Predicates, contracts and calls then use the same ones
(@sec:impl-predicates).

A resource is declared much as a method is, with a parameter list and a body. Its
last line is a #vm[`result:`] naming the pair the body evaluated to. The body
is ordinary straight-line VMIR rather than an assertion in Viper's sense. A
conjunction of accessibility predicates becomes a sequence of adds threading one
heap, so how the source bracketed its conjuncts leaves no trace. A body describes
one level of footprint and no more.

Taking and giving back a whole resource are instructions of their own,
#vm[`inhale`] and #vm[`exhale`]. They are a different thing from the add and the
subtract above, which move permission at a single location. A resource operation
walks the whole footprint, and it carries the body's boolean with it.
#vm[`exhale`] asserts that boolean and #vm[`inhale`] assumes it.

The language is smaller than Viper in ways that are
deliberate rather than incidental. It has no negation, conjunction, disjunction or
implication. Its only boolean connective is the ternary #vm[`c ? a : b`], and the
other four are written in terms of it. #vi[`!b`] becomes #vm[`b ? false : true`].
The #vi[`&&`] of the assertion above becomes #vm[`e3 ? e4 : false`].
#vi[`a || b`] becomes #vm[`a ? true : b`]. An implication #vi[`c ==> e`] becomes
#vm[`c ? e : true`], which is why a goal with a #vm[`true`] arm is an implication
written as a conditional (@sec:impl-proving). One reduction rule then covers what
would otherwise need several, and the prover's tiers are stated over one shape
instead of five. Every desugaring in this chapter has this shape. A surface form
is replaced by the one primitive that already had to exist.

The absence of negation is a statement about values, not about the whole
notation. A cube's literals each carry a polarity, so a block reached when
#vm[`e0`] is false is headed by the cube #vm[`<!e0>`]. That polarity is part of
how a path condition is stored and never becomes a boolean term the prover has to
reason through.

VMIR also has no assertion language separate from its expression language. An
assertion is lowered into the same instructions any other expression is. And it
has no notion of a store. A source variable is lowered to the temporary it named,
and there is no map from names to values at run time.

Nor does it have structured control flow. A method body is a block graph, and a
source #vi[`if`] is resolved into one before lowering, so nothing downstream walks
a syntax tree. A block is three things: the cube it is reached under, a _join
phase_ that reconciles its predecessors, and a _body phase_ of straight-line VMIR.
Joins are binary. A label reached by several #vi[`goto`]s, which is Prusti's
normal shape, is normalised into a chain of binary joins. Blocks are executed in
topological order with back edges cut (@sec:impl-cfg).

The declaration forms are #vm[`function`], #vm[`domain`] with its #vm[`axiom`]s,
#vm[`adt`] and #vm[`resource`]. A #vm[`@`] or #vm[`#`] in a name marks a member
as derived rather than written by the source program. A predicate's snapshot type
is #vm[`own_i32@snap`], its location function #vm[`own_i32@loc`], and a method's
precondition #vm[`m#requires`]. Types stay parametric. A
generic declaration is lowered once and the verifier mints a monomorphic instance
per use, so the IR carries no copy per type argument. #vm[`Option`] is the one
type the verifier injects rather than translation producing it, which keeps
hand-written VMIR valid without a Viper program behind it.

VMIR is a language with a syntax rather than just
an internal data structure. The listings in this chapter are written in it. This
was a goal of the design rather than a consequence of it. A program can be
printed after lowering, read back, diffed against an expected form, and handed to
something other than the verifier this thesis builds. A lowering is therefore
testable on its own terms. An alternative backend over the same IR needs no part
of what follows, even if it discharges the obligations a different way.

The real form spells out mechanical detail that a listing does
not always need to carry. A listing tagged _VMIR-lite_ in its corner drops that
detail. What is left is what the snippet is about. The assignment of
@lst:vmir-glance-lowered is written in full below. An address is computed on a
line of its own, at the location type @sec:impl-heap gives it. The receiver is
the temporary the parameter was lowered to, rather than the source name.

#no-numbers[```vmir
e6: &[f] Int @ 1/1 := f(e0)
h1 := h0 assign(e6, 42)
```]

The difference is mechanical throughout. It is the same difference wherever the
two forms are set beside each other. VMIR-lite is the same language. It agrees
with the real form wherever the point being made lives. A listing tagged plain
VMIR is what the verifier would actually be given.
