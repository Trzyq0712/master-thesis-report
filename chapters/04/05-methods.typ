#import "../../macros.typ": *

== Methods <sec:impl-methods>

A method is the most basic unit of verification in Viper. Its body is checked once,
against the state its own contract describes, and every call to it uses the
contract in place of the body enabling modular verification. This section
describes both ends: what a method contract becomes in VMIR, how Helium
verifies a body against one, and what a call site executes.

For the remainder of this section we only assume straight-line bodies with no
control flow, and @sec:impl-cfg builds on top of this and describes how VMIR and
Helium manage it later. We start from @lst:method-bare, a method that touches
the heap and carries no contract at all.

#lowering(
  caption: [A method that increments a field while holding no permission to it.
    The body starts from #vm[`empty`], so the read fails.],
  label: "lst:method-bare",
)[```viper
field val: Int

method bump(c: Ref)
{
  c.val := c.val + 1   // fails
}
```][```vmir
method bump {
  e0: Ref := fresh         // c
  e1: &[val] Int @ 1/1
     := val(e0)
  e2: Int := *[empty] e1   // fails
  e3: Int := e2 + 1
  h0 := empty assign e1
        with e3
  }
```]

A method body starts from #vm[`empty`]. Each parameter arrives as a #vm[`fresh`]
value, unconstrained beyond its type, and the heap the first instruction reads
is the empty one. The read into #vm[`e2`] therefore fails: a dereference demands
positive permission at #vm[`val(c)`], and permission enters a body through its
contract. A precondition is the clause that can supply it.

=== Method contracts

@lst:method-pre gives #vi[`bump`] permission to the field it reads through. The
clause is a heap fragment together with an assertion about it, which is the pair
@sec:impl-predicates already has a construct for.

#lowering(
  caption: [A Viper method precondition becomes a resource in VMIR.],
  label: "lst:method-pre",
)[```viper
method bump(c: Ref)
  requires acc(c.val, write)
```][```vmir
resource bump#requires(e0: Ref) {
  e1: &[val] Int @ 1/1
     := val(e0)
  h0 := empty + e1 @ 1/1 with self
  result: (h0, true)
}
```]

A #vi[`requires`] clause is a heap fragment together with a self-framing
assertion, which is what a resource is, so the translator lowers a method
precondition to one. The resource takes the method's parameters, and its body is built
exactly as @sec:impl-predicates builds a predicate's.

An #vi[`ensures`] clause becomes a resource as well, and @lst:method-post is
that declaration. It takes one parameter the method's signature does not
mention, because a postcondition may name the state the method was entered in
and the resource has to be given that state from somewhere.

#lowering(
  caption: [The postcondition as a resource. Its trailing parameter is the
    precondition's snapshot, and its first instruction widens that snapshot back
    into a heap.],
  label: "lst:method-post",
)[```viper
method bump(c: Ref)
  requires acc(c.val, write)
  ensures acc(c.val, write)
```][```vmir
resource bump#ensures(e0: Ref,
    e1: bump#requires@snap) {
  h0 := empty inhale
        bump#requires(e0) @ 1/1
        with e1
  e2: &[val] Int @ 1/1
     := val(e0)
  h1 := empty + e2 @ 1/1 with self
  result: (h1, true)
}
```]

A postcondition's parameters are the method's parameters, then its return
variables, and last the precondition's snapshot. It takes that last one whenever
the method has a precondition. From that snapshot the postcondition rebuilds
the pre-state of the method, and its own well-definedness is established against
that state. @lst:method-old adds the clause that pre-state exists for.

// Short enough never to need splitting, and the global `breakable: true` on
// listing figures otherwise strands the caption on the following page.
#block(breakable: false, lowering(
  caption: [The two reads differ in one temporary. #vm[`e3`] consults the delta
    the postcondition grants, #vm[`e4`] the state the method was entered in.],
  label: "lst:method-old",
)[```viper
method bump(c: Ref)
  requires acc(c.val, write)
  ensures acc(c.val, write)
  ensures c.val
       == old(c.val) + 1
```][```vmir
resource bump#ensures(e0: Ref,
    e1: bump#requires@snap) {
  h0 := empty inhale
        bump#requires(e0) @ 1/1
        with e1
  e2: &[val] Int @ 1/1
     := val(e0)
  h1 := empty + e2 @ 1/1 with self
  e3: Int := *[h1] e2
  e4: Int := *[h0] e2
  e5: Int := e4 + 1
  e6: Bool := e3 == e5
  result: (h1, e6)
}
```])

The opening inhale rebuilds the pre-state at #vm[`1/1`], so every chunk returns
at the amount the precondition named for it. Its boolean makes every invariant
the precondition establishes available for the rest of the body. Its chunks frame
the reads that follow.

#vm[`e3`] and #vm[`e4`] are the same read at the same address, separated by the
heap each names: #vm[`e3`] takes #vi[`c.val`] from the postcondition's own
delta, #vm[`e4`] takes #vi[`old(c.val)`] from the pre-state. Since heaps are
values, the ordinary dereference instruction executes an #vi[`old`] expression.
A postcondition reading past the precondition's footprint fails to discharge
at #vm[`h0`], exactly as an unframed read would.

Both contract resources are verified at their declarations, on the terms
@sec:impl-predicates gives any resource. The precondition is verified first,
since the postcondition is verified with the pre-state that the precondition's
inhale rebuilds already in hand. Each leaves behind a record of recipes
(#pararef(<para:impl-slot-recipes>, [Slots and recipes])), so a use of a
contract rebuilds its footprint from that record instead of walking the clause,
and well-definedness is settled once, at the declaration.

=== Verifying a method

@lst:method-full is the method with a return variable and both contracts, which
is every piece of the frame Helium puts around a body. The frame is three
phases: a prologue that builds the entry heap out of the precondition, the body
itself, and an exit that checks the postcondition against what the body left.

#lowering(
  caption: [A complete method: the prologue builds the entry heap, the body
    runs, and the exit checks the contract against what the body left.],
  label: "lst:method-full",
)[```viper
method bump(c: Ref)
    returns (before: Int)
  requires acc(c.val, write)
  ensures acc(c.val, write)
  ensures before == old(c.val)
  ensures c.val == before + 1
{
//@
  before := c.val
  c.val := before + 1
//@
}
```][```vmir
method bump {
  e0: Ref := fresh         // c
  e1: Int := fresh         // before
  e2: bump#requires@snap := fresh
  h0 := empty inhale
        bump#requires(e0) @ 1/1
        with e2
  //@
  e3: &[val] Int @ 1/1
     := val(e0)
  e4: Int := *[h0] e3      // before
  e5: Int := e4 + 1
  h1 := h0 assign e3 with e5
  //@
  _, _ := h1 exhale
          bump#ensures(e0, e4, e2)
          @ 1/1
}
```]

The prologue mints a fresh value for each parameter and for each return
variable, then a fresh handle for the precondition's snapshot, and inhales the
precondition against #vm[`empty`]. Binding the inhale to that handle, rather
than writing #vm[`with fresh`], is what carries the pre-state to the
postcondition at the exit.

The body is made up of the usual VMIR instructions, each treating #vm[`h0`] as
it would any other heap. The read into #vm[`e4`] finds the chunk the inhale put
at #vm[`val(c)`], the permission the same read ran without in @lst:method-bare.

The exit exhales the postcondition. Its arguments are the method's parameters,
the final values of the return variables, and the precondition's snapshot. It
raises the sufficiency obligation of a subtraction
(@sec:impl-heap-ops) at each slot of the postcondition's footprint and asserts its boolean. Both of its results are
discarded, which is why the listing blanks the pair: the exit is the last
instruction of the method.

A body may also reach back to an earlier heap of its own. A #vi[`label`] names
the state at a point, and #vi[`old[L](e)`] reads the state that name stands for.
@lst:method-label writes one field twice and asks about the value in between.

#lowering(
  caption: [A label names a heap. The read that mentions it says #vm[`h1`] where
    an ordinary read would say #vm[`h2`].],
  label: "lst:method-label",
)[```viper
method twice(c: Ref)
  requires acc(c.val, write)
{
  c.val := 1
  label mid
  c.val := 2
  assert old[mid](c.val) == 1
}
```][```vmir
method twice {
  e0: Ref := fresh         // c
  e1: twice#requires@snap := fresh
  h0 := empty inhale
        twice#requires(e0) @ 1/1
        with e1
  e2: &[val] Int @ 1/1
     := val(e0)
  h1 := h0 assign e2 with 1
  h2 := h1 assign e2 with 2
  e3: Int := *[h1] e2
  e4: Bool := e3 == 1
  assert e4
}
```]

The translation records which heap each label stands for. #vi[`mid`] is recorded
as #vm[`h1`], the heap the preceding statement produced, and
#vi[`old[mid](c.val)`] reads from it. An unlabelled #vi[`old`] inside a body
reads #vm[`h0`], the heap the prologue's inhale produced.

=== Calling a method <sec:impl-calls>

A call lowers to a pair of resource operations on the caller's heap, the
callee's contract standing in for its body. Nothing of the callee is executed at
the call site, and nothing about it is needed beyond the two resources its
declaration already produced. @lst:method-call calls the method of
@lst:method-full.

#lowering(
  caption: [A call is an exhale of the callee's precondition and an inhale of
    its postcondition, with the return values minted between the two.],
  label: "lst:method-call",
)[```viper
method client(x: Ref)
  requires acc(x.val, write)
{
  var b: Int
  b := bump(x)
}
```][```vmir
method client {
  e0: Ref := fresh         // x
  e1: client#requires@snap
     := fresh
  h0 := empty inhale
        client#requires(e0) @ 1/1
        with e1
  e2: Int := fresh         // b
  h1, e3: bump#requires@snap
     := h0 exhale
        bump#requires(e0) @ 1/1
  e4: Int := fresh         // b
  h2 := h1 inhale
        bump#ensures(e0, e4, e3)
        @ 1/1 with fresh
}
```]

The exhale takes the precondition's footprint out of the caller's heap, on the
same terms as the exit of a body. It also yields #vm[`e3`], the precondition's
snapshot, recording what the caller's heap held at each of the precondition's
slots. That is the trailing argument the postcondition takes. Between the two
instructions the call mints a fresh value for each return variable, which is
what lets the postcondition name them: #vm[`e4`] is what #vi[`b`] names after
the call.

The inhale adds the postcondition's footprint to the caller's heap, bound
#vm[`with fresh`], so each slot comes back as a value of its own, constrained by
the boolean the inhale then assumes. It relates to what the caller's heap held
before the call exactly where consolidation merges the two chunks
(#pararef(<para:impl-consolidation>, [Consolidation])).

The order of the two instructions matters. Because the exhale runs first,
permission the callee demands leaves the caller's heap before the postcondition
puts anything back, so the caller ends holding what the precondition left behind
plus what the postcondition returns.

=== Comparison with Silicon

Silicon runs its produce and consume rules over the assertion the programmer
wrote at every use @silicon[Section 3.3], and well-definedness there is a side
effect of evaluating an expression rather than a pass of its own
@silicon[Section 3.5]. Every use therefore re-poses the obligations the
declaration's well-definedness check already settled: positive permission for
each heap read, a non-zero divisor, and the precondition of each function
applied. Helium discharges those once, when the resource is verified and compiled
to recipes (#pararef(<para:impl-slot-recipes>, [Slots and recipes])), so a method
with $n$ call sites raises them once rather than $n + 1$ times. The footprint
walk itself costs the same in both, since each use touches every slot either way.
