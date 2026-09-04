#import "../../macros.typ": *

== Methods <sec:impl-methods>

A method's contract lowers to a pair of resources, and Helium verifies the body
against them once. This section describes those two resources, the frame Helium
puts around a body, and the call site. The bodies here are straight-line, and
@sec:impl-cfg adds branches and loops.

#para[Method contracts] A #vi[`requires`] clause is a heap fragment together
with an assertion about it, which is the pair @sec:impl-predicates already has a
construct for, so the translator lowers it to a resource over the method's
parameters. An #vi[`ensures`] clause lowers to a resource as well, carrying one
parameter the method's signature does not have: a postcondition may name the
state at entry, so the resource takes a snapshot of the pre-state and widens it
back into a heap with its first instruction. @lst:method-contract is
#vi[`bump`] with both clauses.

#lowering(
  caption: [A contract as two resources. The postcondition's trailing parameter is the precondition's snapshot, and #vm[`e3`] and #vm[`e4`] are the same read at two different heaps.],
  label: "lst:method-contract",
  placement: auto,
  stacked: true,
)[```viper
field val: Int

method bump(c: Ref)
  requires acc(c.val, write)
  ensures acc(c.val, write)
       && c.val == old(c.val) + 1
```][```vmir
resource bump#requires(e0: Ref) {
  e1: &[val] Int @ 1/1 := val(e0)
  h0 := empty + e1 @ 1/1 with self
  result: (h0, true)
}

resource bump#ensures(e0: Ref, e1: bump#requires@snap) {
  h0 := empty inhale bump#requires(e0) @ 1/1 with e1
  e2: &[val] Int @ 1/1 := val(e0)
  h1 := empty + e2 @ 1/1 with self
  e3: Int  := *[h1] e2
  e4: Int  := *[h0] e2
  e5: Int  := e4 +i 1
  e6: Bool := e3 == e5
  result: (h1, e6)
}
```]

A postcondition's parameters are the method's parameters, then its return
variables, and last the precondition's snapshot. The opening inhale rebuilds the
pre-state at #vm[`1/1`], so every chunk returns at the amount the precondition
named for it, and its boolean makes the invariants the precondition establishes
available to the rest of the body.

#vm[`e3`] and #vm[`e4`] are the same read at the same address, separated by the
heap each names: #vm[`e3`] takes #vi[`c.val`] from the postcondition's own
delta, #vm[`e4`] takes #vi[`old(c.val)`] from the pre-state. Since heaps are
values, the ordinary dereference instruction executes an #vi[`old`] expression,
and a #vi[`label`] inside a body is recorded the same way, as the heap the
labelled point produced. A postcondition reading past the precondition's
footprint fails to discharge at #vm[`h0`], exactly as an unframed read would.

Both contract resources are verified at their declarations, by the rules
@sec:impl-predicates gives: the precondition first, then the postcondition
against the pre-state the precondition's inhale rebuilds.

#para[Verifying a method] Helium frames a body in three phases: a prologue that
builds the entry heap out of the precondition, the body itself, and an exit that
checks the postcondition against what the body left. @lst:method-full is
#vi[`bump`] with a return variable, inside that frame.

#lowering(
  caption: [A complete method: the prologue builds the entry heap, the body
    runs, and the exit checks the contract against what the body left.],
  label: "lst:method-full",
  placement: auto,
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
  e5: Int := e4 +i 1
  h1 := h0 assign e3 with e5
  //@
  _, _ := h1 exhale
          bump#ensures(e0, e4, e2)
          @ 1/1
}
```]

A body starts from #vm[`empty`]. The prologue mints a fresh value for each
parameter and each return variable, then a fresh handle for the precondition's
snapshot, and inhales the precondition against that empty heap. Binding the
inhale to the handle carries the pre-state to the exit. The body is made up of
the usual VMIR instructions, each treating #vm[`h0`] as it would any other heap.

The exit exhales the postcondition over the method's parameters, the final
values of the return variables, and the precondition's snapshot. It raises the
sufficiency obligation of a subtraction (@sec:impl-heap) at each slot of the
postcondition's footprint and asserts its boolean.

#para[Calling a method] A call lowers to a pair of resource operations on the
caller's heap, with the callee's contract standing in for its body.
@lst:method-call calls the method of @lst:method-full.

#lowering(
  caption: [A call is an exhale of the callee's precondition and an inhale of its postcondition, with the return values minted between the two.],
  label: "lst:method-call",
  placement: auto,
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

The exhale takes the precondition's footprint out of the caller's heap and
yields #vm[`e3`], the snapshot recording what that heap held at each of the
precondition's slots, which the postcondition then takes as its trailing
argument. Between the two instructions the call mints a fresh value for each
return variable, so #vi[`b`] names #vm[`e4`] after the call.

The inhale is bound #vm[`with fresh`], so each slot comes back as a value of its
own, constrained by the boolean the inhale then assumes. It relates to what the
caller's heap held before the call exactly where the add merges the two chunks
(@sec:impl-heap).

#para[Comparison with Silicon] A contract is walked once however often it is
used, so a method with $n$ call sites raises the well-definedness obligations of
its clauses once rather than $n + 1$ times (@sec:impl-predicates). The footprint
walk itself costs the same in both verifiers, since each use touches every slot
either way.
