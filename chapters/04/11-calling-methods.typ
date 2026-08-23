#import "../../macros.typ": *

== Calling Methods <sec:impl-calls>

A call is not a control-flow event. Viper's methods are opaque at their boundary
— a caller may use only what the contract says — so a call site never needs the
callee's body, and the verifier never looks at one. What a call _is_ is a
transaction against the heap: permission and facts leave at the precondition and
come back at the postcondition. Everything needed to execute one has already been
built.

A method's #vi[`requires`] and #vi[`ensures`] are
lowered to resources, named #vm[`m#requires`] and #vm[`m#ensures`]. This is the
same construct a predicate becomes (@sec:impl-predicates), and using it here is
the point: a contract is a heap delta plus a boolean claimed of it, which is
exactly what a resource is. One mechanism therefore covers predicates, method
contracts, and — in @sec:impl-functions — function preconditions, and none of the
operations of @sec:impl-heap-interaction had to learn what kind of thing they were
applied to.

The precondition resource is self-framed: its body accumulates from #vm[`empty`]
and reads only what it has just granted itself. The postcondition is the one
construct that is not, and the next paragraph is about that.

A call is an exhale of the precondition followed by an inhale of
the postcondition, with fresh values created in between for whatever the callee
returns. The guiding example's functions call no other function of the crate, so
every call in its encoding is to one of the methods Prusti generates —
@lst:call-site is one, and #vi[`account_deposit`] makes it twice per block that
touches the borrow.

#lowering(caption: [A call is an exhale and an inhale of the callee's contracts.], label: "lst:call-site", target-lang: "lvmir")[```viper
method make_concrete_Account(self: Ref)
  requires acc(own_Param(self,
    Account_type()), write)
  ensures acc(own_Account(self), write)
  ensures old(snap_Param(self,
      Account_type()))
    == generic_Account(
      snap_Account(self))

// ... in account_deposit:
make_concrete_Account(_4p)
```][```lvmir
resource make_concrete_Account#requires(
    e0: Ref) {
  h0 := empty
        + own_Param@loc(e0,
            Account_type()) @ 1/1
        with self
  result: (h0, true)
}

h1, e5 := h0 exhale
      make_concrete_Account#requires(e4)
      @ 1/1
h2 := h1 inhale
      make_concrete_Account#ensures(e4, e5)
      @ 1/1 with fresh
```]

Prusti passes a callee's results as #vi[`Ref`] parameters rather than through
Viper's #vi[`returns`] clause — the corpus contains no #vi[`returns`] at all — so
the two lines above are the whole of a call in a Prusti encoding. Where a
#vi[`returns`] does appear, the values it names are created fresh between the
exhale and the inhale.

The exhale is where the caller pays: it takes the precondition's footprint out of
the caller's heap, raising the sufficiency obligations of
#pararef(<para:impl-subtract>, [Giving permission back]) as it goes, and asserts
the precondition's boolean. The inhale is where it is paid back, and it is total —
an inhale can always be performed, and what it contributes is guarded by the path
condition reaching it. Nothing about the callee is known at either end except what
its two contracts say.

The postcondition inhale is bound #vm[`with fresh`], and that is the same
statement made of the footprint rather than of the return value. A postcondition
describes an arbitrary post-state, so what the caller gets back at each of its
slots is havoc — subject only to the boolean the inhale then assumes. Freshness is
supplied here, by the instruction, and not written into the resource
(@sec:impl-predicates): the same resource inhaled against a snapshot already in
hand would instead give back exactly the values that snapshot records, which is
what a function's entry does with its precondition (@sec:impl-functions).

The ordering is what makes the transaction sound rather than merely
symmetric. Because the exhale runs first, permission the callee demands is gone
from the caller's heap before the postcondition adds anything back, so a caller
cannot silently keep a share it has handed over. And because the return values
are created between the two, the postcondition can talk about them.

A postcondition may mention #vi[`old`], and then
it is a claim about two states rather than one. This is where the resource
construct is stretched, and it is worth following because Prusti relies on
#vi[`old`] heavily — it is how every method that mutates through a reference
relates the new value to the previous one.

The mechanism is visible in @lst:call-site: the exhale of the precondition
_yields a value_, #vm[`e5`], alongside the new heap, and that value is passed to
the postcondition as a trailing argument. The value is the precondition's
snapshot — the same snapshot a predicate instance carries, built by the same
footprint walk (@sec:impl-predicates), holding the values the caller's heap had at
each of the precondition's slots at the moment they were taken.

The postcondition resource is declared to be _two-state_: it takes that snapshot
as an extra parameter, and its body opens by widening it back into a heap.

#lvmir(caption: [#vi[`account_deposit`]'s postcondition, with its pre-state reconstructed. The snapshot plumbing on the fourth line is elided.], label: "lst:two-state")[```lvmir
resource account_deposit#ensures(
    e0: Ref, e1: Ref, e2: Ref,
    e3: account_deposit#requires@snap) {
  h0 := empty inhale
        account_deposit#requires(e0, e1, e2)
        @ wildcard with e3
  h1 := empty + own_Unit@loc(e0) @ 1/1 with self
  e4: Ref := snap_RefMut[h0](e1).RefMut_0
  h2 := h1 + own_Param@loc(e4, Account_type()) @ 1/1
        with self
  result: (h2, true)
}
```]

There are two chains of heaps in the body and no ambiguity about which is which.
#vm[`h1`] and #vm[`h2`] are the delta the postcondition grants — what the caller
gets back — and #vm[`h0`] is the reconstructed pre-state, which grants nothing and
exists only to be read from. The source clause is
#vi[`acc(own_Param(old(snap_RefMut(_1p, ..)).RefMut_0, ..), write)`],
and every part of it is on one of the two sides: the #vi[`old`] reads #vm[`h0`],
the #vi[`acc`] adds to #vm[`h2`], and the difference between reading the pre-state
and the post-state is one temporary in the brackets. The widening is the exact
inverse of the snapshot: one chunk per slot of the precondition, at the same
address, holding the value the snapshot recorded there.

It is also not a special instruction. Reconstructing the pre-state is an
#vm[`inhale`] of the precondition resource bound to the snapshot parameter —
the resource operation of @sec:impl-predicates with its bind point pointing at
#vm[`e3`] — and it is character for character the line a heap-dependent function
opens with (@sec:impl-functions). Both want the same thing, which is a heap
standing for a snapshot somebody else took. The permission is #vm[`wildcard`] for
the same reason there: #vm[`h0`] exists to be read from and grants nothing, so it
must not claim an amount.

The two bind points in the body are therefore the two a resource may use, side by
side. #vm[`with e3`] widens a snapshot the resource received; #vm[`with self`]
declares a slot of the resource's own footprint. Neither is #vm[`with fresh`],
which no resource body ever writes — the caller's inhale is where that arrives,
as @lst:call-site shows.

So #vi[`old`] is not a special form the verifier interprets. It is a read from a
different heap, and heaps are values. The same is true inside a method body: an
unlabelled #vi[`old`] reads the heap the method's precondition inhale produced,
and #vi[`label L`] does nothing except give a name to the heap at a block's entry,
which #vi[`old[L]`] then reads. Prusti emits a label before every statement —
24518 of them across the corpus, against 360 #vi[`old`] expressions to read them
— and each costs one name and nothing else.

Two things follow. A two-state resource may never be folded, and its snapshot is
never handed to a program: it has a footprint, and so a slot vector for its adds to
bind against, but there is no single state that vector summarises, since the body
reads a heap it does not own. What a caller does with such a resource is inhale it
and exhale it, and nothing else. And a postcondition can be verified for
well-formedness once, on its own, as any resource is, with its snapshot parameter
an ordinary symbolic value.

A call that cannot be discharged leaves the transaction
half-executed by design: the exhale reports which location it could not take
enough permission from, with the demanded and held amounts as terms, and the
caller's heap up to that point is intact. Nothing about the callee has been
assumed, since nothing about a callee is ever assumed beyond its contract.
