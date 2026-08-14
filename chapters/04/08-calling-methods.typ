#import "../../macros.typ": *

== Calling Methods <sec:impl-calls>

A call is not a control-flow event. Viper's methods are opaque at their boundary
— a caller may use only what the contract says — so a call site never needs the
callee's body, and the verifier never looks at one. What a call _is_ is a
transaction against the heap: permission and facts leave at the precondition and
come back at the postcondition. Everything needed to execute one has already been
built.

#para[Contracts as resources] A method's #vi[`requires`] and #vi[`ensures`] are
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

#para[Call sites] A call is an exhale of the precondition followed by an inhale of
the postcondition, with fresh values minted in between for whatever the callee
returns.

#lowering(caption: [A call is an exhale and an inhale of the callee's contracts.], label: "lst:call-site")[```viper
method inc(x: Ref) returns (r: Int)
  requires acc(x.f)
  ensures acc(x.f) && x.f == old(x.f) + 1

method caller(y: Ref)
  requires acc(y.f)
{
  var n: Int
  n := inc(y)
}
```][```vmir
method caller {
  bb0 <>:
    join:
    e0: Ref := fresh
    e1: caller#requires@snap := fresh
    h0 := empty inhale
          caller#requires(e0) @ 1/1
          with e1
    body:
    e2: Int := fresh
    h1, e3 := h0 exhale
          inc#requires(e0) @ 1/1
    e4: Int := fresh
    h2 := h1 inhale
          inc#ensures(e0, e4, e3) @ 1/1
          with fresh
}
```]

The exhale is where the caller pays: it takes the precondition's footprint out of
the caller's heap, raising the sufficiency obligations of
#pararef(<para:impl-subtract>, [Giving permission back]) as it goes, and asserts
the precondition's boolean. The inhale is where it is paid back, and it is total —
an inhale can always be performed, and what it contributes is guarded by the path
condition reaching it. The result #vm[`e4`] is fresh because the callee is opaque:
nothing is known of it except what the postcondition then assumes.

The postcondition inhale is bound #vm[`with fresh`], and that is the same
statement made of the footprint rather than of the return value. A postcondition
describes an arbitrary post-state, so what the caller gets back at each of its
slots is havoc — subject only to the boolean the inhale then assumes. Freshness is
supplied here, by the instruction, and not written into the resource
(@sec:impl-predicates): the same resource inhaled against a snapshot already in
hand would instead give back exactly the values that snapshot records, which is
what a function's entry does with its precondition (@sec:impl-functions).

The prologue two lines above is a third case. It mints a snapshot _handle_ and
binds the entry inhale to it, rather than writing #vm[`with fresh`], because the
handle is needed twice: the method's own exit exhales its postcondition against
the state the precondition described, and that resource takes the handle as an
argument. Binding rather than havocking is what makes those two mentions the same
value; the slots underneath are no less arbitrary for it, since nothing constrains
the handle either.

The ordering is what makes the transaction sound rather than merely
symmetric. Because the exhale runs first, permission the callee demands is gone
from the caller's heap before the postcondition adds anything back, so a caller
cannot silently keep a share it has handed over. And because the return values
are minted between the two, the postcondition can talk about them.

#para[Two-state postconditions] A postcondition may mention #vi[`old`], and then
it is a claim about two states rather than one. This is where the resource
construct is stretched, and it is worth following because Prusti leans on
#vi[`old`] heavily — it is how every method that mutates through a reference
relates the new value to the previous one.

The mechanism is visible in the listing above: the exhale of the precondition
_yields a value_, #vm[`e3`], alongside the new heap, and that value is passed to
the postcondition as a trailing argument. The value is the precondition's
snapshot — the same snapshot a predicate instance carries, built by the same
footprint walk (@sec:impl-predicates), holding the values the caller's heap had at
each of the precondition's slots at the moment they were taken.

The postcondition resource is declared to be _two-state_: it takes that snapshot
as an extra parameter, and its body opens by widening it back into a heap.

#vmir(caption: [The postcondition resource of `inc`, with its pre-state reconstructed.], label: "lst:two-state")[```vmir
resource inc#ensures(e0: Ref, e1: Int, e2: inc#requires@snap) {
  h0 := empty inhale inc#requires(e0) @ wildcard with e2
  e3: &[f] Int @ 1/1 := f(e0)
  h1 := empty + e3 @ 1/1 with self
  e4: Int := *[h1] e3
  e5: Int := *[h0] e3
  e6: Int := e5 +i 1
  e7: Bool := e4 == e6
  result: (h1, e7)
}
```]

There are two heaps in the body and no ambiguity about which is which. #vm[`h1`]
is the delta the postcondition grants — what the caller gets back — and
#vm[`h0`] is the reconstructed pre-state, which grants nothing and exists only to
be read from. #vi[`x.f`] reads the first, #vi[`old(x.f)`] reads the second, and
the difference between them is one temporary in the brackets. The widening is the
exact inverse of the snapshot: one chunk per slot of the precondition, at the
same address, holding the value the snapshot recorded there.

It is also not a special instruction. Reconstructing the pre-state is an
#vm[`inhale`] of the precondition resource bound to the snapshot parameter —
the resource operation of @sec:impl-predicates with its bind point pointing at
#vm[`e2`] — and it is character for character the line a heap-dependent function
opens with (@sec:impl-functions). Both want the same thing, which is a heap
standing for a snapshot somebody else took. The permission is #vm[`wildcard`] for
the same reason there: #vm[`h0`] exists to be read from and grants nothing, so it
must not claim an amount.

The two bind points in the body are therefore the two a resource may use, side by
side. #vm[`with e2`] widens a snapshot the resource received; #vm[`with self`]
declares a slot of the resource's own footprint. Neither is #vm[`with fresh`],
which no resource body ever writes — the caller's inhale is where that arrives,
as @lst:call-site shows.

So #vi[`old`] is not a special form the verifier interprets. It is a read from a
different heap, and heaps are values. The same is true inside a method body: an
unlabelled #vi[`old`] reads the heap the method's precondition inhale produced,
and #vi[`label L`] does nothing except give a name to the heap at a block's entry,
which #vi[`old[L]`] then reads. Prusti emits a label per statement, and each costs
one name.

Two things follow. A two-state resource may never be folded, and its snapshot is
never handed to a program: it has a footprint, and so a slot vector for its adds to
bind against, but there is no single state that vector summarises, since the body
reads a heap it does not own. What a caller does with such a resource is inhale it
and exhale it, and nothing else. And a postcondition can be verified for
well-formedness once, on its own, as any resource is, with its snapshot parameter
an ordinary symbolic value.

#para[Reborrows and aliasing] The corpus is where this stopped being
straightforward. A #ru[`&mut`] passed into a call is, in Prusti's encoding, a
reborrow: the caller computes a new reference whose address is provably equal to
one it already holds permission for, and the call site then demands permission at
_that_ address. Every failure below is a variant of the same situation — the
demanded location and the held chunk are one location, but not visibly so at the
moment of the lookup — and each turns on the guarded chunks of @sec:impl-cfg. They
are reported here as findings, because the fixes are not obvious and three of the
four were arrived at by first getting them wrong.

#para[Finding: where the retry belongs] A reborrow's address meets the held
chunk's address only after the full rule set has run: it reaches through the
snapshot machinery, and the terminating reductions the verifier runs after a heap
operation are not enough to close the gap. So a lookup that misses has to be able
to saturate and try again.

Where that retry sits is the whole of the finding. Placing it in the lookup, so
that every miss saturates, is the obvious implementation and costs a factor of
36 on one benchmark of the corpus — 1.48 seconds to 53.5 — because a lookup that
misses is _normal_: an assertion may legitimately demand permission at a location
nothing is held at, and the ordinary answer is that the demanded amount is
provably zero. Putting the retry after that check inverts who pays. A miss that
the zero test closes never saturates; only an obligation that would otherwise be
reported as a failure does.

#para[Finding: a reborrow minted under a branch] The second failure is invisible
to the first fix. A reborrow computed _inside_ an arm has an address whose
equality to the held chunk's is a fact of that arm, so it is in the state as a
guarded implication rather than as a merge of two classes. Matching chunks by
canonical e-class cannot see it, and no amount of saturation on the unguarded
state will make it visible, because the equality is not unconditionally true.

The fix is to route the miss through the under-path-condition lookup instead: the
same collect-the-alias-set path
#pararef(<para:impl-pc-sufficiency>, [Sufficiency under a path condition])
describes, which resolves the address gate under the cube rather than in the
ground state. The consume then proceeds with its debit gated by that cube, so
nothing is taken on the path where the addresses are unrelated.

#para[Finding: consecutive reborrows] The third is a soundness bug rather than a
completeness one, and it is what the alias _set_ exists for. Where several held
chunks coincide with the demand under the path condition, the permission at that
location is their sum and nothing less; proving sufficiency against the first
chunk that matches is order-dependent and wrong. The failing case is two
consecutive consumes through a chain of reborrows: the first drains one chunk,
the second matches that same drained chunk, and — if the check looks no further
— sees the permission still sitting in a sibling and succeeds. The location is
then spent twice.

Proving against the sum and distributing the debit across the set closes it. The
case is pinned by a soundness canary in the suite: two full consumes at one
location, reached through nested equalities, which must not both succeed.

#para[Finding: reading a field after a call] The last is a completeness failure
with a cause in a different section entirely. Re-reading a field after a call
should relate the value read to the one the postcondition established, and it did
not: the occurrence of the function relating them stayed opaque, so two reads of
an unchanged field were provably unrelated.

The cause is that a function's body is captured as a recipe and replayed at each
occurrence (@sec:impl-functions), and the replay is gated by a token marking that
the occurrence is a genuine call. Building a recipe prunes whatever the result
does not depend on — and the token's value is read by nothing, so it was pruned.
An occurrence introduced by a method contract therefore arrived without its
token and was never unfolded. The fix belongs where the pruning is, and is stated
there.

#para[What we record] A call that cannot be discharged leaves the transaction
half-executed by design: the exhale reports which location it could not take
enough permission from, with the demanded and held amounts as terms, and the
caller's heap up to that point is intact. Nothing about the callee has been
assumed, since nothing about a callee is ever assumed beyond its contract.
