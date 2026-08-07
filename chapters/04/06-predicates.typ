#import "../../macros.typ": *

== Predicates <sec:impl-predicates>

Viper's second declaration form is the one with something inside it, and the
instructions of @sec:impl-heap-interaction are what that something is made of. A
predicate declaration lowers to a #vm[`resource`], whose body is not an assertion
in Viper's sense but ordinary straight-line VMIR.

#lowering(caption: [A predicate becomes a resource whose body yields a heap and a value.], label: "lst:predicate-decl")[```viper
predicate gt(x: Ref, b: Int) {
  acc(x.f) && x.f > b
}
```][```vmir
resource gt(e0: Ref, e1: Int) {
  e2: &[f] Int @ 1/1 := f(e0)
  h0 := empty + acc(e2, 1/1)
  e3: Int := *[h0] e2
  e4: Bool := e3 > e1
  result: (h0, e4)
}
```]

Every line of it is now familiar. The location comes from the field's own location
function (@sec:impl-fields), the #vi[`acc`] is one heap add, and the read of
#vi[`x.f`] in the second conjunct dereferences #vm[`h0`] — the heap that add
produced, and not some ambient state. A predicate body introduces no new way of
touching the heap; the chain simply starts from #vm[`empty`] rather than from a
caller's state, because a body describes a footprint in isolation and not an
update to whatever the caller happened to hold.

That the body threads a heap through itself is also what makes its second conjunct
mean anything. #vi[`x.f > b`] is a claim about the value at a location the first
conjunct just granted permission to, and lowering the two in order is what puts
that value in scope for it.

#para[Resources] The last line is what the name #vm[`resource`] refers to. A body
evaluates to a _pair_: a heap and a value. The heap is a delta — what holding this
adds, here one chunk at #vm[`f(e0)`]. The value is an assertion _about_ that delta:
a pure condition claimed to hold of what the delta contains, here that the field
read out of it exceeds #vm[`e1`]. An all-permission body has nothing to claim and
its value is simply #vm[`true`].

The word carries a narrower meaning here than in Viper, and the two should not be
run together. Viper calls any permission-carrying thing a resource, and that sense
is spelled _location_ in VMIR (@sec:impl-heap): a field location and a predicate
location are resources in Viper's sense and are treated alike. A VMIR
#vm[`resource`] is the _declaration form_ — a named, parameterised
delta-plus-assertion pair. A predicate is the first thing that lowers to one, but
not the last: a method's precondition and postcondition and a function's
precondition all become resources too (@sec:impl-cfg), which is why the construct
is worth separating from the predicate that motivated it.

#para[Derived members] Naming a bundle costs two members the source program never
writes. Every resource brings into being a snapshot type and a location function.

#vmir[```vmir
adt gt@snap { #0(Option<Int>) }

function gt(e0: Ref, e1: Int): &[gt] gt@snap @ *
```]

An #vm[`@`] in a name marks a member as derived rather than declared, which is why
the snapshot type is #vm[`gt@snap`] while the location function is plain
#vm[`gt`]: the latter is the resource's own name, exactly as a field's location
function carries the field's name.

That location function is @lst:field-decl at the predicate's arity, and its
components are fixed the same way. The group is the predicate's name, so each
predicate owns a partition. The stored type is the derived snapshot type. The
bound is #vm[`*`]: nothing stops a program from holding arbitrarily many instances
of one predicate, and a partition of unbounded kind is the one that receives
neither of the axioms of @sec:impl-heap.

#para[Snapshots] The snapshot is what is stored at a predicate location — what an
instance remembers of the delta it folded away. Its type is read off the body
syntactically: every heap add in the body contributes one slot, in order, typed by
what is stored at the location added.

The slots are #vm[`Option`]-typed because @lst:guarded-add made an add
unconditional and put the condition in the amount. Presence is therefore a question
about the amount rather than about the instruction, and the slot is packed as
#vm[`0 < p ? Some(v) : None`] — present exactly where positive permission was
contributed. Where the add was unconditional the discriminant folds to #vm[`true`]
and the projection reductions peel the slot back to the value, so an unconditional
footprint pays nothing for the wrapper.

#para[Inhaling and exhaling an instance] An #vi[`inhale`] of a predicate instance
is not a run of adds the way an #vi[`inhale`] of a conjunction of #vi[`acc`]s is.
It is a single instruction carrying the whole bundle: the delta is applied and the
assertion _assumed_ on the way in, demanded and _asserted_ on the way out. Both
directions scale the delta by a permission amount, and both yield the instance's
snapshot alongside the new heap.

#lowering(caption: [A predicate instance is inhaled and exhaled as one instruction.], label: "lst:resource-inhale")[```viper
inhale acc(gt(x, b))
//@
exhale acc(gt(x, b))
```][```vmir
h1, e2 := h0 inhale gt(e0, e1) 1/1
//@
h2, e3 := h1 exhale gt(e0, e1) 1/1
```]

The asymmetry between the two is where the obligation sits. An inhale is total: it
can always be performed, and what it contributes is guarded by the path condition
reaching it, so a conditional inhale cannot leak its fact past the branch. An
exhale carries a side condition — the permission has to be there to be taken —
discharged under that same path condition.

Neither instruction interprets the body at the site it is used. The chunk it adds
sits at the predicate's own location, holds an opaque snapshot, and says nothing
about the fields the body would have named. That is exactly the point of a
predicate, and it is also what the next paragraph has to undo.

#todo[
  Folding and unfolding. Beat 3 of this section and the substance of the chapter's
  hot path — the corpus counts have `unfold` second only to `exhale`.

  - A #vi[`fold`] consumes the chunks the delta names and builds the snapshot out
    of *their* values, where an inhale mints an opaque one. An #vi[`unfold`] runs
    the exchange the other way and recovers the fields from the snapshot.
  - The pair is what makes the round trip exact: why two reads of an unchanged
    field across a `fold`/`unfold` are provably the same value.
  - #vi[`unfolding`] in expressions.
]

#para[Abstract predicates] A predicate declared without a body has no delta to read
a snapshot type off, so it does not get one. The snapshot type is an opaque domain
instead of an #vm[`adt`], and values of it are only ever passed around, never
constructed or projected. Nothing else changes: there is still a derived location
function at the same arity, into a partition of the same kind, and an instance is
inhaled and exhaled by @lst:resource-inhale like any other. What is lost is only
the relation to a footprint — with no pair to split there is nothing to fold or
unfold, so such an instance can be held, given away and taken back, and nothing
more.

Prusti's #vi[`p_Param`], the one abstract predicate in the worked example, is
exactly this case: a value of a generic type parameter whose representation is not
known where the encoding is generated, and about which the verifier is therefore
expected to conclude nothing.

#note[
  *Listing notation.* The listings in these three sections use
  #vm[`acc(e1, 1/1)`] and #vm[`assign(e1, 42)`], following the rest of the
  chapter. A real translation dump prints these without the punctuation —
  #vm[`h0 + acc e1 1/1`], #vm[`h0 assign e1 42`] — while #vm[`result: (h0, e4)`]
  and the inhale and exhale forms are verbatim. Worth settling in one pass over
  the chapter rather than per section.
]
