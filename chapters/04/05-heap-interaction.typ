#import "../../macros.typ": *

== Interacting with the Heap <sec:impl-heap-interaction>

#todo[
  This section owns the *operations*; @sec:impl-fields and @sec:impl-predicates
  own the declarations they act on. Everything here is shown on a field, because
  a field is the one location that needs no explanation of its own — but nothing
  in it is field-specific.

  The corpus counts belong in the opening: `exhale` and `unfold` dominate, which
  is what makes this the hot path. `fold` / `unfold` / `unfolding` are deferred
  to @sec:impl-predicates, since they relate an instance to a body that does not
  exist yet at this point in the chapter.

  A wildcard amount is gated structurally rather than arithmetically, since there
  is no term to multiply out. Wildcards are not introduced yet, so
  #pararef(<para:impl-amounts>, [Permission amounts]) states the arithmetic case
  only; check it still reads honestly once they arrive.

  #para[Run-in headings] Threading the heap / Adding and subtracting permission /
  Permission amounts / Reading and writing / Proving sufficiency / What we record
]

#para[Threading the heap] The symbolic heap of @sec:impl-heap is not a mutable
structure the verifier updates in place. It is a value like any other, named by a
temporary, and instructions relate to it in one of two ways that the notation
keeps apart.

A _heap-producing_ instruction takes a heap and yields a new one, and is written
with the new heap on the left. The add and subtract below are of this kind, as are
an assignment and a fold. Chained together, these are what a body's state
consists of: each such statement yields the next link, and the heap in hand at any
point is whichever temporary the chain has reached.

A _heap-dependent_ instruction does not extend the chain. It reads one link of it
and produces an ordinary value, and it names the link it reads in brackets:
#vm[`*[h] e1`] is the value stored at #vm[`e1`] in the heap #vm[`h`], and
#vm[`perm[h] e1`] is how much permission #vm[`h`] holds there. The brackets are
the marker to read for — a heap on the left of the assignment means a state was
produced, a heap in brackets means one was consulted.

Every chain begins at #vm[`empty`], the heap that holds nothing. A method body
starts there and its first links are the inhale of its precondition, so the state
a body works in is built rather than assumed; a resource body (@sec:impl-predicates)
starts there too, which is what makes it describe a footprint in isolation rather
than an update to whatever a caller held.

Naming the state is what lets an operation say _which_ state it is about. A read
names the heap it reads from, so two reads of one location in two heaps are two
different terms, and two reads in one heap are literally the same term — the same
e-class, with nothing to prove. Framing is thereby a question about which
temporary an instruction mentions, rather than an argument to be made about
separation.

#para[Adding and subtracting permission] Permission moves by one instruction,
which combines a base heap with a single chunk in one of two directions:

$ h' := h #h(0.35em) plus.minus #h(0.35em) "acc"(ell, p) $

Adding grows the state by permission $p$ at location $ell$; subtracting takes it
away. An #vi[`inhale`] walks an assertion left to right and adds what it names, an
#vi[`exhale`] walks it and subtracts, and over an #vi[`acc`] each is exactly one
of the two, with the fraction carried across unchanged.

#lowering(caption: [Inhale and exhale of an `acc` are one heap add and one heap subtract.], label: "lst:field-acc")[```viper
inhale acc(x.f)
//@
exhale acc(x.f, 1/2)
```][```vmir
e1: &[f] Int @ 1/1 := f(e0)
h1 := h0 + acc(e1, 1/1)
//@
h2 := h1 - acc(e1, 1/2)
```]

Here #vm[`h0`] is whatever link the chain had reached when the #vi[`inhale`] was
executed — the fragment sits inside a body rather than opening one, so it extends
a state instead of starting from #vm[`empty`].

Both are pure heap accounting: neither assumes nor asserts anything. Note that the
exhale of a half leaves the location's own bound untouched — the #vm[`1/1`] in the
type is what a chunk of this kind may hold, not what this chunk does hold, and
after the subtract that is #vm[`1/2`]. The obligation the subtract carries, that
enough was held to take it, is a side condition on the instruction rather than
part of it.

A conjunction of #vi[`acc`]s is a run of these instructions threading one heap into
the next, which is the first place the chain of the previous paragraph does visible
work: an assertion is not applied to the state all at once, it is applied one chunk
at a time, and each link is a state the verifier can name.

#para[Permission amounts] <para:impl-amounts> The amount $p$ is a _term_, not a
literal. A chunk's amount is an e-class exactly as its location and its value are,
so it may be an arbitrary expression, and this is what keeps an add unconditional
even where the access is not.

#lowering(caption: [A guarded access gates the amount, not the instruction.], label: "lst:guarded-add")[```viper
inhale b ==> acc(x.f)
```][```vmir
e2: &[f] Int @ 1/1 := f(e0)
e3: Real := e1 ? 1/1 : 0/1
h1 := h0 + acc(e2, e3)
```]

With #vm[`e0`] the receiver and #vm[`e1`] the guard, the chunk is added
unconditionally and the guard is pushed into the amount. Nothing about the _shape_
of the heap then depends on the condition: the same partitions exist and the same
chunks sit in them whichever way #vi[`b`] goes, and only the arithmetic differs.
The verifier never case-splits to find out what it is holding, and a guarded access
costs it a ternary rather than a second heap. What it costs instead is that a later
demand at #vm[`e2`] is an obligation on an arithmetic term rather than a comparison
of literals.

#para[Reading and writing] A field access does not mean one thing. Viper writes
#vi[`x.f`] in three positions and they lower differently, because a location and
the value at a location are different things. Inside an #vi[`acc`] it denotes the
location itself and nothing more, which is what the instructions above consume. As
the target of an assignment it denotes the location whose value is to be replaced.
In an expression it denotes the value — and a value has to be read out of some
particular heap.

#lowering(caption: [Allocating a reference, writing a field, and reading it back.], label: "lst:field-access")[```viper
var x: Ref := new(f)
//@
x.f := 42
//@
assert x.f > 0
```][```vmir
e0: Ref := fresh
e1: &[f] Int @ 1/1 := f(e0)
h1 := empty + acc(e1, 1/1)
//@
h2 := h1 assign(e1, 42)
//@
e2: Int := *[h2] e1
e3: Bool := e2 > 0
assert e3
```]

The three positions share their first move — every one of them calls #vm[`f`] on
the receiver — and differ only in the instruction applied to the result. The
allocation adds permission at it, opening the chain at #vm[`empty`] since the
fragment is a body's first statement; the assignment replaces the value at it,
producing #vm[`h2`]; and the read consults #vm[`h2`] without producing anything.
Because the read names its heap, #vm[`e2`] is the value #vm[`h2`] holds, and
#vm[`h2`] is by construction the heap the assignment produced, so the #vi[`assert`]
reaches what was just written with no framing argument. Reading from #vm[`h1`]
would have been a different term, and reading a location the assignment never
touched is how a read is framed at all.

The receiver #vm[`e0`] is fresh only in the sense that nothing has been assumed
about it: a new e-class, not one asserted distinct from any other. No allocation
axiom is needed either — the full permission the allocation hands out is already
inconsistent with any other chunk of the group sitting at the same address.

#todo[
  Proving sufficiency.

  Every demand raised above lands here: the subtract needs enough permission to
  take, the write needs #vm[`1/1`], the read needs some. Open by recalling that a
  chunk's amount may be a ternary
  (#pararef(<para:impl-amounts>, [Permission amounts])), which is why the check is
  an obligation on an arithmetic term rather than a lookup — "held $>=$ demanded"
  is discharged in the e-graph, not by comparing literals.
]
