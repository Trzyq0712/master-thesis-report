#import "../../macros.typ": *

== Interacting with the Heap <sec:impl-heap-interaction>

#todo[
  - `inhale` / `exhale` / `fold` / `unfold` / `unfolding`. The corpus counts
    make the case that this is the hot path: `exhale` and `unfold` dominate.
  - Beat 3 is the substance here: how a `fold`/`unfold` pair relates the
    snapshots before and after, and why two reads of an unchanged field are
    provably the same value.
  - Permission amounts and Proving sufficiency moved here from @sec:impl-heap,
    which now says only what a chunk *is*. Both need predicates already
    explained: the first turns on a resource body's guard, the second on what a
    demand looks like. Decide where they sit among the beats above — amounts
    before inhale and exhale, sufficiency after, is the obvious reading.
  - A wildcard amount is gated structurally rather than arithmetically, since
    there is no term to multiply out. Wildcards are not introduced yet, so
    Permission amounts states the arithmetic case only; check it still reads
    honestly once they arrive.

  #para[Run-in headings] Inhale and exhale / Permission amounts / Folding and
  unfolding / Unfolding in expressions / Proving sufficiency / What we record
]

#lowering(caption: [Allocating a reference, writing a field, and reading it back.], label: "lst:field-access")[```viper
var x: Ref := new(f)
//@
x.f := 42
//@
assert x.f > 0
```][```vmir
e0: Ref := fresh
e1: &[f] Int @ 1/1 := f(e0)
h0 := empty + acc(e1, 1/1)
//@
h1 := h0 assign(e1, 42)
//@
e2: Int := *[h1] e1
e3: Bool := e2 > 0
assert e3
```]

#para[Permission amounts] A permission amount is a _term_, not a literal.
Because a chunk's amount is an e-class like its location and its value, it may
be an arbitrary expression, and this is what lets the heap stay flat. A
resource body may state a conditional footprint:

#lowering(caption: [A guarded footprint becomes an unconditional chunk holding a conditional amount.], label: "lst:guarded-footprint")[```viper
predicate P(x: Ref, p: Perm) {
  p > 0 ==> acc(x.f, p)
}
```][```vmir
e1: Bool := e0 > 0
e2: Real := e1 ? e0 : 0/1
h0 := empty + acc(f(x), e2)
```]

The chunk is added unconditionally; the guard is pushed into the amount, which
becomes #vm[`p > 0 ? p : 0`]. Nothing about the _shape_ of the heap depends on
the condition: the same partitions exist and the same chunks sit in them
whichever way #vi[`p > 0`] goes, and only the arithmetic differs. The verifier
therefore never has to case-split to find out what it is holding, and a
conditional footprint costs it a ternary rather than a second heap.

#todo[
  Proving sufficiency.

  Say here that this is why the sufficiency check has to be an obligation on an
  arithmetic term rather than a lookup: the amount found may be a ternary, so
  "held $>=$ demanded" is discharged in the e-graph, not by comparing literals.
]
