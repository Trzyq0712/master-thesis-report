#import "../../macros.typ": *
#import "../../figures/location-anatomy.typ": location-anatomy
#import "../../figures/heap-partitions.typ": heap-partitions
#import "../../figures/consolidation.typ": consolidation

== The Heap in VMIR and Helium <sec:impl-heap>

So far, Helium has only executed streams of value-only instructions. To
verify a real Viper program it also has to reason about the heap.
@lst:heap-first-inhale takes permission to one field, states a fact about it,
and asserts a different one back.

#viper(
  caption: [Taking permission to a field, assuming a fact about it, and checking one.],
  label: "lst:heap-first-inhale",
)[```viper
field f: Int

method client(x: Ref) {
  inhale acc(x.f, write) && x.f == 42
  assert x.f > 0
}
```]

#vi[`x.f`] appears twice above, in two different roles: once inside
#vi[`acc`], naming what permission is taken to, and once as an ordinary
expression, naming the value stored there. VMIR removes that dual use by
making a location a value of its own. #vi[`x.f`] becomes #vm[`f(x)`], a
location that permission can be taken to, read from and written to,
whichever the instruction asks for. @lst:heap-first-inhale-vmir shows more precisely how the above Viper code is lowered to VMIR.

#vmir(
  caption: [Field access becomes a location dereference, and the heap is threaded explicitly through every operation on it.],
  label: "lst:heap-first-inhale-vmir",
)[```vmir
function f(e0: Ref): &Int

method client {
  e0: Ref := fresh         // x
  e1: &Int := f(e0)        // address of x.f
  h0 := empty + e1 @ 1/1 with fresh
  e2: Int := *[h0] e1      // read the value at e1 in h0
  e3: Bool := e2 == 42     // x.f == 42
  assume e3
  e4: Int := *[h0] e1      // read the value at e1 in h0 again
  e5: Bool := e4 > 0       // x.f > 0
  assert e5
}
```]

The field declaration becomes an ordinary function,
#vm[`function f(e0: Ref): &Int`]: given a #vi[`Ref`], it returns a location
type holding an #vi[`Int`].

The body itself lowers to a sequence of instructions. The #vi[`inhale`]
becomes #vm[`h0 := empty + e1 @ 1/1`] on line 6, the first heap operation VMIR
has: it takes a prior heap, #vm[`empty`] here since this is the body's first
statement, and adds a location to it, #vm[`e1`], with an amount, #vm[`1/1`],
and a value named after #vi[`with`], here a fresh symbolic one. Line 7 then
reads that value back out with the dereference operator #vm[`*`], which takes
a location and a heap to consult, #vm[`e1`] and #vm[`h0`]. The #vi[`assume`]
then states the fact promised by the #vi[`inhale`]. The rest of the method
repeats the read against the same #vm[`h0`] and checks the assertion.

@lst:heap-first-inhale-vmir shows one more thing worth naming: heaps are
explicit and immutable. Every heap operation produces a new one, and a
heap-dependent instruction has to name which heap it means, #vm[`h0`] both
times here, since nothing produced a later one. Viper's heap, by contrast, is
implicit and threaded for the program: an operation acts on whatever heap is
current, and reaching an earlier one takes an explicit #vi[`old`] expression.

#para[Location types] The example above has already introduced the idea of
locations as values. We formalise it here.

@lst:heap-first-inhale-vmir also leaves out two parts of a location type:
its _group_ and its _permission bound_. Both exist because of Viper's
aliasing rules. Two fields coming from two distinct field declarations may
never alias, even when they store the same type, so a location type has to
encode which declaration it came from: this is the _group_. The _permission
bound_ states how much permission a location may hold at once. A field's
bound is always #vi[`write`]; a predicate's bound is unconstrained by
default, since Viper lets a program hold an arbitrary amount of a folded
predicate. @fig:location-anatomy shows the complete representation of a
location type.

#figure(
  location-anatomy,
  caption: [A location belonging to group #vm[`f`], storing an integer, with at most #vm[`1/1`] permission amount.],
) <fig:location-anatomy>

Because a location type is fully self-defining, it can stand for a field or a
predicate alike: to the verifier, a folded predicate is just another location
type, one that stores the predicate's footprint instead of a plain value.
Locations can also be computed over directly, since every aliasing check or
permission-bound assumption only needs information already present at that
point in the program.

#para[Fields in VMIR] Fields are the first of the location producers.
@lst:field-decl states what a #vi[`field f: Int`] declaration becomes in
VMIR.

#lowering(
  caption: [Field declaration in Viper becomes an uninterpreted function that maps the receiver to a location.],
  label: "lst:field-decl",
)[```viper
field f: Int
```][```vmir
function f(e0: Ref): &[f] Int @ 1/1
```]

VMIR diverges from verifiers like Silicon in one respect: it does not assume
field mappings are injective. Silicon's reasoning about fields relies on
injectivity holding; VMIR does not require it by default, so learning that
two locations are equal ($f(x) = f(y)$) does not by itself imply that the
receivers are ($x = y$). A frontend that wants injectivity can still declare
it, by exposing an inverse function alongside a postcondition stating the
round trip (@lst:field-inv).

#vmir(caption: [Injectivity of location functions can be encoded if required.], label: "lst:field-inv")[```vmir
function f(e0: Ref): &[f] Int @ 1/1
  ensures e0 == f_inv(result)

function f_inv(e0: &[f] Int @ 1/1): Ref
```]

=== Heap representation in Helium

A field becomes a location type; a program takes permission to it. What
remains is how Helium represents the heap those locations index into.

#para[Partitioning] A chunk is a triple of symbolic values: a location, a
permission amount and a value. Helium does not keep chunks in one flat set.
It splits them into _partitions_, one per location kind — group, stored type
and permission bound taken together (@fig:location-anatomy). A chunk lives in
exactly the partition its location's type names. Within a partition, Helium
indexes chunks by location: the e-class the location resolves to in the
e-graph.

A lookup goes in two steps, shown in @fig:heap-partitions: pick the partition
from the location kind, then find the chunk by e-class inside it. This makes
a lookup cheaper than Silicon's, which keeps every chunk in one flat list and
scans it for a match.

#figure(
  heap-partitions,
  caption: [The symbolic heap as boxes, one per location kind. A chunk lives
    in exactly one partition; #vi[`f(x)`] and #vi[`f(y)`] land in different partitions
    despite sharing a stored type and bound; the predicate box is the
    #vm[`*`]-bounded one, dashed.],
) <fig:heap-partitions>

#para[Consolidation] <para:impl-consolidation> Adding a chunk first checks
whether its partition already holds one at the same location. If it does,
Helium creates no new chunk: it folds the two into one, summing their
amounts. It takes the value from whichever side holds positive permission;
if both do, it assumes them equal rather than asserting it. For two chunks
with amounts and values $p_0, v_0$ and $p_1, v_1$, folding produces

$ p' := p_0 + p_1, quad v' := ternary(p_0 > 0, v_0, v_1) $

$ p_0 > 0 and p_1 > 0 ==> v_0 = v_1 " (assumed)" $

Sometimes Helium learns two locations are equal only after their chunks are
already on the heap. @lst:heap-consolidate takes half permission to
#vi[`x.f`] and half to #vi[`y.f`], learns #vi[`x == y`], then exhales the
combined whole.

#viper(
  caption: [Two chunks added separately, found equal only afterward.],
  label: "lst:heap-consolidate",
)[```viper
inhale acc(x.f, 1/2) && acc(y.f, 1/2)
assume x == y
exhale acc(x.f, 1/1)
```]

The greedy lookup for the #vi[`exhale`] fails: it finds only the #vm[`1/2`]
chunk at #vm[`f(x)`]'s own e-class, since the #vi[`assume`] merged #vi[`x`]
and #vi[`y`]'s e-classes without touching the heap. On failure, Helium
re-keys the partition. It asks the e-graph for each chunk's canonical
e-class and rebuilds the partition around those, folding the two chunks by
the same rule as an ordinary add. The retried lookup then finds one chunk
holding #vm[`1/1`], as required.

Re-keying costs one linear pass over the partition, and no second round is
needed. Congruence, an invariant of the e-graph, already closed the equality
before re-keying ran — nothing outside the heap needs to track it.

#para[Location axioms] <para:impl-location-axioms> For a location kind
bounded by $b$, Helium also emits two axioms whenever a chunk is added or
re-keyed:

- *Permission bound:* a chunk's own amount does not exceed the bound.
  $ p <= b $
- *Non-aliasing:* two chunks in the same partition, holding amounts $p, p'$ at
  locations $ell, ell'$, cannot together exceed the bound once their
  locations are equal.
  $ ell = ell' ==> p + p' <= b $

A field's bound is always #vm[`1/1`]. Take two full chunks, #vm[`f(x)`] and
#vm[`f(y)`], each holding #vm[`1/1`]: were they the same location, the
non-aliasing axiom would force $1 + 1 <= 1$, a contradiction, so they cannot
be. #vi[`x != y`] follows — needing nothing about #vi[`f`] beyond congruence;
no injectivity is assumed.

#para[Comparison with Silicon] Silicon reaches similar guarantees by a
different route. It consolidates chunks with a fixpoint algorithm: after each
new equality, it repeatedly asks the SMT solver whether pairs of receivers
are equal. This is cubic in the number of chunks in the worst case
@silicon[Section 3.4.2], so Silicon schedules consolidation rather than
running it after every operation. Helium instead keeps every location
canonicalised inside the e-graph, so a lookup only ever needs the one linear
pass described above (#pararef(<para:impl-consolidation>, [Consolidation])).

The two verifiers also place the non-aliasing axiom differently. Silicon
states it over field receivers, one instance per field:
$x = y ==> p + p' <= b$. Helium states it over locations instead
(#pararef(<para:impl-location-axioms>, [Location axioms])):
$ell = ell' ==> p + p' <= b$, which covers a field and a bounded predicate in
the same form. Stating it over receivers is exactly where Silicon assumes
field mappings are injective, an assumption VMIR does not make by default
(@lst:field-inv).

== Heap operations in VMIR
This section has so far only briefly introduced one of the heap operations in @lst:heap-first-inhale-vmir, #vm[`empty + e1 @ 1/1 with fresh`], without yet specifying concrete semantics. We will now complete the gap, introducing the remaining core heap operations and their semantics.

TODO

#pagebreak()
