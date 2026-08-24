#import "../../macros.typ": *
#import "../../figures/location-anatomy.typ": location-anatomy
#import "../../figures/heap-partitions.typ": heap-partitions
#import "../../figures/consolidation.typ": consolidation

== Interacting with the Heap <sec:impl-heap>

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

=== Partitioning the Heap <sec:impl-heap-partitioning>

Add a second field and take permission to it on the same receiver:

#lowering(
  caption: [A second field on the same receiver: two chunks that must never merge.],
  label: "lst:heap-second-field",
  target-lang: "lvmir",
)[```viper
field g: Int
...
inhale acc(x.g, write)
```][```lvmir
h1 := h0 + g(x) @ write
      with fresh
```]

#vm[`h0`] already holds a chunk at #vm[`f(x)`]; #vm[`h1`] now holds one at
#vm[`g(x)`] too, and the two must stay distinct no matter what the verifier
later learns about #vi[`x`]: merging permission to a field with permission to
an unrelated field would be wrong at any receiver. What tells the two chunks
apart is not #vi[`x`], which they share, but the field: #vm[`f(x)`] and
#vm[`g(x)`] carry different groups, hence different location types, hence are
never even compared.

This is why the heap is not one flat set of chunks but a set of _partitions_,
one per location type, group, stored type and bound together, called a
_location kind_. Every chunk lives in exactly the partition its type names,
and an access resolves the partition before it resolves a chunk within it.

#figure(
  pad(y: 0.6em, heap-partitions),
  caption: [The symbolic heap as boxes, one per location kind. A chunk lives
    in exactly one box; #vi[`x.f`] and #vi[`y.g`] land in different boxes
    despite sharing a stored type and bound; the predicate box is the
    #vm[`*`]-bounded one, dashed.],
) <fig:heap-partitions>

Partitioning this way also settles where an aliasing question can even arise:
only between two chunks of one partition. #vm[`f(x)`] and #vm[`g(x)`] are
never compared because they are filed apart before any comparison could
happen; what remains to say is what happens between two chunks that _do_
share a partition.

=== Consolidation <para:impl-consolidation>

Take the first field from two receivers instead of one:

#lowering(
  caption: [Two receivers, one field, split into two chunks — until an equality merges them.],
  label: "lst:heap-consolidate",
  target-lang: "lvmir",
)[```viper
inhale acc(x.f, 1/2) && acc(y.f, 1/2)
assume x == y
```][```lvmir
h1 := h0 + f(x) @ 1/2 with fresh
h2 := h1 + f(y) @ 1/2 with fresh
assume e0 // x == y
```]

#vm[`f(x)`] and #vm[`f(y)`] are two distinct e-classes when #vm[`h2`] is
built, so this is genuinely two chunks in one partition, each holding
#vm[`1/2`]. The #vm[`assume`] then merges those e-classes — and with them, the
two chunks stop being two: they describe the same location, so together they
hold #vm[`1/2 + 1/2`], not two separate halves.

Nothing runs when the #vm[`assume`] executes to make this happen; the merge is
a consequence the verifier only has to notice, and it does so the next time
the partition is consulted. Resolving a location scans the chunks of its
partition, compares canonical e-classes, and folds together any that have
collapsed into one — an amount held twice becomes an amount held once, added.

The permission side of the fold is simple addition. The value side is not:
the two chunks may disagree about what they store, and only a chunk holding
positive permission has any claim to be right. Write $p_0, v_0$ and $p_1, v_1$
for the two amounts and values before the fold. The merged value is picked
asymmetrically,

$ ternary(p_0 > 0, v_0, v_1) $

and agreement between the two is _assumed_ rather than asserted:

$ p_0 > 0 and p_1 > 0 => v_0 = v_1 $

The two cases resolve on their own once stated this way. Where both amounts
are positive, saturation collapses the implication to $v_0 = v_1$ and the two
values merge into one e-class — the asymmetry of the pick becomes moot, since
either side now names the same thing. Where one amount is zero, the
antecedent is false, nothing is assumed of a value nobody holds, and the pick
selects the one genuinely held. Asserting $v_0 = v_1$ outright would be
unsound in that second case and is simply unneeded in the first.

#figure(
  pad(y: 0.6em, consolidation),
  caption: [Consolidation. The merge of two location e-classes _triggers_ the
    fold that follows, rather than being the fold: a separate step, drawn as
    a separate arrow.],
) <fig:consolidation>

Because a partition's chunks are indexed by kind and their locations are
e-classes already sitting in a graph that keeps congruence closed, this scan
is one linear pass over one partition — there is no second round to run once
new equalities arrive, and no partition but this one is even touched.

=== Location Axioms <para:impl-location-axioms>

Take the two receivers again, this time without ever learning they are equal:

#viper(caption: [Distinctness derived without ever assuming injectivity.], label: "lst:field-distinct")[```viper
inhale acc(x.f, write) && acc(y.f, write)
assert x != y
```]

Two full chunks, #vm[`write`] each, land in one partition — and #vm[`f`]'s
bound is #vm[`1/1`], one #vm[`write`]'s worth. If #vm[`f(x)`] and #vm[`f(y)`]
were ever merged, the fold above would leave a chunk holding
#vm[`write + write`], past the bound. So the verifier states, for every
partition bounded by $b$, one axiom over any pair of its chunks holding
$p_0, p_1$ at locations $ell_0, ell_1$:

$ ell_0 = ell_1 => p_0 + p_1 <= b $

and one over each chunk alone, $p <= b$: a chunk whose amount folds past its
bound leaves the state inconsistent, which is exactly right — that path
cannot be reached, so anything asked of it holds.

Under @lst:field-distinct, the pairwise axiom's implication has a false
consequent, #vm[`write + write <= write`], so its antecedent must be false:
#vm[`f(x) != f(y)`]. Narrowing that to the receivers is the contrapositive of
congruence — #vm[`f`] applied to two arguments landed in different e-classes,
so the arguments did, and #vi[`x != y`] follows. Nothing here asked whether
#vm[`f`] is injective; the axiom is stated over locations and their bound; the
receivers are recovered afterward, and only because #vm[`f`] happens to be
unary so there is exactly one argument to blame.

A location's bound is carried in its type rather than derived from whether it
came from a field or a predicate, which is what lets a frontend buy this
axiom for a predicate too: declaring one bounded at #vm[`2/1`] instead of
#vm[`*`] is not documentation, it moves that predicate's partition from no
constraint to this one.

#para[Comparison with Silicon] Silicon reaches the same two facts by a
different route. `assume-valid-permissions` bounds each field chunk at
#vi[`write`] directly, the way the axiom above does; its non-aliasing
constraint is stated over receivers rather than locations, $x = y => p + q <=
1$, one instance per resource kind, where phrasing it over locations covers a
field, a bounded predicate and anything else in one form. And where this
verifier folds two chunks the moment their locations merge, Silicon's _state
consolidation_ iterates to a fix-point over terms handed to the solver — one
merge can produce an equality that licenses the next — with a worst case
cubic in the number of chunks @silicon[Section 3.4.2], which is why Silicon
schedules it rather than running it continuously. Holding locations as
e-classes removes the fix-point rather than the work: congruence has already
propagated every equality before the heap is consulted, so one linear pass
over one partition is all a lookup ever needs, and there is no scheduling
question left to ask.

That is the whole of what a chunk and a field are. What a program does with
one is the subject of @sec:impl-heap-interaction next.
