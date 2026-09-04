#import "../../macros.typ": *
#import "../../figures/location-anatomy.typ": location-anatomy
#import "../../figures/heap-partitions.typ": heap-partitions

== The Heap <sec:impl-heap>

Up to this point, we have executed streams of value-producing instructions only. To
verify an actual Viper program, the execution model must also reason about the
heap. The program below is the simplest one requiring heap manipulation: it acquires
permission to a field, assumes a fact about the underlying value, and
subsequently asserts a consequence of that fact.

#no-numbers[```viper
field f: Int

method client(x: Ref) {
  inhale acc(x.f, write) && x.f == 42
  assert x.f > 0
}
```]

In Viper, #vi[`x.f`] denotes two different things depending on where it appears:
inside #vi[`acc`] it denotes the place permission is held, and in an expression
it denotes the value stored there. VMIR separates the two, as
@lst:heap-first-inhale-vmir shows. The place becomes the location #vm[`f(x)`],
the operand a heap operation adds permission to or subtracts it from. The value
becomes the dereference #vm[`*[h] f(x)`], which names the heap it reads.

#vmir(
  caption: [Field access becomes a location dereference, and the heap is threaded explicitly through every operation on it.],
  label: "lst:heap-first-inhale-vmir",
  placement: auto,
)[```vmir
function f(e0: Ref): &[f] Int @ 1/1

method client {
  e0: Ref := fresh              // x
  e1: &[f] Int @ 1/1 := f(e0)   // address of x.f
  h0 := empty + e1 @ 1/1 with fresh
  e2: Int := *[h0] e1           // value at x.f
  e3: Bool := e2 == 42          // x.f == 42
  assume e3
  e4: Int := *[h0] e1           // value at x.f again
  e5: Bool := e4 >i 0           // x.f > 0
  assert e5
}
```]

The field declaration becomes the ordinary function on line 1: given a
#vi[`Ref`], it returns a location type. The #vi[`inhale`] becomes lines 6 to 9.
Line 6 is the first heap operation VMIR has: it takes a prior heap, #vm[`empty`]
here since this is the body's first statement, and adds a location to it,
#vm[`e1`], the #vm[`f(e0)`] bound on the line above, with a permission amount,
the rational literal #vm[`1/1`], and a value named after #vi[`with`], here a
fresh symbolic one. Lines 7 to 9 carry the conjunct: line 7 reads the value back
out with the dereference operator #vm[`*`], which takes a location and a heap to
consult, and the #vi[`assume`] states the fact the #vi[`inhale`] promised. The
rest of the method repeats the read against the same #vm[`h0`] and checks the
assertion.

@lst:heap-first-inhale-vmir highlights an additional architectural choice: heaps
are explicit and immutable. Each heap operation yields a new heap, requiring any
heap-dependent instruction to explicitly specify its target heap---#vm[`h0`] in
both instances here, as no subsequent heap was produced. Conversely, Viper
maintains an implicit, globally threaded heap where operations implicitly modify
the current state, and accessing prior states requires an explicit #vi[`old`]
expression.

#para[Location types] The type #vm[`&[f] Int @ 1/1`] the example above gives #vm[e1] has three parts,
named in @fig:location-anatomy. #vi[`Int`] is the type stored at the location.
The #vm[`f`] in brackets is the location's _group_, and the #vm[`1/1`] after the
#vm[`@`] is its _permission bound_.

In Viper, a field access names its declaration, so the verifier can look up what
that access permits. VMIR detaches a location from its declaration: #vm[`f(x)`]
is an ordinary term, and a heap operation receives nothing but that term. The
information the declaration supplied therefore has to be recorded somewhere, and
the location's type is the natural place. The group records which declaration the
location came from, so that two fields from distinct declarations never alias
even when they store the same type. The permission bound caps how much permission
the location may hold at once, and it is either a rational literal or #vm[`*`],
which is no cap at all.

#figure(
  location-anatomy,
  caption: [A location belonging to group #vm[`f`], storing an integer, with at most #vm[`1/1`] permission amount.],
) <fig:location-anatomy>

Because the type is self-contained, one form covers both kinds of location: a
folded predicate is a location whose stored type is the predicate's footprint
rather than a value. An aliasing check or a bound axiom reads what it needs from
the location alone, without consulting the declaration.

#para[Fields in VMIR] Fields are the first of the location producers, the declarations a location type
can come from. A field declaration fixes all three parts of the type at once,
and it becomes an uninterpreted function mapping the receiver to a location.

#lowering(
)[```viper
field f: Int
```][```vmir
function f(e0: Ref): &[f] Int @ 1/1
```]

VMIR differs from Silicon in one respect here: it does not assume that a field
mapping is injective. Silicon has no function symbol for a field, since a chunk
is identified by its field and its receiver together, so two chunks coincide only
when their receivers do. VMIR names the field with an uninterpreted function, so
$f(x) = f(y)$ does not on its own give $x = y$. A translation from Viper that
needs the property can state it, by emitting an inverse function and a
postcondition for the round trip, written below in pseudo-VMIR.

#no-numbers[```vmir
function f(e0: Ref): &[f] Int @ 1/1
  ensures e0 == f_inv(result)

function f_inv(e0: &[f] Int @ 1/1): Ref
```]

#para[Heap representation in Helium] A program holds permission at locations, and
Helium records each such holding as a _chunk_: the location, the permission
amount, and the value stored there. We do not
keep chunks in one flat set, but split them into _partitions_, one per location
kind, where a kind is a group, a stored type and a permission bound taken
together (@fig:location-anatomy). A chunk lives in exactly the partition its location's
type names, and within a partition chunks are indexed by the e-class their
location resolves to. A lookup therefore picks a partition from the location
kind and finds the chunk by e-class inside it (@fig:heap-partitions).

Silicon holds every chunk in one flat sequence and filters it by chunk
identifier on each lookup, then matches the receiver syntactically and, failing
that, asks the solver to compare it against each remaining candidate.
Partitioning does that filtering once, when the chunk is added, and the e-class
index settles the receiver without a solver query.

#figure(
  heap-partitions,
  caption: [The symbolic heap as boxes, one per location kind. A chunk lives in
    exactly one partition, so #vi[`f(x)`] and #vi[`g(y)`] land in different
    partitions despite sharing a stored type and a bound.],
) <fig:heap-partitions>

Adding a chunk merges it with what the partition already holds. We first check
whether the partition holds a chunk at the same location. If it does, we create
no new chunk but merge the two into one, summing their permission amounts. We take the value from whichever side holds positive
permission;
if both do, we assume them equal rather than asserting it. For two chunks
with permission amounts and values $p_0, v_0$ and $p_1, v_1$, merging produces

$ p' := p_0 + p_1, quad v' := ternary(p_0 > 0, v_0, v_1) $

$ p_0 > 0 and p_1 > 0 ==> v_0 = v_1 " (assumed)" $

Sometimes we learn two locations are equal only after their chunks are
already on the heap. The program below takes half permission to #vi[`x.f`] and half to
#vi[`y.f`], learns #vi[`x == y`], then exhales the combined whole.

#no-numbers[```viper
inhale acc(x.f, 1/2) && acc(y.f, 1/2)
assume x == y
exhale acc(x.f, 1/1)
```]

The greedy lookup for the #vi[`exhale`] fails: it finds only the #vm[`1/2`]
chunk at #vm[`f(x)`]'s own e-class, since the #vi[`assume`] merged #vi[`x`]
and #vi[`y`]'s e-classes without touching the heap. On failure, we _consolidate_ the
partition: we ask the e-graph for each chunk's canonical e-class and rebuild the
partition around those, merging chunks by the same rule as an ordinary add. The
retried lookup then finds one chunk holding #vm[`1/1`], as required. Silicon's
heap consolidation does the same repair, but decides aliasing by asking the
solver whether pairs of receivers are equal, so it is scheduled periodically
rather than run on demand. Helium's reads canonical e-classes that congruence has
already computed, so it costs one linear pass and runs on a failed lookup.

To match Viper's memory
semantics, we emit two _location axioms_ for a location kind bounded by $b$
whenever a chunk is added or consolidated:

- *Permission bound:* a chunk's own permission amount does not exceed the bound.
  $ p <= b $
- *Non-aliasing:* two chunks in the same partition, holding permission amounts $p, p'$ at
  locations $ell, ell'$, cannot together exceed the bound once their
  locations are equal.
  $ ell = ell' ==> p + p' <= b $

A field's bound is always #vm[`1/1`]. Two full chunks #vm[`f(x)`] and #vm[`f(y)`]
share a partition, so were their locations equal the non-aliasing axiom would
force $1 + 1 <= 1$, and therefore $f(x) != f(y)$. The contrapositive of
congruence, $f(x) != f(y) ==> x != y$, then gives #vi[`x != y`] without assuming
injectivity.

#para[Heap operations in VMIR] @lst:heap-first-inhale-vmir already used heap
addition and dereference without stating their semantics.
@lst:heap-ops-instructions demonstrates the four operations that act at a single
location, on the same #vm[`e1`], taken, read, overwritten, and finally given
up.

#vmir(
  caption: [The same location added, read, overwritten, and then given up
    entirely — the final read has nothing left to find.],
  label: "lst:heap-ops-instructions",
)[```vmir
e1: &[f] Int @ 1/1 := f(e0)
h0 := empty + e1 @ 1/1 with fresh     // add perm for loc e1
e2: Int := *[h0] e1                   // read the stored value
h1 := h0 assign e1 with 10            // replace it with 10
h2, e3: Option[Int] := h1 - e1 @ 1/1  // give up full permission
e4: Int := *[h2] e1                   // now fails: no perm left
```]

An addition, #vm[`h' := h + l @ p with v`], takes permission to a location.
Given a heap #vm[`h`], a location
#vm[`l`], a permission amount #vm[`p`] and a value #vm[`v`], it produces a new
heap #vm[`h'`] holding one more chunk at #vm[`l`]. #vm[`p`] is a #vm[`Real`]
amount, or the #vm[`wildcard`] permission amount introduced below. Before
adding the chunk, we confirm the amount is non-negative, $p >= 0$,
discharged by the usual mechanisms (@sec:impl-execution).

The value operand after the #vm[`with`] clause is one of two things.
#vm[`fresh`] leaves the value unconstrained: we pick an arbitrary symbolic value for the chunk, restricted
only by the location's stored type. Otherwise the program supplies a concrete
value, an earlier temporary #vm[`e`]#sub[`n`] or a literal constant, which must
share that type. Either way, if the partition already holds a chunk at that
location, the two are merged rather than kept apart.
Line 2 of
@lst:heap-ops-instructions takes #vm[`1/1`] at #vm[`e1`] with a fresh value.

A dereference, #vm[`v := *[h] l`], reads the value a heap holds at a location.
It is the one heap
operation that produces no new heap: it takes #vm[`h`] and #vm[`l`] and returns
the stored value #vm[`v`]. Reading requires strictly positive permission,
$p_"held" > 0$. If no chunk is found, or the held permission amount cannot be
proven positive, the dereference fails. Line 3 reads the chunk the line before
it added, and the amount there was #vm[`1/1`], so #vm[`e2`] is bound to the
fresh value.

An assignment, #vm[`h' := h assign l with v`], replaces the value a heap holds
at a location. It takes
#vm[`h`], #vm[`l`] and a new value #vm[`v`], and produces #vm[`h'`] with the
target chunk's value replaced and every other chunk untouched. Writing requires
the location's full permission bound, #vm[`1/1`] for a field and #vm[`*`] for a
predicate, which by construction can never be written. Line 4 overwrites the
value at #vm[`e1`], which already holds #vm[`1/1`], so the write succeeds and
#vm[`h1`] maps #vm[`e1`] to #vm[`10`].

A subtraction, #vm[`h', v := h - l @ p`], gives up permission to a location. It
is addition's mirror image:
it takes #vm[`h`], #vm[`l`] and a permission amount #vm[`p`] to remove, and
produces a new heap #vm[`h'`] together with a snapshot of the removed chunk's
value, #vm[`v: Option[Int]`], which is #vm[`Some(...)`] if the removed
permission amount was positive and #vm[`None`] otherwise. It fails if #vm[`p`]
cannot be proven non-negative, or if the found chunk holds less than #vm[`p`].
If the chunk is missing or insufficient, we consolidate the partition and
retry once, in case two locations merged since the chunk was added.

Line 5 of @lst:heap-ops-instructions subtracts the full #vm[`1/1`] and leaves
#vm[`e1`] with nothing behind it in #vm[`h2`]. Line 6 dereferences #vm[`e1`] again and fails: the held permission
is zero, not strictly positive, so no value can be produced. We remove a
chunk outright once its permission provably reaches zero, since a
zero-permission chunk can never be read and never usefully merges with another.

#para[Conditional permissions] A Viper assertion may put an #vi[`acc`] under a condition, so the permission is
granted only where that condition holds. The lowering below does so at a
symbolic amount, with #vm[`e0`] the receiver and #vm[`e1`] the amount: the guard
becomes a conditional permission amount.

#lowering(
)[```viper
inhale p >= none ==> acc(x.f, p)
```][```vmir
e2: Bool := e1 <r 0/1
e3: Bool := e2 ? false : true
e4: &[f] Int @ 1/1 := f(e0)
p0 := e3 ? e1 : 0/1
h0 := <e3> empty + e4 @ p0 with fresh
```]

We conditionalise the permission amount rather than encoding the implication
directly: the guard produces #vm[`p0`], which evaluates to #vm[`e1`] where
#vm[`e3`] holds and to #vm[`0/1`] otherwise. The guard is also the add's path
condition, #vm[`<e3>`], which is what lets the add discharge its obligation that
#vm[`p0`] be non-negative.
VMIR gives permission amounts their own namespace, #vm[`p`], distinct from values #vm[`e`] and heaps #vm[`h`].
An amount can be a rational literal, a symbolic value of type #vi[`Real`], a #vm[`wildcard`], or a ternary conditional expression:

#align(center)[#vm[`p' := e ? p0 : p1`]]

Helium keeps a conditional amount in two forms at once. The amount enters the
e-graph like any other term, giving one e-class for the whole ternary, and Helium
separately retains the ternary as a tree of conditions with amounts at its
leaves.

The tree proves sufficiency at a subtraction. Helium first asks whether
the held amount covers the requested one from the e-classes alone, and when that
fails it descends the tree, checking each branch under its own condition.
Settling it in the e-graph instead would need the distributive rule
@sec:impl-execution rules out, whose right-hand side names terms the left does
not bind. Descending the tree is therefore one of the few places Helium
case-splits.

#para[Wildcard permissions] In Viper, wildcards are used when a programmer wants to denote some positive amount of permission without specifying an exact value. In VMIR, a #vm[`wildcard`] can be used wherever a heap operation expects a permission amount (#vi[`Real`]). However, a wildcard is not a normal value and has no concrete numerical meaning by itself. It only gains meaning when executed by a heap operation, at which point it resolves to an unspecified positive amount of permission, as
in the lowering below.

#lowering(
  stacked: true,
)[```viper
inhale acc(x.f, wildcard)
```][```vmir
e1: &[f] Int @ 1/1 := f(e0)
h0 := empty + e1 @ wildcard with fresh
```]

When a wildcard is added to a location, the new permission amount is defined to be a fresh permission symbolic assumed to be strictly more than the symbolic stored there previously. If a location held permission amount $p$, adding a wildcard produces a new fresh share $p'$ with the assumption $p' > p$. This settles $p' > 0$ since $p$ was at least zero. Where the location held nothing, the share is simply a fresh positive real.

Conversely, when a wildcard is subtracted, the obligation is that the location holds some positive permission ($p_"held" > 0$). The new permission amount is defined to be a fresh remainder $r$ that is strictly less than what was held before, but still greater than zero ($0 < r < p_"held"$).

Wildcards can appear under conditions, such as when a programmer conditionally inhales a wildcard. This delayed interpretation is precisely why structurally distinct #vm[`p`]-kinded expressions are necessary. When adding or subtracting a wildcard under a #vm[`p`]-ternary tree, Helium has to pick a concrete symbolic value for the wildcard branch. For example, assume we held $p$ permission before. If we now add the amount #vm[`c ? wildcard : 1/2`], Helium resolves this during the heap operation. The resulting permission amount becomes #vm[`c ? p' : p +r 1/2`], where $p'$ is a fresh symbolic assumed to be larger than $p$ ($p' > p$). Building this ternary structure in the #vm[`p`] namespace allows the wildcard to remain uninterpreted until the heap operation can correctly resolve it against the currently held permission.

Beyond explicit use by the programmer, wildcards are heavily relied upon internally during translation. When lowering heap-dependent functions to VMIR, Helium follows the default semantics of Silicon and changes every permission amount to be either a #vm[`wildcard`] or #vm[`0/1`]. If it is not decidable at translation time whether a symbolic amount $p$ is positive, the translator emits a ternary expression: #vm(`0/1 < p ? wildcard : 0/1`).


#para[Comparison with Silicon] Silicon's heap representation reaches the same
guarantees as partitioning, consolidation and the location axioms above, by a
different route throughout. Its consolidation is cubic in the number of chunks in
the worst case, since a full pass repeatedly queries the solver
@silicon[Section 3.4.2].

The two verifiers also place the non-aliasing axiom differently. Silicon
states it over field receivers, one instance per field:
$x = y ==> p + p' <= b$. Helium states it over locations, $ell = ell' ==> p + p'
<= b$, with $ell$ being #vm[`f(x)`] for a field. Stating it over receivers makes Silicon's field mappings injective. VMIR has injectivity only where a
translation encodes it.
