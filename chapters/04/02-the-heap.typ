#import "../../macros.typ": *
#import "../../figures/location-anatomy.typ": location-anatomy
#import "../../figures/heap-partitions.typ": heap-partitions
#import "../../figures/consolidation.typ": consolidation

== The Heap <sec:impl-heap>

So far, Helium has only executed streams of value-only instructions. To
verify a real Viper program it also has to reason about the heap.
@lst:heap-first-inhale is the smallest program that asks for that: it takes
permission to a field, assumes a fact about the value behind it, and then
checks a consequence of that fact.

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

VMIR makes a location a value of its own. #vi[`x.f`] becomes #vm[`f(x)`], a
location that permission can be taken to, read from and written to,
whichever the instruction asks for. Viper's #vi[`x.f`] instead plays two
roles above: once inside #vi[`acc`], naming what permission is taken to, and
once as an ordinary expression, naming the value stored there.
@lst:heap-first-inhale-vmir shows more precisely how the above Viper code is
lowered to VMIR, where that dual use is gone.

#vmir(
  caption: [Field access becomes a location dereference, and the heap is threaded explicitly through every operation on it.],
  label: "lst:heap-first-inhale-vmir",
)[```vmir
function f(e0: Ref): &[f] Int @ 1/1

method client {
  e0: Ref := fresh              // x
  e1: &[f] Int @ 1/1 := f(e0)   // address of x.f
  h0 := empty + e1 @ 1/1 with fresh
  e2: Int := *[h0] e1           // read the value at e1 in h0
  e3: Bool := e2 == 42          // x.f == 42
  assume e3
  e4: Int := *[h0] e1           // read the value at e1 in h0 again
  e5: Bool := e4 > 0            // x.f > 0
  assert e5
}
```]

The field declaration becomes an ordinary function,
#vm[`function f(e0: Ref): &[f] Int @ 1/1`]: given a #vi[`Ref`], it returns a
location type, which @sec:impl-locations reads part by part. The body lowers to
a sequence of instructions. The
#vi[`inhale`]
becomes #vm[`h0 := empty + e1 @ 1/1`] on line 6, the first heap operation VMIR
has: it takes a prior heap, #vm[`empty`] here since this is the body's first
statement, and adds a location to it, #vm[`e1`], with a permission amount, #vm[`1/1`],
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

=== Location types <sec:impl-locations>

The type #vm[`&[f] Int @ 1/1`] the example above gives #vm[e1] has three parts,
named in @fig:location-anatomy. #vi[`Int`] is the type stored at the location.
The #vm[`f`] in brackets is the location's _group_, and the #vm[`1/1`] after the
#vm[`@`] is its _permission bound_.

Both of those exist because a VMIR location is just a value. Viper's heap
already knows which object and which declaration a chunk belongs to, whereas
VMIR keeps no bookkeeping outside the type, so the type has to carry that
information. Two fields from two distinct field declarations may never alias
even when they store the same type, so the group records which declaration the
location came from. The permission bound caps how much permission the location
may hold at once, and it is either a rational literal or #vm[`*`], which is no
cap at all. A field's bound is #vm[`1/1`], since Viper allows no more than
#vi[`write`] to a field, and a predicate's is #vm[`*`], since Viper lets a
program hold an arbitrary permission amount of a folded predicate. Those two are
all a Viper program produces, though the type admits any literal.

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

=== Fields in VMIR

Fields are the first of the location producers, the declarations a location type
can come from. A field declaration fixes all three parts of the type at once,
and @lst:field-decl pairs it with the function it becomes.

#lowering(
  caption: [Field declaration in Viper becomes an uninterpreted function that maps the receiver to a location.],
  label: "lst:field-decl",
)[```viper
field f: Int
```][```vmir
function f(e0: Ref): &[f] Int @ 1/1
```]

VMIR diverges from verifiers like Silicon in one respect: it does not assume
field mappings are injective. In Silicon, injectivity is simply a consequence of how
a field chunk is represented, not a fact the reasoning would heavily depend on.
VMIR represents a field as an uninterpreted function instead, so injectivity
does not come for free. For instance, learning that two
locations are equal ($f(x) = f(y)$) does not by itself imply that the
receivers are ($x = y$). A frontend that wants injectivity can still declare
it, by exposing an inverse function alongside a postcondition stating the
round trip (@lst:field-inv). This means that VMIR's representation is
more expressive and flexible compared to what is assumed of Viper by Silicon.

#vmir(
  caption: [Injectivity of location functions can be encoded if required (pseudo-VMIR).],
  label: "lst:field-inv",
)[```vmir
function f(e0: Ref): &[f] Int @ 1/1
  ensures e0 == f_inv(result)

function f_inv(e0: &[f] Int @ 1/1): Ref
```]

=== Heap representation in Helium

A field becomes a mapping to location type; a program can take permission to
locations. Helium represents each permission a program holds to a location as
a _chunk_: a triple of symbolic values, a location, a permission amount and a
value. What remains is how Helium organises chunks into a heap.

#para[Partitioning] <para:impl-heap-part> Helium does not keep chunks in one
flat set. It splits them into _partitions_, one per location kind — group, stored type
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
Helium creates no new chunk: it merges the two into one, summing their
permission amounts. It takes the value from whichever side holds positive
permission;
if both do, it assumes them equal rather than asserting it. For two chunks
with permission amounts and values $p_0, v_0$ and $p_1, v_1$, merging produces

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
e-class and rebuilds the partition around those, merging the two chunks by
the same rule as an ordinary add. The retried lookup then finds one chunk
holding #vm[`1/1`], as required. Re-keying costs one linear pass over the
partition, and congruence, an invariant of the e-graph, had already closed the
equality before it ran, so nothing outside the heap needs to track it.

#para[Location axioms] <para:impl-location-axioms> To match Viper's memory
semantics, Helium emits two axioms for a location kind bounded by $b$
whenever a chunk is added or re-keyed:

- *Permission bound:* a chunk's own permission amount does not exceed the bound.
  $ p <= b $
- *Non-aliasing:* two chunks in the same partition, holding permission amounts $p, p'$ at
  locations $ell, ell'$, cannot together exceed the bound once their
  locations are equal.
  $ ell = ell' ==> p + p' <= b $

A field's bound is always #vm[`1/1`]. Take two full chunks, #vm[`f(x)`] and
#vm[`f(y)`], each holding #vm[`1/1`]: were they the same location, the
non-aliasing axiom would force $1 + 1 <= 1$, a contradiction, so they cannot
be. #vi[`x != y`] follows — needing nothing about #vi[`f`] beyond congruence;
no injectivity is assumed.

=== Heap operations in VMIR <sec:impl-heap-ops>

@lst:heap-first-inhale-vmir already used heap addition and dereference
without stating their preconditions. This subsection defines all four heap
instructions precisely: the partitions and chunks from the previous
subsection are what they operate on. @lst:heap-ops-instructions demonstrates
all four on the same location, #vm[`e1`], taken, read, overwritten, and
finally given up.

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

#align(center)[#vm[`h' := h + l @ p with v`]]

An addition takes permission to a location. Given a heap #vm[`h`], a location
#vm[`l`], a permission amount #vm[`p`] and a value #vm[`v`], it produces a new
heap #vm[`h'`] holding one more chunk at #vm[`l`]. #vm[`p`] is a #vm[`Real`]
amount, or the #vm[`wildcard`] permission amount introduced below. Before
adding the chunk, Helium confirms the amount is non-negative, $p >= 0$,
discharged by the usual mechanisms (@sec:impl-execution).

For #vm[`v`], a program writes one of two things. #vm[`fresh`] leaves the value
unconstrained: Helium picks an arbitrary symbolic value for the chunk,
restricted only by #vm[`l`]'s stored type. Otherwise the program supplies a
concrete value, an earlier temporary #vm[`e`]#sub[`n`] or a literal constant,
which must itself share that type. Either way, if the partition already holds a
chunk at #vm[`l`], the two are merged by consolidation rather than kept apart
(#pararef(<para:impl-consolidation>, [Consolidation])). Line 2 of
@lst:heap-ops-instructions takes #vm[`1/1`] at #vm[`e1`] with a fresh value.

#align(center)[#vm[`v := *[h] l`]]

A dereference reads the value a heap holds at a location. It is the one heap
operation that produces no new heap: it takes #vm[`h`] and #vm[`l`] and returns
the stored value #vm[`v`]. Reading requires strictly positive permission,
$p_"held" > 0$. If no chunk is found, or the held permission amount cannot be
proven positive, the dereference fails. Line 3 reads the chunk the line before
it added, and the amount there was #vm[`1/1`], so #vm[`e2`] is bound to the
fresh value.

#align(center)[#vm[`h' := h assign l with v`]]

An assignment replaces the value a heap holds at a location. It takes
#vm[`h`], #vm[`l`] and a new value #vm[`v`], and produces #vm[`h'`] with the
target chunk's value replaced and every other chunk untouched. Writing requires
the location's full permission bound, #vm[`1/1`] for a field and #vm[`*`] for a
predicate, which by construction can never be written. Line 4 overwrites the
value at #vm[`e1`], which already holds #vm[`1/1`], so the write succeeds and
#vm[`h1`] maps #vm[`e1`] to #vm[`10`].

#align(center)[#vm[`h', v := h - l @ p`]]

A subtraction gives up permission to a location. It is addition's mirror image:
it takes #vm[`h`], #vm[`l`] and a permission amount #vm[`p`] to remove, and
produces a new heap #vm[`h'`] together with a snapshot of the removed chunk's
value, #vm[`v: Option[Int]`], which is #vm[`Some(...)`] if the removed
permission amount was positive and #vm[`None`] otherwise. It fails if #vm[`p`]
cannot be proven non-negative, or if the found chunk holds less than #vm[`p`].
If the chunk is missing or insufficient, Helium re-keys the partition and
retries once (#pararef(<para:impl-consolidation>, [Consolidation])), in case two
locations merged since the chunk was added.

Line 5 subtracts the full #vm[`1/1`] and leaves #vm[`e1`] with nothing behind it
in #vm[`h2`]. Line 6 dereferences #vm[`e1`] again and fails: the held permission
is zero, not strictly positive, so no value can be produced. Helium removes a
chunk outright once its permission provably reaches zero, since a
zero-permission chunk can never be read and never usefully merges with another.

=== Conditional permissions <sec:impl-conditional-perms>

A Viper assertion may put an #vi[`acc`] under a condition, so the permission is
granted only where that condition holds. @lst:guarded-add does so at a symbolic
amount, which is what shows where the condition has to reach.

#lowering(
  caption: [A guarded access at a symbolic amount, #vm[`e0`] the receiver and
    #vm[`e1`] the amount. The guard becomes both the permission and the add's
    path condition.],
  label: "lst:guarded-add",
)[```viper
inhale p >= none ==> acc(x.f, p)
```][```vmir
e2: Bool := e1 < 0/1
e3: Bool := e2 ? false : true
e4: &[f] Int @ 1/1 := f(e0)
p0 := e3 ? e1 : 0/1
h0 := <e3> empty + e4 @ p0 with fresh
```]

The add carries no trace of the implication. What the guard produces is
#vm[`p0`], the amount #vm[`e1`] where #vm[`e3`] holds and #vm[`0/1`] where it
does not. The condition reaches the add a second way, as the path condition
#vm[`<e3>`]: an add owes $p >= 0$ before it places its chunk, and with a
symbolic amount that condition alone proves it. The inhale
is equivalent to #vi[`inhale acc(x.f, p >= none ? p : none)`], which is what
Helium executes.

#vm[`p0`] belongs to neither namespace the section has used so far. VMIR gives
amounts one of their own, #vm[`p`], beside values #vm[`e`] and heaps #vm[`h`].
An amount is a rational literal, a value of type #vi[`Real`], the
#vm[`wildcard`] of @sec:impl-wildcards, or a temporary produced by the sole
instruction the namespace has,

#align(center)[#vm[`p' := e ? p0 : p1`]]

whose condition is drawn from the value space and whose arms are themselves
amounts. What the separate namespace buys is the subject of @sec:impl-wildcards.

A chunk's permission is therefore not a single amount but a tree of conditions
with amounts at the leaves, in the shape the instructions that built it had.
Helium holds that tree beside the e-graph, building a term only where a prover
needs one e-class.

Obligations over an amount are answered arm by arm. Addition and subtraction
demand only
$0 <= p$, which a gated amount meets on both: the arm the guard switches off is
the literal #vm[`0/1`] and folds away, and the other stands under the guard. A
dereference's $p > 0$, an assignment's demand for the location's
permission bound, and the permission bound axiom are discharged leaf
by leaf, each under the conditions that reach it. The non-aliasing axiom weighs
a sum of two amounts, which Helium forms only where both are unbranched, so a
branch-structured amount states no disequality. The resource instructions of
@sec:impl-predicates demand strict positivity instead, each carrying a boolean
that at zero permission would be vacuous.

=== Wildcard permissions <sec:impl-wildcards>

A #vm[`wildcard`] is an amount that carries a sign and no magnitude: the share
is positive and its size stays open. It stands in the amount slot with no
operand of its own. What it denotes depends on what the heap already holds at
the location, so the instruction executing it resolves it.
@lst:wildcard-ops takes one onto a location held at a fraction, and gives it
back.

#vmir(
  caption: [A wildcard added under a guard to a location held at #vm[`1/2`],
    then given back.],
  label: "lst:wildcard-ops",
)[```vmir
e2: &[f] Int @ 1/1 := f(e0)
h0 := empty + e2 @ 1/2 with fresh
p0 := e1 ? wildcard : 0/1
h1 := h0 + e2 @ p0 with fresh  // holds e1 ? p' : 1/2, with 1/2 < p'
h2 := h1 - e2 @ wildcard       // needs p > 0, leaves 0 < r < p
```]

Adding a wildcard to a location already holding $p$ produces a fresh share $p'$
assumed strictly larger, $p < p'$, which settles $0 < p'$ too, since $p$ was at
least zero. Where the location held nothing, the share is a fresh positive real.
Helium builds no sum node in either case: the e-graph carries no order theory
for the reals, so $p + w$ would be an opaque leaf no comparison could use. The
permission bound of #pararef(<para:impl-location-axioms>, [Location axioms])
finishes the argument: a location held at #vm[`1/1`] that takes a further
wildcard bounds a strictly larger share by #vm[`1/1`], so that state is
unreachable.

Subtraction has nothing to weigh a wildcard against. The obligation is instead
that the location holds something at all, $p_"held" > 0$, and what remains is a
fresh remainder, $0 < r < p_"held"$. Those are the two facts a later read and a
later debit turn on, and a difference node $p_"held" - w$ would support neither,
for want of an order theory.

Line 3 is what earns the permission namespace its place: a wildcard under a
guard. Helium could resolve the share where the instruction is emitted, by
reading what the heap holds at the location under that guard and picking a
larger value there. It builds the gate instead and lets the add resolve it arm
by arm, so a location held at $p$ under a guard $g$ comes out at
$ternary(g, p', p)$ with $p < p'$, which is line 4. A
wildcard on its own denotes nothing that can be computed over, and the namespace
guarantees it never is: heap instructions and further permission instructions
are its only consumers, settled by typing rather than a check at every use. Its
provenance rides on that structure too, since congruence would put a share
coinciding with a literal into that class.

A Viper program may write #vi[`wildcard`] itself, and the translator introduces
one wherever the program only reads: a function's body, and the resource a
heap-dependent function's precondition lowers to. There a literal #vm[`0/1`]
stays, a literal nonzero amount becomes a #vm[`wildcard`], and a symbolic amount
$p$ becomes

$ ternary(0 < p, "wildcard", "0/1") $

which keeps a conditional footprint conditional: #vi[`requires b ==> acc(x.f)`]
demands a share only where #vi[`b`] holds, while predicate bodies and method
preconditions keep their amounts as written. The cost is that nothing records
how much a wildcard debit took, which is the arithmetic a read-only region
needs.


=== Comparison with Silicon

Silicon's heap representation reaches the same guarantees as partitioning,
consolidation and the location axioms above, by a different route throughout. Silicon treats consolidation the same way Helium treats re-keying: a fallback
that repairs the heap representation rather than something run after every
operation. It is scheduled periodically, since a full pass repeatedly asks
the SMT solver whether pairs of receivers are equal, which is cubic in the
number of chunks in the worst case @silicon[Section 3.4.2]. Helium's
re-keying instead costs one linear pass, since every location is already canonicalised inside the e-graph (#pararef(<para:impl-consolidation>, [Consolidation])), and thus can run directly on a failed lookup.

The two verifiers also place the non-aliasing axiom differently. Silicon
states it over field receivers, one instance per field:
$x = y ==> p + p' <= b$. Helium states it over locations instead
(#pararef(<para:impl-location-axioms>, [Location axioms])):
$ell = ell' ==> p + p' <= b$, which covers a field and a bounded predicate in
the same form. Stating it over receivers is exactly where Silicon's
representation makes field mappings injective, something VMIR's location
type does not give by default (@lst:field-inv).
