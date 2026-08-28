#import "../../macros.typ": *
#import "../../figures/location-anatomy.typ": location-anatomy
#import "../../figures/heap-partitions.typ": heap-partitions
#import "../../figures/consolidation.typ": consolidation

== The Heap in VMIR and Helium <sec:impl-heap>

So far, Helium has only executed streams of value-only instructions. To
verify a real Viper program it also has to reason about the heap, as in
@lst:heap-first-inhale.

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

#para[Location types] The example above has already introduced the idea of
locations as values. We formalise it here.

@lst:heap-first-inhale-vmir also leaves out two parts of a location type:
its _group_ and its _permission bound_. Both exist because a VMIR location is
just a value: unlike Viper's heap, which already knows which object and
which declaration a chunk belongs to, VMIR has no bookkeeping outside the
type itself, so the type has to carry that information. Two fields coming
from two distinct field declarations may never alias, even when they store
the same type, so a location type has to encode which declaration it came
from: this is the _group_. The _permission bound_ states how much permission
a location may hold at once. A field's
bound is always #vi[`write`]#[;] a predicate's bound is unconstrained by
default, since Viper lets a program hold an arbitrary permission amount of a folded
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
field mappings are injective. In Silicon, injectivity is simply a consequence of how
a field chunk is represented, not a fact the reasoning would heavily depend on.
VMIR represents a field as an uninterpreted function instead, so injectivity
does not come for directly. For instance, learning that two
locations are equal ($f(x) = f(y)$) does not by itself imply that the
receivers are ($x = y$). A frontend that wants injectivity can still declare
it, by exposing an inverse function alongside a postcondition stating the
round trip (@lst:field-inv). This means that VMIR's representation is
more expressive and flexible compared to what is assumed of Viper by Silicon.

#vmir(caption: [Injectivity of location functions can be encoded if required.], label: "lst:field-inv")[```vmir
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
holding #vm[`1/1`], as required.

Re-keying costs one linear pass over the partition. Congruence, an invariant
of the e-graph, already closed the equality before re-keying ran — nothing
outside the heap needs to track it.

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

#para[Comparison with Silicon] Silicon's heap representation reaches the same
guarantees as partitioning, consolidation and the location axioms above, by a
different route throughout. Silicon treats consolidation the same way Helium treats re-keying: a fallback
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

=== Heap operations in VMIR

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

#para[Heap addition] <para:impl-heap-add>

#align(center)[#vm[`h' := h + l @ p with v`]]

Line 1 of @lst:heap-ops-instructions is this instruction: given a heap #vm[`h`], a
location #vm[`l`], a permission amount #vm[`p`] and a value #vm[`v`], it produces a new
heap #vm[`h'`] holding one more chunk at #vm[`l`]. #vm[`p`] is a #vm[`Real`]
amount, or the #vm[`wildcard`] permission amount introduced below; before adding the
chunk, Helium confirms it is non-negative, $p >= 0$, discharged by the usual
mechanisms (@sec:impl-execution).

For #vm[`v`], a program writes one of two things. #vm[`fresh`], used on line
1, leaves the value unconstrained: Helium picks an arbitrary symbolic value
for the chunk, restricted only by #vm[`l`]'s stored type. Otherwise the
program supplies a concrete value — an earlier temporary #vm[`e`]#sub[`n`] or
a literal constant — which must itself share that type. Either way, if the
partition already holds a chunk at #vm[`l`], the two are merged by
consolidation rather than kept apart (#pararef(<para:impl-consolidation>, [Consolidation])).

#para[Heap dereference] <para:impl-heap-deref>

#align(center)[#vm[`v := *[h] l`]]

Line 2 reads the chunk just added. Dereference is the one heap operation that
produces no new heap: it takes #vm[`h`] and #vm[`l`] and returns the stored
value #vm[`v`]. Reading requires strictly positive permission, $p_"held" >
0$. The permission amount added on line 1 was #vm[`1/1`], so the read succeeds and
#vm[`e2`] is bound to the fresh value. If no chunk is found, or the held
permission amount cannot be proven positive, the dereference fails.

#para[Heap assignment] <para:impl-heap-write>

#align(center)[#vm[`h' := h assign l with v`]]

Line 3 overwrites that value. Assignment takes #vm[`h`], #vm[`l`] and a new
value #vm[`v`], and produces #vm[`h'`] with the target chunk's value
replaced; every other chunk is untouched. Writing requires full permission —
the location's permission bound, #vm[`1/1`] for a field, #vm[`*`] (unbounded)
for a predicate, which by construction can never be written. #vm[`e1`]
already holds #vm[`1/1`] from line 1, so the write on line 3 succeeds, and
#vm[`h1`] maps #vm[`e1`] to #vm[`10`].

#para[Heap subtraction] <para:impl-heap-sub>

#align(center)[#vm[`h', v := h - l @ p`]]

Line 4 gives up that permission. Subtraction is addition's mirror image: it
takes #vm[`h`], #vm[`l`] and a permission amount #vm[`p`] to remove, and produces a new
heap #vm[`h'`] together with a snapshot of the removed chunk's value,
#vm[`v: Option[Int]`] — #vm[`Some(...)`] if the removed permission amount was positive,
#vm[`None`] otherwise. It fails if #vm[`p`] cannot be proven non-negative, or
if the found chunk holds less than #vm[`p`]. If the chunk is missing or
insufficient, Helium re-keys the partition and retries once
(#pararef(<para:impl-consolidation>, [Consolidation])), in case two locations
merged since the chunk was added.

Subtracting the full #vm[`1/1`] on line 4 leaves #vm[`e1`] with nothing
behind it in #vm[`h2`]. Line 5 dereferences #vm[`e1`] again and fails: the
held permission is zero, not strictly positive, so no value can be produced.
Helium removes a chunk outright once its permission provably reaches zero —
a zero-permission chunk can never be read and never usefully merges with
another, so dropping it costs nothing.

=== Conditional permissions <sec:impl-conditional-perms>

Each of the four instructions names one location and one amount, and executes
whenever control reaches it. Viper grants permission under a condition as
readily as it grants it outright, and @lst:guarded-add is the smallest program
that does so.

#lowering(
  caption: [A guarded access. The guard becomes the permission amount, and the
    add stays unconditional.],
  label: "lst:guarded-add",
)[```viper
method client(x: Ref, b: Bool) {
  inhale b ==> acc(x.f, write)
}
```][```vmir
method client {
  e0: Ref := fresh
  e1: Bool := fresh
  e2: &[f] Int @ 1/1 := f(e0)
  p0 := e1 ? 1/1 : 0/1
  h0 := empty + e2 @ p0
        with fresh
}
```]

The add on the last line carries no trace of #vi[`b`]. What the guard produces
is #vm[`p0`], the full amount where #vm[`e1`] holds and none where it does not,
and the add then runs whatever that amount turns out to be.

#vm[`p0`] belongs to neither namespace the section has used so far. VMIR gives
permissions an operand namespace of their own, #vm[`p`], beside values #vm[`e`]
and heaps #vm[`h`]. An amount is a rational literal, an ordinary value of type
#vi[`Real`], the #vm[`wildcard`] of @sec:impl-wildcards, or a temporary produced
by the sole instruction the namespace has,

#align(center)[#vm[`p' := e ? p0 : p1`]]

whose condition is drawn from the value space and whose two arms are themselves
amounts. Separating the namespaces settles two questions by typing that would
otherwise take a check at every use: #vm[`wildcard`] is well-formed exactly
where an amount is expected, and an amount reaches the e-graph only when a
prover asks for it. Guards nest by nesting the instruction, one temporary per
condition, so the translator emits a gate for each condition standing on its
branch stack when it reaches an #vi[`acc`].

A reader would reasonably expect the condition on the add instead, selecting
between a heap that holds the chunk and a heap that does not. We keep the add
unconditional because the alternative makes the set of chunks a heap holds
depend on a path condition, and @sec:impl-predicates needs that set to be
readable from a declaration alone. The cost is that presence becomes an
arithmetic question rather than a structural one, and every obligation the four
instructions raise has to be answered in those terms.

Helium answers them in two ways. First, addition and subtraction demand only
that the amount is non-negative, $0 <= p$. A gated amount meets that demand by
construction, since the arm the guard switches off is the literal #vm[`0/1`] and
constant folding closes the goal before the guard enters it. A strict demand
here would be wrong rather than merely stronger, because it would reject every
guarded #vi[`acc`] on the path where its guard fails. The resource instructions
of @sec:impl-predicates do demand strict positivity, for a reason specific to
them: each also assumes or asserts a boolean, which at zero permission would be
vacuous.

Second, the demands that weigh an amount against something else are proven arm
by arm. A dereference requires $p > 0$, an assignment requires the location's
permission bound, and the permission bound and non-aliasing axioms each weigh
an amount against that bound. For each, Helium walks the ternary structure of the amount, pushes
the arm's condition onto the path condition, and proves the leaf beneath it.
Flattening the same demand into one goal over $ternary(g, p, 0)$ would instead
require reasoning by cases, which the prove ladder of @sec:impl-execution
deliberately does not do.

For the non-aliasing axiom the difference between the two readings is a
soundness question rather than a completeness one. @lst:gate-alias takes full
permission to one field on each branch and asks whether the two receivers
differ.

#viper(
  caption: [Two full accesses on exclusive paths. The receivers may well be
    equal, and Helium must not prove otherwise.],
  label: "lst:gate-alias",
)[```viper
method client(x: Ref, y: Ref, b: Bool) {
  if (b) { inhale acc(x.f, write) }
  else   { inhale acc(y.f, write) }
  assert x != y                       // must not verify
}
```]

Both chunks sit on one heap, each at an amount worth #vm[`1/1`] on its own
branch and #vm[`0/1`] on the other. Read flat, with the guards discarded, the
two amounts are #vm[`1/1`] apiece, and the non-aliasing axiom forces
$1 + 1 <= 1$ once $f(x) = f(y)$, which refutes the equality and proves
#vi[`x != y`]. The program establishes only that one of the two was taken:
whichever branch ran, nothing was ever held at both locations at once, and the
receivers are free to be equal. Stating the axiom per arm attaches to each
amount the condition under which it is positive, and those two conditions are
contradictory, so the sum the axiom would bound never arises.

Helium therefore holds an amount's ternary structure alongside the e-graph
rather than as a term inside it, and builds a term only where a prover needs a
single e-class to work with. We chose that representation because a consume can
then line the arms of what it demands up against the arms of what is held,
instead of discharging one goal over two opaque ternaries.

=== Wildcard permissions <sec:impl-wildcards>

A gated amount lets a program hold permission on some paths. A different
weakening is what a program that only ever reads needs, and Prusti's encoding
asks for it in 24 of its 11648 accesses (@tbl:corpus), every other one naming
#vi[`write`]. @lst:wildcard-ops runs a location through the full cycle at that
weaker amount.

#vmir(
  caption: [A wildcard taken, read through, given back, and given back a second
    time under a guard. No instruction here names an amount that another could
    be measured against.],
  label: "lst:wildcard-ops",
)[```vmir
e0: Ref := fresh
e1: Bool := fresh
e2: &[f] Int @ 1/1 := f(e0)
h0 := empty + e2 @ wildcard with fresh
e3: Int := *[h0] e2      // a read needs a share, not an amount
h1 := h0 - e2 @ wildcard // gives up an unspecified share
p0 := e1 ? wildcard : 0/1
h2 := h1 - e2 @ p0       // debits only where e1 holds
```]

A #vm[`wildcard`] is an amount that carries a sign and no magnitude: it states
that the share is positive and leaves its size open. It stands in the amount
slot with no operand of its own, because the magnitude is chosen when the
instruction executes rather than when it is emitted. Helium mints a fresh
symbolic real for each occurrence and assumes it positive.

That the real came from a wildcard is recorded beside the e-graph rather than
inside it. Congruence closure merges an e-class with every term it is proven
equal to, so a share that later coincides with a literal would sit in that
literal's class and answer to it. Helium therefore carries the wildcard mark on
the amount's own structure, where the instructions that take a different rule
for one read it directly, and where it survives every merge.

A Viper program may write #vi[`wildcard`] itself, and those 24 accesses do.
Nearly every wildcard Helium executes is one the translator introduced, in the
two regions where the program is known only to read: a function's body, and the
resource a heap-dependent function's precondition lowers to. Throughout those
regions the translator weakens each amount as it lowers it. A literal #vm[`0/1`]
stays #vm[`0/1`], a literal nonzero amount becomes a #vm[`wildcard`], and a
symbolic amount $p$ becomes

$ ternary(0 < p, "wildcard", "0/1") $

which is the gate of @lst:guarded-add with a wildcard in one arm. That third
case is what keeps a conditional footprint conditional, so a precondition
#vi[`requires b ==> acc(x.f)`] demands a share where #vi[`b`] holds and exactly
none where it does not. The rule is Silicon's default. Predicate bodies and
method preconditions keep their amounts as written, both describing permission
a program transfers rather than permission it reads through.

Addition takes a wildcard as it takes any amount, and consolidation is where the
missing magnitude shows. Helium builds no sum node when either side came from a
wildcard, because the e-graph carries no order theory for the reals and a sum
containing an unspecified share would be an opaque leaf that no later comparison
could use. Where one of the two summands is known positive, Helium mints a fresh
share and states that each summand is strictly smaller than it. The permission
bound of #pararef(<para:impl-location-axioms>, [Location axioms]) then finishes
the argument: a location already held at #vm[`1/1`] that takes a further
wildcard bounds a strictly larger share by #vm[`1/1`], which is a contradiction,
so that state is unreachable. Silicon returns the same verdict on it. Scaling
behaves the same way for the same reason, since a wildcard scaled by a positive
amount is a wildcard again, with no size to multiply. Silicon collapses
$w dot q$ to $w$ on that observation.

Subtraction is where the rule genuinely differs. The sufficiency obligation
$p_"held" >= p_"needed"$ of #pararef(<para:impl-heap-sub>, [Heap subtraction])
has nothing to weigh, so Helium proves instead that the location holds something
at all, $p_"held" > 0$, and leaves a fresh remainder assumed strictly smaller
than what was held. Line 6 of @lst:wildcard-ops raises the first and produces
the second, and line 8 succeeds against that remainder for exactly the same
reason.

Recording the remainder as the difference $p_"held" - w$ would say less than
this. With no order theory for the reals, a difference node supports neither
$0 < p_"held" - w$ nor $p_"held" - w < p_"held"$, which are the two facts a
later read and a later debit each turn on. The fresh remainder states both once,
at the point where they are known. This is Silicon's constrainable-ARP rule, and
it is the whole of what a wildcard has ever supported.

Line 7 gates a wildcard, and the demand it builds is walked arm by arm like any
other. Helium restricts the held amount to the arm it stands under, extends the
path condition with that arm's guard, and applies the wildcard rule at the leaf.
Line 8 therefore debits where #vm[`e1`] holds, and where it does not the arm is
a provable zero, which passes the held share through untouched and raises no
obligation at all. Because the demand's mark is read off its own structure
rather than out of the e-graph, a wildcard sitting under a guard is still
recognised as a wildcard demand.

The cost is that nothing records how much a wildcard debit took. A program that
gives up a wildcard and then asks for a stated fraction of the remainder cannot
be verified, and no run of wildcard debits ever pins the share down. That is
precisely the arithmetic a read-only region needs, which is why the translator
introduces wildcards there and leaves every other amount as the program wrote
it.

#pagebreak()
