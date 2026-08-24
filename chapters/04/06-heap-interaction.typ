#import "../../macros.typ": *

== Interacting with the Heap <sec:impl-heap-interaction>

These four instructions are the hot path: #vi[`exhale`], #vi[`unfold`] and
#vi[`fold`] are among the most frequent statements a Prusti encoding contains,
and every #vi[`acc`] assertion any of them carries is what the operations below
ultimately do to the heap. Whatever else the verifier is good at, it has to be
good at this.

A program that owns a field takes permission to it, writes through it, reads back
what it wrote, and gives permission away again. The following four lines do all of
that, over the field @sec:impl-fields lowered.

#viper(
  caption: [Taking permission to one field in two pieces, writing it, reading it back, and giving half of it away.],
  label: "lst:heap-ops",
)[```viper
inhale acc(x.f, 1/3) && acc(x.f, 2/3)
x.f := 42
assert x.f > 10
exhale acc(x.f, 1/2)
```]

The fractions are chosen deliberately: a Prusti encoding never states an
#vi[`acc`] at anything but #vi[`write`], so a listing built from one would
exercise the arithmetic at exactly one value and hide what the operations do.
They are split here for that reason and for no other.

The four statements are taken one at a time below, each becoming one kind of
instruction. The listings are VMIR-lite in two respects: the receivers keep
their source names rather than becoming numbered values, and the computation of
an address is written where it is used rather than on a line of its own.

#para[Taking permission] <para:impl-threading> The heap is named by a temporary
of its own sort, and an instruction either produces one or consults one.
Each conjunct of an assertion is applied on its own, threading
one heap into the next, so the #vi[`inhale`] of @lst:heap-ops becomes one add per
#vi[`acc`]:

#lowering(
  caption: [An #vi[`inhale`] becomes one add per #vi[`acc`], threading the heap.],
  label: "lst:heap-inhale",
  target-lang: "lvmir",
)[```viper
inhale acc(x.f, 1/3)
    && acc(x.f, 2/3)
```][```lvmir
h0 := empty + f(x) @ 1/3
      with fresh
h1 := h0 + f(x) @ 2/3
      with fresh
```]

Both instructions of @lst:heap-inhale are _heap-producing_: each takes a heap and
yields a new one. The chain starts at #vm[`empty`], since this is the first
statement of a body. The location is #vm[`f(x)`],
the location function of @sec:impl-fields applied to the receiver, and that is the
whole of what #vi[`x.f`] means in this position; elsewhere it means the value
stored there, which has to be read out of a particular heap.

The trailing #vm[`with`] is the instruction's bind point. An add
is the one direction that has no value of its own. It puts permission somewhere
the program may not have held any, so the value has to be a parameter of the
instruction rather than something the verifier decides.

What an add does with the bind depends on whether the partition already holds a
chunk at the location. If it does not, a new chunk is created holding the value
the bind supplies — for #vm[`fresh`], a new e-class with nothing assumed about it.
If it does, the two are the same chunk: the amounts add, the value stays as it
was, and the bind is not consulted. That is the second add of
@lst:heap-inhale. The first created a value and gave it #vm[`1/3`]; the second
finds #vm[`f(x)`] already present in the partition, leaves the value alone, and
raises the amount to
#vm[`1/3 + 2/3`], which folds to #vm[`1/1`]. Two conjuncts naming one location
produce one chunk, not two, which is what makes the held amount at a location a
single term to compare against. An add can never fail for want of permission.

What it can fail on is the amount itself. Every #vi[`acc(l, p)`] carries the side
condition

$ p >= 0 $

whichever direction it is applied in, since an assertion naming a negative
fraction denotes nothing, and the verifier raises it as an obligation before the
add or subtract it belongs to. The amounts of @lst:heap-inhale are literals and
answer it on the spot; one computed from program values does not, and it is
checked like anything else. Adding permission is thereby
unconditional in the heap and conditional only on its own assertion being
meaningful.

The merge happens here only because the two locations are syntactically the same
and so land in the same e-class immediately. Had the assertion been
#vi[`acc(x.f, 1/3) && acc(y.f, 2/3)`], the add would have produced two chunks in
the partition, and they would still merge later if #vi[`x == y`] were derived —
the e-classes collapse, and the fold that adds the amounts and reconciles the two
values under the agreement axiom is
#pararef(<para:impl-consolidation>, [Consolidation]) of @sec:impl-heap. Nothing an
add does depends on knowing the aliasing up front; it is a lookup that happens to
succeed early in this example.

An assignment produces a heap in which one location holds a new
value and every other chunk is untouched:

#lowering(
  caption: [An assignment replaces one chunk's value and frames the rest.],
  label: "lst:heap-assign",
  target-lang: "lvmir",
)[```viper
x.f := 42
```][```lvmir
h2 := h1 assign(f(x), 42)
```]

Executing it takes three steps. The location is _resolved_ first: #vm[`f(x)`] is
taken to its canonical e-class, the partition of #vm[`h1`] that this location
belongs to is scanned for chunks at that e-class, and any that have since
collapsed into one are folded together
(#pararef(<para:impl-consolidation>, [Consolidation])). If nothing answers, the
amount held is zero and the write fails for want of permission. Second, the amount
of the chunk found is checked against the bound $b$ of that partition — #vm[`1/1`]
for field-originated locations, which is why a program holding a half cannot store
through one; here the demand is met by the merged chunk, since either piece alone
would have been too little. Third, the value is replaced: the chunk keeps its
location and its amount, its value becomes the e-class of the term written, and no
other chunk is examined at all. The fresh value created by the first add is
replaced without ever having been read, which is the usual outcome for a value
inhaled and then overwritten.

The obligation the second step raises is

$ p_"held" >= b $

under the instruction's path condition, and it is an obligation like any other,
with nothing special to the heap about it. It is an inequality rather than an equality because an amount
above the bound leaves the state inconsistent by the axiom of @sec:impl-heap, so
letting the write through costs nothing.

The bound is what makes the check mean exclusivity, so a location of a kind
bounded by #vm[`*`] can never be written to: with no $b$, no amount rules out a
second holder of the same location, and exclusivity is unprovable in principle
rather than merely unproven here. Nothing is lost by it, since the kinds left
unbounded are the ones nothing writes through directly — predicate instances
(@sec:impl-predicates), which are mutated by unfolding them and writing to the
fields inside.

A write is not primitive in the way the others are. It could be desugared to a
subtract of $b$, an add of $b$ — which creates a fresh value, the
subtract having dropped the chunk — and an assumption equating that value with the
one written. That means the same thing, but it tears a chunk down and rebuilds it,
introduces an e-class nothing needs, and leaves an equality for congruence closure
to merge, where #vm[`assign`] replaces the value in place after a single lookup.
Mutation is everywhere, so the difference is paid on the hot path.

A read is the first instruction here that needs a value out of a heap. It is
_heap-dependent_: it produces an ordinary value and consults a heap without
producing one.

#lowering(
  caption: [A read names the heap it consults and yields an ordinary value.],
  label: "lst:heap-read",
  target-lang: "lvmir",
)[```viper
assert x.f > 10
```][```lvmir
e0: Int := *[h2] f(x)
e1: Bool := e0 > 10
assert e1
```]

The location is resolved as it is for a write, but the obligation is only
_positivity_,

$ p_"held" > 0 $

again under the path condition: any amount above zero entitles the program to
look, and where no chunk answers the amount held is zero, so reading without
permission is caught by the same check.

Framing is then a matter of which temporary the instruction mentions. The read of
@lst:heap-read names #vm[`h2`], which is by construction what the assignment
produced, so it reaches what was just written with no framing argument to make.

#para[Giving permission back] <para:impl-subtract> An #vi[`exhale`] subtracts what
the assertion names, with the fraction carried across unchanged:

#lowering(
  caption: [An #vi[`exhale`] subtracts the amount the assertion names.],
  label: "lst:heap-exhale",
  target-lang: "lvmir",
)[```viper
exhale acc(x.f, 1/2)
```][```lvmir
h3, _ := h2 - f(x) @ 1/2
```]

A subtract has a second result, which is why @lst:heap-exhale binds a pair.
It is the counterpart of the bind point, and it points the other
way. An add is told what value to put somewhere. A subtract _discovers_ what value
was there and hands it back. The one construct that wants it is an unfold
(@sec:impl-predicates), which passes it straight into the instruction that reproduces
the footprint, and that is the whole reason the yield exists.

What is handed back is an #vm[`Option`], #vm[`Some(v)`] exactly where the amount
taken away is positive, for the same reason a snapshot slot is
(@sec:impl-predicates): a subtract of no permission removes nothing and so has
nothing to report. This is the only position in the instruction set where a value
is optional, and the asymmetry is deliberate — presence is _discovered_ here,
whereas a bind point _supplies_ a value and the instruction works out for itself,
from the amount, whether a chunk results.

@sec:impl-functions has a case where blanking a result changes the instruction's
meaning rather than merely its cost.

A subtract can fail in two ways. It carries
the same non-negativity side condition on the amount its #vi[`acc`] names, and it
raises one of its own, that enough was held to take that amount away:

$ p_"held" >= p_"needed" $

with the amount being taken on the right. Where the second cannot be shown the
instruction reports insufficient permission rather than producing a heap. What
survives an instruction that does go through is the chunk with its
amount replaced by the term
$p_"held" - p_"needed"$, built and left unevaluated; here that is #vm[`1/2`], so
the chunk stays. The chunk is dropped only where the difference is _provably_
zero, and that is an optimisation rather than a matter of soundness: a chunk
holding no permission is inert.

#if not excerpt-mode [
  #para[Conditional permission amounts] <para:impl-amounts> The harder case is an
  access taken only conditionally. A chunk's amount is an e-class exactly as its
  location and its value are, so it may be an arbitrary term, and a guarded inhale
  stays a single unconditional add.

  #lowering(
    caption: [A guarded access gates the amount, not the instruction.],
    label: "lst:guarded-add",
    target-lang: "lvmir",
  )[```viper
  inhale p > 0 ==> acc(x.f, p)
  ```][```lvmir
  e0: Bool := p > 0
  e1: Real := e0 ? p : 0/1
  h1 := h0 + f(x) @ e1 with fresh
  ```]

  The amount inhaled is the program's own #vi[`p`], and the condition is a fact
  about it. With #vm[`h0`] the heap in hand, the chunk is added unconditionally and
  the guard is pushed into the amount, which is exactly an add under a ternary whose
  other arm is no permission at all. The _shape_ of the heap is then independent of
  the condition — the same chunks sit in the same partitions whichever way
  #vi[`p > 0`] goes — so the verifier never case-splits to find out what it is
  holding, and a guarded access costs a ternary rather than a second heap.

  Conjoining the condition instead of implying with it is a different assertion, and
  the two lower apart:

  #lowering(
    caption: [A conjoined condition gates the delta and is assumed at the end.],
    label: "lst:conjoined-add",
    target-lang: "lvmir",
  )[```viper
  inhale p > 0 && acc(x.f, p)
  ```][```lvmir
  e0: Bool := p > 0
  h1 := <e0> h0 + f(x) @ p with fresh
  assume e0
  ```]

  The #vm[`<e0>`] is a guard on the instruction, and it means what the ternary of
  @lst:guarded-add means — a guarded delta is the delta with its amount gated,
  $ternary(e_0, p, 0)$ — written the way @sec:impl-cfg writes a block's path
  condition. The pure conjunct is assumed once, after the deltas rather than before
  them, since an assertion is self-framing and a pure conjunct may read through
  permission an earlier conjunct granted; the gate then reduces to #vm[`p`] on the
  next line, so the add is unconditional in effect.

  @lst:conjoined-add gives #vi[`p`] unconditionally and _also_ learns that it is
  positive, which every later instruction on the path can use; @lst:guarded-add
  learns nothing and gives an amount that is only as good as #vi[`p > 0`] later
  turns out to be. A read at the location goes through immediately after
  @lst:conjoined-add, its positivity obligation being exactly the fact just assumed,
  and after @lst:guarded-add only where #vi[`p > 0`] can be established. The pure
  conjunct is the informative one, the guard the expensive one, and reading one for
  the other is the standard way to be surprised by a Viper specification. Neither
  form licenses a write, since neither says anything that puts #vi[`p`] at the bound.

  What it costs instead is that a later demand at that location is an obligation on
  an arithmetic term, which the representation then recovers. A demand of
  #vm[`p`] against a held #vm[`e0 ? p : 0/1`] is not decidable as arithmetic, but
  under an assumed #vm[`e0`] the ternary reduces to #vm[`p`] by the same rule that
  simplifies any conditional, and the obligation is then an amount against itself:
  one e-class compared with the same one, closed without any theory of rationals.

  One amount does not gate this way, and it is the exception @sec:impl-wildcards is
  about. A #vi[`wildcard`] has no term to push a condition into, so a guarded
  wildcard is gated one level up — the ternary is over the permission rather than
  inside it — and the demand it raises is structural rather than arithmetic.

  A demand that cannot be discharged is reported as
  insufficient permission, which is a failure to prove rather than a loss of
  information: the chunk is still in its partition with its amount as a term, the
  path condition is still exact, and the obligation is still a pair of e-classes,
  so it could be handed to a procedure that reasons about rationals. Two
  escalations sit before that report and need machinery introduced later — a
  demand may have to be met by a _sum_ over chunks only conditionally at one
  location (@sec:impl-cfg), and the location demanded may meet the one held only
  under an equality a saturation has yet to derive (@sec:impl-calls).

  Where the limit actually lies is worth naming, because it is not where the
  representation might suggest. A demand of a fraction _different_ from the amount
  held is discharged whenever both are literals — #vi[`inhale acc(x.f, 3/4)`]
  followed by #vi[`exhale acc(x.f, 1/2)`] leaves #vm[`1/4`] by constant folding
  alone. A demand at a conditionally-held location is discharged whenever the
  guard is assumed, by the ternary reduction just described. The non-negativity
  side condition on a symbolic amount discharges too: from an assumed
  #vi[`p > 0`] the obligation #vm[`!(p < 0)`] follows by asymmetry of a strict
  order, $a < b => not (b < a)$, which the rule set states alongside the fold of
  #vm[`<`] on literals — the same rule @sec:impl-wildcards leans on for its own
  sufficiency check. What is left outside the rule set is the general arithmetic
  gap of the tiered prover: an inequality that needs reasoning about a sum of
  terms rather than about one term's own sign, which no permission amount here
  raises on its own.
]
