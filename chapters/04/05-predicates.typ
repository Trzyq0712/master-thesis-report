#import "../../macros.typ": *

== Predicates <sec:impl-predicates>

Predicates serve a crucial role in expressing any more complex programs
in Viper. They are the mechanism by which
a program packages up some part of the heap and the claims about it,
and passes it around as a single unit without exposing its internal
structure. It is also a tool for describing memory structures of potentially
unbounded size, such as linked trees or lists.

Naturally, as any reasonable verifier, Helium has to provide support for
programming with predicates. In this section we describe how predicates are
viewed from the perspective of VMIR, and then explain how Helium implements
the concepts introduced by the new IR.

We start with a simple example of a predicate. @lst:cell-pred showcases
one of the simplest predicates in Viper one could define, namely a cell
that holds an integer field.

#viper(
  caption: [A cell predicate that hold a single integer field.],
  label: "lst:cell-pred",
)[```viper
field val: Int

predicate Cell(this: Ref) {
  acc(this.val, write)
}
```]

VMIR has no direct "predicate" primitive. Instead, a predicate is lowered
to a concept that we call a _resource_. A resource is similar to a
predicate, in that it is a named, parameterised pair of a heap fragment and
an assertion about it. @lst:cell-resource shows how the #vi[`Cell`] predicate
is lowered to a VMIR #vm[`resource`].

#vmir(
  caption: [A cell predicate translated to a VMIR resource.],
  label: "lst:cell-resource",
)[```vmir
resource Cell(e0: Ref) {
  e1: &[val] Int @ 1/1 := val(e0)
  h0 := empty + e1 @ 1/1 with self
  result: (h0, true)
}
```]

=== VMIR Resources

In principle, a resource's body is a sequence of instructions almost exactly
like these would look in a method body. At the end of the resource declaration,
the body yields a pair of values: a heap fragment and an assertion. In
case of @lst:cell-resource, the heap fragment will consist of a single chunk
holding an integer value at full permission, and the assertion will
simply state #vm[`true`] as there are no additional claims about the heap.

One crucial detail that follows directly from Viper's predicates, is the
requirement for the resources to be self-framing. This means that
the body of a resource must grant the permissions that are required for any
heap operations inside the resource body.

#lowering()[```viper
predicate PositiveCell(this: Ref) {
  this.val > 0
}
```][```vmir
resource PositiveCell(e0: Ref) {
  e1: &[val] Int @ 1/1 := val(e0)
  e2: Int := *[empty] e1
  e3: Bool := 0 < e2
  result: (empty, e3)
}
```]

#lowering(
  caption: [A predicate becomes a resource whose body yields a heap and a boolean.],
  label: "lst:pred-decl",
)[```viper
field val: Int

predicate Cell(this: Ref) {
  acc(this.val, write)
}
```][```vmir
function val(e0: Ref): &[val] Int @ 1/1

```]

The body is not an assertion. It is ordinary straight-line VMIR, and every
instruction in it appeared in @sec:impl-heap. #vm[`e1`] builds the address,
#vm[`h0`] adds a chunk for it, and #vm[`result`] delivers the pair. The heap half
is #vm[`h0`], the delta that holding a #vi[`Cell`] contributes. The boolean half
is #vm[`true`], because a body of permissions alone claims nothing.

One thing about that add is new. #pararef(<para:impl-heap-add>, [Heap addition]) gave
an add two ways to name its value, #vm[`fresh`] and an already computed
temporary. A body uses the third. #vm[`with self`] binds the chunk to the next
slot of the resource's own footprint, which is the value a user of the resource
supplies for it. We give the form no ordinal. A slot's position is a
consequence of where its add stands in the body. A body therefore cannot name a
slot out of order, and cannot name one it never declared.

A resource is more general than a predicate. Method contracts and function
preconditions become resources too (@sec:impl-calls, @sec:impl-functions),
because each of them is also a heap delta with a boolean claimed of it. One
construct therefore covers all three, and none of the heap instructions had to
learn which kind it was applied to.

#para[Derived members] <para:impl-derived> Naming a bundle costs two members the
source program never writes. We derive both from the declaration, as
@lst:pred-derived shows.

#vmir(
  caption: [The two members derived from #vi[`Cell`]: a snapshot type for what an
    instance remembers, and a location function for where it sits.],
  label: "lst:pred-derived",
)[```vmir
adt Cell@snap { #0(Option[Int]) }

function Cell@loc(e0: Ref): &[Cell] Cell@snap @ *
```]

An #vm[`@`] in a name marks a member as derived rather than declared. The
snapshot type #vm[`Cell@snap`] is what an instance stores, and
#pararef(<para:impl-snapshots>, [Snapshots]) below reads it off the body. The
location function #vm[`Cell@loc`] is @lst:field-decl at the predicate's arity,
and its three components are fixed the same way. Its group is the predicate's
name, so each predicate owns a partition. Its stored type is the derived
snapshot type. Its bound is #vm[`*`], following Viper, which lets a program hold
any amount of a folded predicate at once.

That last choice has a price. A partition of unbounded kind receives neither
axiom of #pararef(<para:impl-location-axioms>, [Location axioms]), so two
instances of one predicate are never proven distinct the way two full field
chunks are. Nothing forces the bound to be uniform. It is a component of a
location type like any other, so a predicate known to be exclusive could be
given #vm[`1/1`] instead and would then get both axioms. We leave how a declared
bound is to be checked for later work.

=== Reading the footprint off the body

#para[Snapshots] <para:impl-snapshots> The snapshot is what an instance
remembers of the delta it folded away. We read its type off the body
syntactically: every #vm[`with self`] contributes one member, in order, typed by
what is stored at the location added. @lst:pred-decl has one such add, so
#vm[`Cell@snap`] has one member at the type #vi[`val`] stores.

We leave #vi[`Cell`] as it is and grow a second predicate beside it,
#vi[`Node`], one conjunct at a time. The first conjunct added is a second field.

#lowering(
  caption: [A second conjunct becomes a second add, and a second member of the
    snapshot type.],
  label: "lst:pred-two-slots",
)[```viper
field next: Ref

predicate Node(this: Ref) {
  acc(this.val, write) &&
  acc(this.next, write)
}
```][```vmir
adt Node@snap { #0(Option[Int],
                   Option[Ref]) }

resource Node(e0: Ref) {
  e1: &[val] Int @ 1/1 := val(e0)
  h0 := empty + e1 @ 1/1 with self
  e2: &[next] Ref @ 1/1 := next(e0)
  h1 := h0 + e2 @ 1/1 with self
  result: (h1, true)
}
```]

A body is a sequence of adds threading one heap, so the conjunction's
associativity leaves no trace: how the source bracketed its conjuncts is not
recoverable from @lst:pred-two-slots and does not matter.

We mark the slots rather than counting the adds, and that is what makes the
reading exact. A body may contain adds that are not footprint, since an
#pararef(<para:impl-unfolding>, [`unfolding`]) inside it produces the chunks of
another predicate. Treating every add as a slot would be wrong there, and wrong
in the direction that silently changes what the predicate means. The check that
the marking is honest is a bijection. A body's heaps form a chain from
#vm[`empty`] to the one #vm[`result`] delivers, every add on that chain carries
#vm[`with self`], and every #vm[`with self`] lies on it. A scoped heap sits off
the chain and is excluded by construction.

The slots are #vm[`Option`]-typed, and the reason is @lst:pred-conditional
below. We lower a guarded #vi[`acc`] to an unconditional add at a guarded
amount. Whether a slot is present is then a question about that amount, not
about the instruction. A fold packs slot $i$ as
#vm[`0 < p ? Some(v) : None`], present exactly where positive permission was
contributed. Where the add was unconditional the condition folds to
#vm[`true`], and the wrapper costs an unconditional footprint nothing.

#para[The boolean half] Every body so far has claimed #vm[`true`]. A pure
conjunct is what puts something else there. We add one to @lst:pred-two-slots.

#lowering(
  caption: [A pure conjunct contributes no chunk. It becomes the resource's
    boolean instead.],
  label: "lst:pred-bool",
)[```viper
predicate Node(this: Ref) {
  acc(this.val, write) &&
  acc(this.next, write) &&
  this.val > 0
}
```][```vmir
resource Node(e0: Ref) {
  e1: &[val] Int @ 1/1 := val(e0)
  h0 := empty + e1 @ 1/1 with self
  e2: &[next] Ref @ 1/1 := next(e0)
  h1 := h0 + e2 @ 1/1 with self
  e3: Int := *[h1] e1
  e4: Bool := e3 > 0
  result: (h1, e4)
}
```]

#vm[`e3`] and #vm[`e4`] are a read and a comparison, and the read consults
#vm[`h1`], the heap the two adds produced. The conjunct is therefore evaluated against
permission the body has already granted itself. The snapshot type is unchanged,
since a pure conjunct adds no #vm[`with self`].

Viper requires a predicate body to be _self-framing_: it must grant the
permissions its own heap reads go through. The alternative we did not take is a
separate check for that property, run over the assertion before it is lowered.
@lst:pred-unframed is why we did not need one.

#lowering(
  caption: [The same body with the conjuncts swapped. The read now consults an
    empty heap and fails.],
  label: "lst:pred-unframed",
  target-lang: "lvmir",
)[```viper
predicate Node(this: Ref) {
  this.val > 0 &&          // fails
  acc(this.val, write) &&
  acc(this.next, write)
}
```][```vmir
resource Node(e0: Ref) {
  e1: &[val] Int @ 1/1 := val(e0)
  e2: Int := *[empty] e1   // fails
  e3: Bool := e2 > 0
  ...
}
```]

The read into #vm[`e2`] consults #vm[`empty`], because nothing has been added yet. It
fails the positivity obligation of
#pararef(<para:impl-heap-deref>, [Heap dereference]), and the failure is
reported as insufficient permission, exactly as the same read in a method body
would be. The lesson is that self-framing is not a discipline of its own. It is
the ordinary obligation a read carries, raised in a body instead of a method,
and Helium runs no separate pass for it.

#para[Ordered slots] A slot's address may depend on an earlier slot's value.
@lst:pred-nested replaces the pure conjunct of @lst:pred-bool with an instance
of the predicate of @lst:pred-decl, sitting at the reference the second slot
holds. The boolean half goes back to #vm[`true`] with it.

#lowering(
  caption: [A nested instance whose address is read out of the slot before it.],
  label: "lst:pred-nested",
)[```viper
predicate Node(this: Ref) {
  acc(this.val, write) &&
  acc(this.next, write) &&
  acc(Cell(this.next), write)
}
```][```vmir
resource Node(e0: Ref) {
  e1: &[val] Int @ 1/1 := val(e0)
  h0 := empty + e1 @ 1/1 with self
  e2: &[next] Ref @ 1/1 := next(e0)
  h1 := h0 + e2 @ 1/1 with self
  e3: Ref := *[h1] e2
  e4: &[Cell] Cell@snap @ *
     := Cell@loc(e3)
  h2 := h1 + e4 @ 1/1 with self
  result: (h2, true)
}
```]

#vm[`e3`] reads the second slot's value and #vm[`e4`] builds a location from it,
so the third slot's address exists only once the second slot has been produced.
This is why slots have an order at all, and it is the same order-dependence that
makes a Viper assertion self-framing. The third slot's type is
#vm[`Cell@snap`], so #vm[`Node@snap`] now holds a snapshot of another predicate,
and the nesting of the source shows up in the types.

Nothing about the rule changes with depth. A resource body is one level of
footprint and no more. What a #vm[`Cell@loc`] slot holds is another resource's
business, recovered only when something unfolds it.

#para[Conditional footprints] <para:impl-gate-split> A slot can also be present
only sometimes. @lst:pred-conditional guards the nested instance on the
reference being non-null, which is the shape any linked structure needs.

#lowering(
  caption: [An implication guards a slot. The guard moves into the permission
    amount, and the add stays unconditional.],
  label: "lst:pred-conditional",
)[```viper
predicate Node(this: Ref) {
  acc(this.val, write) &&
  acc(this.next, write) &&
  (this.next != null ==>
     acc(Cell(this.next), write))
}
```][```vmir
resource Node(e0: Ref) {
  e1: &[val] Int @ 1/1 := val(e0)
  h0 := empty + e1 @ 1/1 with self
  e2: &[next] Ref @ 1/1 := next(e0)
  h1 := h0 + e2 @ 1/1 with self
  e3: Ref := *[h1] e2
  e4: Bool := e3 != null
  e5: Real := e4 ? 1/1 : 0/1
  e6: &[Cell] Cell@snap @ *
     := Cell@loc(e3)
  h2 := h1 + e6 @ e5 with self
  result: (h2, true)
}
```]

The guard becomes the amount #vm[`e5`], and the add runs whatever that amount
turns out to be. Keeping the add unconditional is what lets the
footprint be read off the body syntactically at all. A guarded instruction would
make the slot count depend on a path condition, and a snapshot type cannot
depend on a path condition. The cost is that presence becomes an arithmetic
question rather than a structural one. That is why the slot is
#vm[`Option`]-typed, and why an obligation about it may need its amount decided
first.

#para[Recursion] One further change makes the predicate recursive, and it is a
change of a single name. Replacing #vi[`Cell`] with #vi[`Node`] in
@lst:pred-conditional gives the usual linked-list predicate. Its body is the
same instructions with #vm[`Node@loc`] building the third address. The snapshot
type becomes recursive with it, holding an #vm[`Option[Node@snap]`] at its third
member.

Nothing in the verifier needs a depth limit or a cycle check for this, because
the body still describes one level. An address is built by a call to
#vm[`Node@loc`], and forming an address needs no certificate, so Helium records
no dependency of #vi[`Node`] on itself. A recursive predicate is therefore
verified in one ordinary pass, like any other. One shape is rejected: a
#vi[`fold`] or #vi[`unfold`] of #vi[`Node`] inside #vi[`Node`]'s own body. That
is a genuine cycle, and Helium reports it as a circular resource dependency.

=== Verifying a resource

A resource is checked once, at its declaration, under fresh symbolic parameters.
The body is walked instruction by instruction, and every obligation it raises
goes to @sec:impl-execution with no special handling. The reads in
@lst:pred-bool and @lst:pred-unframed are the same reads a method body would
raise. Well-formedness of a predicate is therefore not a separate discipline.

Two kinds of instruction never appear in a body. There are no assignments and no
havocs, because the assertion grammar a body is lowered from has five nodes and
none of them is a statement. And no add in a body binds #vm[`fresh`], because
the lowering emits #vm[`with self`] for every #vi[`acc`] it meets inside a
resource. That second restriction is the load-bearing one. A body that minted a
value of its own would claim something about a value nobody supplied. The same
resource used twice would then mean two different things. Freshness is a
property of the instruction that _uses_ a resource, never of the resource. A body
is therefore a recipe over its parameters rather than a piece of program.

#para[Slots and recipes] <para:impl-slot-recipes> None of the body survives
verification as a body. What Helium keeps is a small record of _recipes_, which
is the same construct a function body leaves behind in
#pararef(<para:impl-recipes>, [Recipes]) of @sec:impl-functions. There are two
per footprint slot, one building the slot's address and one building its
permission amount, and one more for the body's boolean. Each is stored alongside
the slot's location kind and element type.

For @lst:pred-conditional that is three address recipes, three permission
recipes, and a boolean recipe that is the constant #vm[`true`]. Nothing of the
body's execution is retained: not the heap it threaded, not the instructions
that threaded it.

A recipe is a sequence of pure steps in a space of its own, seeded by either a
parameter or the value of an earlier slot. The heap reads of @lst:pred-nested
and @lst:pred-conditional do not survive into one. Slot three of either body
reads the second slot out of the heap. Its recipe is seeded by that slot's value
directly, because the walk already holds it by then. That second kind of seed is
why the recipes are ordered, and why a slot may only look backwards.

Recipes hold no e-classes, no heap and no path condition. Rebuilding one at a
use site therefore adds terms and imports nothing. Whatever was merged while the
body was being verified stays where it was proved. A user of the resource
derives what it needs from what it can itself establish. We did not choose this
for speed alone. A body is verified under its own parameters, so importing its
merges would let a client inherit facts it has not established.

A resource consequently has no presence in the state at all until something uses
it. The recipes describe the delta, and a use is what builds it. The rebuild is
cheap enough to do at every use because it is add-only, so Helium normalises
only where a rebuild actually introduced a node. A rebuild that added nothing
named only terms the state already had. Normalising once per slot regardless
re-runs the whole rule set over the graph, and cost about 3.5 times as much when
we measured it.

The price of compiling the body once is that a recipe is fixed when the resource
is checked. Nothing at a use site can specialise it the way a verifier that
re-executed the assertion in the state at hand could.

=== Folding and unfolding

Taking and giving back an instance needs nothing new. An #vi[`acc`] naming a
predicate is an #vi[`acc`] like any other. It lowers to the add and the subtract
of @sec:impl-heap at the location #vm[`Cell@loc(c)`], carrying a snapshot rather
than a field's stored value. Neither direction looks at the
body, which is why -lst:pred-fails failed. Undoing that is what the rest of this
subsection does.

#para[The resource operations] <para:impl-resource-ops> VMIR has two further
heap instructions, #vm[`inhale`] and #vm[`exhale`], and they take a whole
resource rather than one location. Each walks the slots in the body's order,
rebuilds every address and every amount at the actual arguments, and applies the
delta one slot at a time. The body's boolean comes with the walk: an
#vm[`exhale`] asserts it, an #vm[`inhale`] assumes it.

They are the two directions of one walk, and they take their values the way the
slot-level pair does. An #vm[`exhale`] is read-shaped. It reads each slot's
value out of the heap on its way past and yields the snapshot assembled from
what it read. An #vm[`inhale`] is write-shaped. It has no values of its own, so
it takes a bind point, and what is bound there is a whole snapshot. Slot $i$ of
the walk is bound to member $i$ of that snapshot, which is what #vm[`with self`]
in the body named.

One obligation is stricter here than at a slot. A resource operation demands

$ p > 0 $

rather than the non-negativity an add and a subtract demand. The reason is the
boolean. At zero permission the operation would assert or assume a claim about
chunks it neither received nor gave, which is a claim about nothing. Viper
rejects the same programs. The slot-level pair keeps $p >= 0$, because it says
nothing at all and because a guarded #vi[`acc`] is exactly zero on the path its
guard excludes.

A #vi[`fold`] exchanges the chunks the body's delta names for the instance
itself, and the instance it produces remembers what those chunks held. An
#vi[`unfold`] runs the exchange the other way. @lst:fold-unfold is both.

#lowering(
  caption: [Neither statement is one instruction. Each is a resource operation
    paired with a slot-level add or subtract, sharing one temporary.],
  label: "lst:fold-unfold",
)[```viper
fold acc(Cell(c), write)
//@
unfold acc(Cell(c), write)
```][```vmir
h1, e1: Cell@snap := h0
        exhale Cell(e0) @ 1/1
h2 := h1 + Cell@loc(e0) @ 1/1
      with e1
//@
h1, e1: Option[Cell@snap] := h0
        - Cell@loc(e0) @ 1/1
e2: Cell@snap := unwrap(e1)
h2 := h1 inhale Cell(e0) @ 1/1
      with e2
```]

The fold exhales the resource first. The walk subtracts each slot's permission,
raising the sufficiency obligation of
#pararef(<para:impl-heap-sub>, [Heap subtraction]) as it goes, reads the value
the heap held there, and asserts the body's boolean. Asserting is right, because
a fold claims the assertion holds of what it is folding away. The walk yields
the assembled snapshot, and the add on the next line puts one chunk at the
predicate's own location bound to it.

The unfold is the same two instructions with every direction reversed. The
predicate chunk is subtracted first, which hands back the snapshot it held. The
resource is then inhaled bound to that snapshot, so each slot is added back with
its value taken from the matching member. The body's boolean is assumed rather
than asserted. Assuming is right in this direction, because holding the
instance is what entitles the program to the claim.

The order is forced in both directions, and by permission accounting rather than
by anything about the boolean. The predicate chunk must be gone before the
body's slots are produced, and the slots must be gone before the chunk is
produced. Otherwise a predicate whose body mentions its own instance, which is
@lst:pred-conditional with #vi[`Node`] in place of #vi[`Cell`], would briefly
hold both. We write each statement as a pair so that the bracketing is expressed
positionally.

Which half carries the boolean is the reason to pair them this way round. The
chunk-side instruction is the slot-level add or subtract, which asserts and
assumes nothing, so the body's boolean can only land on the resource side. It is
then asserted by the fold and assumed by the unfold, at the right polarity in
each direction by construction. Had the resource operation gone on the chunk
side, one half of each pair would assume a boolean the other half had just been
asked to prove.

The obvious alternative is a single #vi[`fold`] instruction doing both halves at
once. It would save the seam described next. What it would cost is the one
property the pair gets for free: the snapshot an unfold reproduces the body from
is the same value the chunk held. Here that holds because it is literally the
same temporary, #vm[`e1`] threaded into #vm[`e2`] and then into the inhale. A
single instruction would have to carry that equation as a side condition, and
would have no way to state it after the fact. The lesson is that the equation
between an instance and its footprint is better made emergent than maintained.

#para[The seam] The #vm[`unwrap`] in @lst:fold-unfold's unfold half is the one
coercion in either pair. A subtract yields an #vm[`Option`], because at zero
permission it removes nothing and has nothing to report. An inhale takes a plain
snapshot, because it demands positive permission and so cannot be reached where
nothing was there. The two obligations meet at that line.

It is not a proof obligation. Presence is built from the amount the instruction
was written with, #vm[`0 < 1/1`] here, so it folds to #vm[`true`] and the yield
is concretely a #vm[`Some`]. The unwrap is then peeled by a reduction of
@sec:impl-adts before anything is asked to prove anything. The same holds
structurally where the amount is a #vm[`wildcard`], a wildcard being positive by
construction. Emitting an assertion that the yield is present would put a proof
search where there is currently a lookup.

That reduction is also what makes the round trip exact. A fold packs slot $i$'s
value #vm[`v`] as #vm[`Some(v)`], and an unfold recovers it as an
unwrap of a member of that same construction. Both steps are rewrite rules of
the core (@sec:impl-adts), so the recovered term is not merely provably equal to
#vm[`v`]. It is #vm[`v`], in the same e-class, reached by two reductions and no
obligation. A field read before a fold and the same field read after the
matching unfold are then the same term. An assertion relating the two is
discharged by comparing class identifiers.

@lst:pred-succeeds is -lst:pred-fails with the unfold in place.

#viper(
  caption: [The opening failure repaired. One #vi[`unfold`] exchanges the
    instance for the chunk its body names.],
  label: "lst:pred-succeeds",
)[```viper
method use(c: Ref)
  requires acc(Cell(c), write)
{
  unfold acc(Cell(c), write)
  assert acc(c.val, write)   // succeeds
}
```]

The unfold subtracts the chunk at #vm[`Cell@loc(c)`] and inhales the resource
bound to what it held, which adds a chunk at #vm[`val(c)`] holding #vm[`1/1`].
The assertion then resolves that location the way @sec:impl-heap resolves any
location, and finds full permission.

#para[Unfolding in an expression] <para:impl-unfolding> Viper also spells the
exchange as an expression. #vi[`unfolding acc(P(args), p) in e`] opens the
instance for the duration of #vi[`e`], and it is what a heap-dependent function
body is built from. @lst:unfolding is one.

#lowering(
  caption: [An #vi[`unfolding`] lowers to the unfold half alone. The enclosing
    expression keeps the heap it already named.],
  label: "lst:unfolding",
)[```viper
function get(this: Ref): Int
  requires acc(Cell(this), write)
{
  unfolding acc(Cell(this), write)
    in this.val
}
```][```vmir
h1, e1: Option[Cell@snap] := h0
        - Cell@loc(e0) @ 1/1
e2: Cell@snap := unwrap(e1)
h2 := h1 inhale Cell(e0) @ 1/1
      with e2
e3: &[val] Int @ 1/1 := val(e0)
e4: Int := *[h2] e3
```]

Only the unfold half is emitted. The sub-expression is lowered against
#vm[`h2`], the heap that half produced, and the read into #vm[`e4`] consults it.
Nothing folds the instance back, and nothing needs to. Heaps are values, the
enclosing expression already names the heap it wants, and #vm[`h2`] is simply
not mentioned again. Scoping an effect is thereby a question of which temporary
an instruction reads.

One consequence is worth stating. Because #vi[`unfolding`] is an expression, it
can sit under a condition that no statement does, inside a ternary arm for
instance. Its two instructions are then the only heap instructions that may
carry a path condition finer than their block's. The effect is scoped and
fabricates no permission, so this is benign. It is nonetheless the one place
where the block granularity @sec:impl-cfg relies on is not literally true.

=== Predicates without a body

A predicate may be declared with no body, and Viper gives such an instance no
relation to any footprint. @lst:pred-abstract is one, and its derived members
differ in exactly one respect.

#lowering(
  caption: [An abstract predicate. With no delta to read a snapshot type off,
    the snapshot becomes an opaque domain.],
  label: "lst:pred-abstract",
)[```viper
predicate Opaque(this: Ref)
```][```vmir
resource Opaque(e0: Ref)

domain Opaque@snap

function Opaque@loc(e0: Ref)
  : &[Opaque] Opaque@snap @ *
```]

There is no body, so there are no #vm[`with self`] adds, so there is nothing to
read a member list off. The snapshot type is an opaque #vm[`domain`] instead of
an #vm[`adt`], and values of it are only ever passed around, never constructed
and never projected. Everything else is unchanged: a location function at the
same arity, into a partition of the same kind, and an instance added and
subtracted exactly as @lst:fold-unfold's chunk-side halves do.

What is lost is only the relation to a footprint. With no body there is no walk
for a resource operation to run, so there is nothing to fold or unfold. Such an
instance can be held, given away and taken back, and nothing more. Helium skips
such a declaration during verification, since it states nothing to prove.

=== Comparison with Silicon

Silicon keeps a predicate as the assertion the programmer wrote, and re-runs its
produce and consume rules over that assertion at every use. Each #vi[`acc`] in
it has its receiver and its permission expression evaluated afresh in the state
at hand, which may branch, may query the solver, and may raise obligations of
its own @silicon[Section 3.3]. Compiling the body to recipes is that walk done
once, at the declaration, where its obligations are discharged against the
body's own state. A use then rebuilds terms instead of re-executing an
assertion, and pays no branching for it.

The two verifiers also differ in what a snapshot is. Silicon's snapshots live in
a single uninterpreted sort. A footprint of several locations is a right-nested
tree of #vm[`Combine`] pairs, taken apart by #vm[`First`] and #vm[`Second`]. A
value of any other sort enters and leaves that tree through sort wrappers.
What a slot is cannot be recovered from such a term. The shape of the tree is a
convention the encoding maintains, the projections are functions the solver
reasons about axiomatically, and reading a field out of a nested predicate means
composing a path of projections and unwrappers.

We give each resource its own #vm[`adt`] instead, which makes that structure
part of the type. A slot is a member at a known type, so a projection that does
not correspond to a slot cannot be written. No wrapping is needed either,
because the member already has the sort the location stores. The exactness
argument above is what this buys concretely. Silicon connects a fold to its
unfold by emitting snapshot equalities and letting the solver relate them, and
here there is nothing to relate.

#note[
  *Listing notation.* The listings in this section write #vm[`Cell@loc`] for a
  predicate's location function, following the rest of the chapter. The
  implementation prints the predicate's bare name there, and writes
  #vm[`Cell@addr`] only in its derived-member dump. Worth settling in one pass
  over the chapter rather than per section.
]
