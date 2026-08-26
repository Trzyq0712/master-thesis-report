#import "../../macros.typ": *
#import "../../figures/resource-recipes.typ": resource-recipes

== Predicates <sec:impl-predicates>

Predicates are what lets a Viper program express anything of size. They are the
mechanism by which a program packages up some part of the heap and the claims
about it, and passes it around as a single unit without exposing its internal
structure. They are also the tool for describing memory structures of
potentially unbounded size, such as linked lists or trees.

Helium therefore has to support programming with predicates. This section
describes how VMIR represents them, and how Helium implements the concepts that
representation introduces.

@lst:cell-pred is one of the simplest predicates one could define in Viper, a
cell that holds a single integer field.

#viper(
  caption: [A predicate packaging a single integer field behind a name. It is
    the resource the rest of the section builds on.],
  label: "lst:cell-pred",
)[```viper
field val: Int

predicate Cell(this: Ref) {
  acc(this.val, write)
}
```]

Hiding the contents of a predicate is what makes it useful, and it is also what
makes it awkward to work with. @lst:pred-fails holds an instance of #vi[`Cell`]
and asks for the field inside it.

#viper(
  caption: [Holding a predicate instance says nothing about the field inside it.],
  label: "lst:pred-fails",
)[```viper
method use(c: Ref)
  requires acc(Cell(c), write)
{
  exhale acc(c.val, write)   // fails
}
```]

Each of the four heap instructions of @sec:impl-heap acts at a single location
it is given. The precondition places one chunk on the heap, at the location that
stands for the instance, and that chunk does not sit at #vm[`val(c)`]. The
exhale on the last line therefore finds no permission there, and fails its
sufficiency obligation. Recovering the field costs an #vi[`unfold`], which we
describe in @sec:impl-fold.

=== VMIR resources

VMIR has no direct "predicate" primitive, and the reason is that a predicate is
not the only thing in Viper with a predicate's shape. A method contract and a
function precondition are also permission to some part of the heap together with
a claim about what that part holds, and a verifier has to take and give back all
three in the same way. VMIR therefore provides one construct general enough to
carry all of them, which we call a _resource_: a named, parameterised pair of a
heap delta and a boolean claimed of that delta. Predicates are lowered to
resources, and so are the contracts of @sec:impl-calls and @sec:impl-functions.
Each heap instruction treats all three alike.

@lst:cell-resource shows how the #vi[`Cell`] predicate is lowered to a VMIR
#vm[`resource`].

#vmir(
  caption: [The #vi[`Cell`] predicate of @lst:cell-pred as a VMIR resource. The
    field declaration above it becomes the location function #vm[`val`].],
  label: "lst:cell-resource",
)[```vmir
function val(e0: Ref): &[val] Int @ 1/1

resource Cell(e0: Ref) {
  e1: &[val] Int @ 1/1 := val(e0)
  h0 := empty + e1 @ 1/1 with self
  result: (h0, true)
}
```]

The body of a resource is a sequence of instructions, almost exactly like the
ones a method body is made of. Every instruction in @lst:cell-resource has
appeared in @sec:impl-heap. #vm[`e1`] builds the address, #vm[`h0`] adds a chunk
for it, and #vm[`result`] delivers the pair the declaration yields. The delta of
#vi[`Cell`] is therefore a single chunk holding an integer at full permission,
and its boolean is #vm[`true`], because a body of permissions alone claims
nothing. The add carries one piece of syntax that no method body uses,
#vm[`with self`]. It marks the chunk as one the resource itself contributes. The
chunks a body marks this way are its _footprint_, and
#pararef(<para:impl-snapshots>, [Snapshots]) makes the marking precise.

#para[Associated members] <para:impl-derived> Every VMIR resource implicitly
defines two associated members. The first is a snapshot type, which records the
values the resource holds while it is folded. The second is a location function,
which names the place a folded instance occupies in the heap. @lst:pred-derived
shows both for the #vi[`Cell`] resource of @lst:cell-resource. An #vm[`@`] in a
name marks a member as derived rather than declared.

#vmir(
  caption: [The two members derived from #vi[`Cell`]: a snapshot type for what an
    instance remembers, and a location function for where it sits.],
  label: "lst:pred-derived",
)[```vmir
adt Cell@snap { #0(Option[Int]) }

function Cell@loc(e0: Ref): &[Cell] Cell@snap @ *
```]

The snapshot type is an #vm[`adt`] with a single constructor, one member per
chunk of the footprint. #vi[`Cell`] contributes one chunk, so #vm[`Cell@snap`]
has one member. #pararef(<para:impl-snapshots>, [Snapshots]) derives the member
list and the types on it.

The location function maps the resource's arguments to a location, exactly as a
field declaration does at arity one. Its group is the resource's name, so each
resource owns a partition of the heap. Its stored type is the derived snapshot
type, so a chunk in that partition holds a whole instance. Its bound is
#vm[`*`], because Viper lets a program hold any amount of a folded predicate at
once and we match that.

The bound is the one component of the three that we would rather not fix. A
partition of unbounded kind receives neither axiom of
#pararef(<para:impl-location-axioms>, [Location axioms]), so two instances of
one resource stay possibly equal where two full field chunks would be proven
distinct. Some resources admit a tighter bound than #vm[`*`]. A bound is a
component of a location type like any other, and the machinery treats each
partition on its own, so a frontend that knew which resources those are would
recover both axioms for them. VMIR does not currently offer that choice: the
bound of a resource's location function is unbounded by construction rather than
by declaration, and we leave making it declarable to future work.

=== Lowering a predicate body

Deriving the snapshot type, and later running a resource operation, both need
the footprint: which of a body's adds are the chunks the resource contributes.
We read that list off the body syntactically. This subsection describes the
reading, and the shapes of body it has to cope with.

#para[Snapshots] <para:impl-snapshots> The snapshot is what an instance
remembers of the delta it folded away. It is built out of the adds the body
marks with #vm[`with self`], which is the third way an add can name the value of
the chunk it produces. #pararef(<para:impl-heap-add>, [Heap addition]) gave the
other two, #vm[`fresh`] and an already computed temporary. #vm[`with self`]
defers the choice of value to whatever context uses the resource.

Each such add contributes one _slot_ of the footprint, and each slot contributes
one member of the snapshot type, typed by what is stored at the location added.
The members are ordered as the adds are. #vm[`with self`] therefore carries no
slot index, because the slot an add fills is already determined by where the add
stands. The order of the slots is the order of the body, and a body declares
exactly the slots it adds. #vi[`Cell`] has one such add, so #vm[`Cell@snap`] has
one member at the type #vi[`val`] stores.

We leave #vi[`Cell`] as it is and grow a second predicate beside it,
#vi[`Node`], one conjunct at a time. In @lst:pred-two-slots the first conjunct we
add is a second field.

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

Marking is what determines the footprint, not counting. The snapshot has one
member per #vm[`with self`] add, in the order the adds appear, and any other
instruction in the body leaves the snapshot type alone. Each member is an
#vm[`Option`] of what its slot stores, for the reason
#pararef(<para:impl-gate-split>, [Conditional footprints]) gives below.

Every body so far has claimed #vm[`true`]. A pure conjunct is what puts something
else there. @lst:pred-bool adds one to @lst:pred-two-slots.

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
#vm[`h1`], the heap the two adds produced. The conjunct is therefore evaluated
against permission the body has already granted itself. The snapshot type is
unchanged, since a pure conjunct adds no #vm[`with self`].

Viper requires a predicate body to be _self-framing_: it must grant the
permissions its own heap reads go through. @lst:pred-unframed swaps the
conjuncts of @lst:pred-bool so that the requirement is violated.

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

The violation is visible in the VMIR without running anything. The read into
#vm[`e2`] consults #vm[`empty`], because nothing has been added yet, and a
dereference of an empty heap cannot succeed. Helium reports it through the
positivity obligation of
#pararef(<para:impl-heap-deref>, [Heap dereference]), as insufficient
permission, exactly as it would report the same read in a method body.
Self-framing is therefore the ordinary obligation a read carries, raised in a
body rather than in a method, and Helium runs no separate pass for it.

The address of a slot may depend on the value of an earlier slot.
@lst:pred-nested replaces the pure conjunct of @lst:pred-bool with an
instance of #vi[`Cell`], sitting at the reference the second slot holds. The
boolean half goes back to #vm[`true`] with it.

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

#vm[`e3`] reads the value of the second slot and #vm[`e4`] builds a location
from it, so the address of the third slot exists only once the second slot has
been produced. This is why slots have an order at all, and it is the same
order-dependence that makes a Viper assertion self-framing. The type of the
third slot is #vm[`Cell@snap`], so #vm[`Node@snap`] now holds a snapshot of
another predicate, and the nesting of the source shows up in the types.

The same rule applies at any depth, because a resource body describes exactly
one level of footprint. What a #vm[`Cell@loc`] slot holds is the business of
another resource, and it is recovered only when something unfolds it.

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
turns out to be. We keep the add unconditional, which is what lets the footprint
be read off the body syntactically at all. A guarded instruction would make the
slot count depend on a path condition, and a snapshot type cannot depend on a
path condition. The cost is that presence becomes an arithmetic question rather
than a structural one.

This is where the snapshot's #vm[`Option`] members come from. Whether the third
slot is present depends on the reference the use site supplies, which is known
at verification time, whereas the snapshot type is fixed when the resource is
declared. Optional members are the choice that is safe at declaration time, so we
make every member one. A fold packs slot $i$ as #vm[`0 < p ? Some(v) : None`],
present exactly where positive permission was contributed. Where the add was
unconditional that condition folds to #vm[`true`], so the wrapper reduces away
and an unconditional footprint pays for it only in the type.

#para[Recursion] <para:impl-recursion> One further change makes the predicate
recursive, and it is a change of a single name. @lst:pred-recursive is
@lst:pred-conditional with the nested instance naming #vi[`Node`] instead of
#vi[`Cell`], which is the usual linked-list predicate.

#viper(
  caption: [The linked-list predicate. The nested instance is the predicate
    being declared.],
  label: "lst:pred-recursive",
)[```viper
predicate Node(this: Ref) {
  acc(this.val, write) &&
  acc(this.next, write) &&
  (this.next != null ==>
     acc(Node(this.next), write))
}
```]

Its body is the same instructions with #vm[`Node@loc`] building the third
address. The snapshot type becomes recursive with it, holding an
#vm[`Option[Node@snap]`] at its third member.

Helium handles this with the machinery it already has, because the body still
describes one level. The third slot's address is built by a call to
#vm[`Node@loc`], and building an address is a pure step over the arguments, so
Helium records no dependency of #vi[`Node`] on itself. A recursive predicate is
therefore verified in one ordinary pass, like any other, with no depth limit.

One shape is rejected. A body that unfolds a resource inside that resource's own
definition, directly or around a cycle of several, is refused by Helium before
verification starts. Unfolding a resource rebuilds it from the record its own
verification produced (#pararef(<para:impl-slot-recipes>, [Slots and recipes])),
so Helium schedules a resource after everything it unfolds, and a cycle admits
no such order. Silicon accepts these programs, since it re-executes the
assertion against the state at each use. We have not found the restriction
binding in practice, as a predicate body that unfolds a predicate is rare.

=== Verifying a resource

A resource is checked once, at its declaration, under fresh symbolic parameters.
Helium walks the body instruction by instruction, and every obligation it raises
goes to @sec:impl-execution with no special handling. A dereference in a body
demands its permission on the same terms a dereference in a method body does.

Two kinds of instruction are absent from every body. A body is lowered from an
assertion, and an assertion contains no statements, so there is no assignment
and no havoc to lower. An add binding #vm[`fresh`] is absent because a body that
minted a value of its own would claim something about a value the use site never
supplied, and the same resource used twice would then mean two different things.
Freshness belongs to the instruction that uses a resource.

#para[Slots and recipes] <para:impl-slot-recipes> None of the body survives
verification as a body. What Helium keeps is a record of _recipes_: two per
footprint slot, one building the slot's address and one building its permission
amount, plus one for the boolean. Each is stored alongside the location kind and
element type of its slot. A function body leaves behind the same construct.

The recursive #vi[`Node`] of #pararef(<para:impl-recursion>, [Recursion]) shows
what that record looks like. Its third slot is the guarded
#vi[`acc(Node(this.next), write)`], produced by the instructions below, which
@fig:node-recipes reduces to recipes:

#no-numbers[```vmir
e3: Ref := *[h1] e2
e4: Bool := e3 != null
e5: Real := e4 ? 1/1 : 0/1
e6: &[Node] Node@snap @ * := Node@loc(e3)
h2 := h1 + e6 @ e5 with self
```]

#figure(
  caption: [The record #vi[`Node`] leaves behind. A recipe may name the
    resource's argument and the members of its snapshot, and nowhere else. The
    receiver the source wrote as #vi[`this.next`] is answered by the snapshot
    member that slot 1 contributed.],
  resource-recipes,
) <fig:node-recipes>

The dereference on the first line is absent from the record. A #vm[`with self`]
add binds its chunk to the slot the resource is given, so while the body is
checked, the chunk at #vm[`next(e0)`] holds the value slot 1 contributes to the
snapshot. The dereference resolves to that chunk and yields the value itself, so
#vm[`e3`] is the snapshot member itself. The guard
#vm[`e4`], the amount #vm[`e5`] and the address #vm[`e6`] are then terms over
that member and the argument, which is what the figure draws.

A recipe is consequently a pure expression built from pure operations. Its
obligations were discharged when the resource was verified, so a use site
rebuilds the terms without re-running any of them. A division in a body has its
divisor proven non-zero once, and a call in a body has its precondition proven
once, at the declaration. Rebuilding is term construction.

A recipe is seeded by an argument or by the value of an earlier slot, so slots
are ordered and a slot may look only backwards. And a value the body invented would belong to neither seed, so no
recipe could name it: an add binding #vm[`fresh`] on the path to any recipe
would have to be rejected. The lowering never emits one, because it writes
#vm[`with self`] for every #vi[`acc`] it meets inside a resource.

A use site supplies each slot value from what it already holds. Giving a
resource up reads the value out of the heap as the walk passes the slot. Taking
one on is handed a snapshot and takes member $i$ for slot $i$, so the arrow into
slot 2 in @fig:node-recipes is the term #vm[`unwrap(#0@1(s))`], where
#vm[`#0@1`] is the projection at the snapshot's one constructor
(@sec:impl-adts). The two instructions that run
these walks are the subject of @sec:impl-fold.

=== Folding and unfolding <sec:impl-fold>

So far a resource has been a declaration: something Helium checks on its own and
compiles to a record. A program has to interact with one, and the two Viper
statements that do are #vi[`fold`] and #vi[`unfold`]. This subsection covers the
instructions they are built from and the statements themselves.

#para[The resource operations] <para:impl-resource-ops> VMIR has two heap
instructions beyond the four of @sec:impl-heap. Both take a whole resource
rather than one location.

#align(center)[#vm[`h', s := h exhale R(args) @ p`]]

An #vm[`exhale`] gives up a resource. It walks the slots in the body's order,
rebuilds each address and each amount from the recipes at #vm[`args`], and
subtracts that much permission at each, raising the sufficiency obligation of
#pararef(<para:impl-heap-sub>, [Heap subtraction]) slot by slot. It reads the
value the heap held at each slot as it passes, and yields those values assembled
into the snapshot #vm[`s`]. The boolean of the body is asserted, because giving
up a resource claims that what is being given up satisfies it.

#align(center)[#vm[`h' := h inhale R(args) @ p with s`]]

An #vm[`inhale`] takes a resource on. It runs the same walk in the other
direction, adding permission at each slot instead of subtracting it. It reads no
values out of the heap, so the values it adds come from the #vm[`with`] clause:
a snapshot #vm[`s`], whose member $i$ becomes the value of slot $i$. That is
what #vm[`with self`] in the body named. The boolean of the body is assumed,
because holding the resource is what entitles a program to the claim.

Both demand

$ p > 0 $

rather than the non-negativity an add and a subtract demand. The reason is the
boolean. At zero permission the walk transfers no chunks, so the claim it would
assert or assume is about a footprint the operation neither received nor gave.
Viper rejects the same programs. An add and a subtract carry no claim of their
own, and a guarded #vi[`acc`] is exactly zero on the path its guard excludes, so
the slot-level pair keeps $p >= 0$.

The two Viper statements are built from these. A #vi[`fold`] exchanges the
chunks of the body for the instance itself, and the instance remembers what
those chunks held. An #vi[`unfold`] runs the exchange the other way. Each is a
pair of instructions, as @lst:fold-unfold shows.

#lowering(
  caption: [Each statement is a resource operation paired with a slot-level add
    or subtract, sharing one temporary.],
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

Each direction is the resource operation and the slot-level instruction that
mirrors it, sharing one temporary. The fold exhales the resource and adds the
predicate chunk bound to the snapshot the exhale yielded. The unfold subtracts
that chunk and inhales the resource bound to what it held, through an
#vm[`unwrap`], since a subtract reports its value as an #vm[`Option`].

The order is forced by permission accounting rather than by the binding. The
recursive #vi[`Node`] mentions its own instance in its body, so the outer and
inner instances sit at the same location kind, and producing either before the
other is gone would put both on the heap at once. And the boolean can only ride
on the resource half, because an add and a subtract carry no claim. It is
therefore asserted by the fold and assumed by the unfold, at the right polarity
in each direction by construction.

VMIR used to have a dedicated #vm[`fold`] instruction doing both halves at once,
and it worked. We removed it for one fewer instruction in the IR, at the cost of
the #vm[`unwrap`]. What made the trade worth taking is the equation between an
instance and its footprint, which the dedicated instruction had to maintain: the
snapshot an unfold reproduces the body from is the same value the chunk held.
Written as a pair, that equation is the same temporary named twice, #vm[`e1`]
threaded into #vm[`e2`] and then into the inhale.

The round trip is therefore exact. A fold packs the value #vm[`v`] of slot $i$
as #vm[`Some(v)`], and the matching unfold recovers it as an unwrap of a member
of that same construction. Both steps are rewrite rules of the core
(@sec:impl-adts), so the recovered term lands in #vm[`v`]'s own e-class rather
than merely being provably equal to it. A field read before a fold and the same
read after the unfold are the same term, and an assertion relating the two is
discharged by comparing class identifiers.

@lst:pred-succeeds is @lst:pred-fails with the unfold in place, beside the VMIR
that now makes the lookup succeed.

#lowering(
  caption: [The opening failure repaired. The pair puts a chunk at
    #vm[`val(c)`], and the exhale finds the location that was empty before.],
  label: "lst:pred-succeeds",
)[```viper
method use(c: Ref)
  requires acc(Cell(c), write)
{
  unfold acc(Cell(c), write)
  exhale acc(c.val, write)   // succeeds
}
```][```vmir
h1, e1: Option[Cell@snap] := h0
        - Cell@loc(e0) @ 1/1
e2: Cell@snap := unwrap(e1)
h2 := h1 inhale Cell(e0) @ 1/1
      with e2
e3: &[val] Int @ 1/1 := val(e0)
h3, e4: Option[Int] := h2 - e3 @ 1/1
```]

The subtract takes the predicate chunk and hands back the snapshot it held. The
inhale walks the one slot of #vi[`Cell`], rebuilds its address from the recipe,
and adds a chunk at #vm[`val(c)`] at full permission, bound to the member of
that snapshot. The exhale is the subtract of
#pararef(<para:impl-heap-sub>, [Heap subtraction]) with its results discarded,
raising the same sufficiency obligation it raised in @lst:pred-fails. This time
the chunk is there.

#para[Unfolding in an expression] <para:impl-unfolding> Viper also spells the
exchange as an expression. #vi[`unfolding acc(P(args), p) in e`] opens the
instance for the duration of #vi[`e`] and closes it again afterwards, so the
statement around it is left holding what it held before. @lst:unfolding reads a
field through one.

#lowering(
  caption: [An #vi[`unfolding`] emits the same pair a statement #vi[`unfold`]
    does. Only the heap that pair produces is scoped.],
  label: "lst:unfolding",
)[```viper
method peek(c: Ref)
  requires acc(Cell(c), write)
{
  assert unfolding acc(Cell(c), write)
    in c.val > 0
}
```][```vmir
h1, e1: Option[Cell@snap] := h0
        - Cell@loc(e0) @ 1/1
e2: Cell@snap := unwrap(e1)
h2 := h1 inhale Cell(e0) @ 1/1
      with e2
e3: &[val] Int @ 1/1 := val(e0)
e4: Int := *[h2] e3
e5: Bool := e4 > 0
assert e5
```]

We translate an #vi[`unfolding`] exactly as we translate an #vi[`unfold`],
through the same pair of instructions. What differs is which heap the
instructions after it read. The sub-expression is lowered against #vm[`h2`], the
heap the pair produced, so the read into #vm[`e4`] finds the field. Once the
sub-expression is finished, #vm[`h2`] goes unmentioned and the enclosing
statement carries on from #vm[`h0`]. The instance stays open in a heap value
that the surrounding code has stopped naming, so a matching fold would be
redundant and we emit none. Scoping an effect is therefore a question of which
temporary an instruction reads.

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
same arity, into a partition of the same kind, and an instance put on the heap
and taken off it by an ordinary add and subtract.

The relation to a footprint is what an abstract predicate gives up. A resource
operation walks the slots of a body, so with no body there is no walk, and
#vi[`fold`] and #vi[`unfold`] have nothing to do. A program can hold such an
instance, give it away and take it back, which is the whole of what it may do
with one. Helium skips the declaration during verification, since it states
nothing to prove.

=== Comparison with Silicon

Silicon keeps a predicate as the assertion the programmer wrote, and re-runs its
produce and consume rules over that assertion at every use. Each #vi[`acc`] in
it has its receiver and its permission expression evaluated afresh in the state
at hand, which may branch, may query the solver, and may raise obligations of
its own @silicon[Section 3.3]. Compiling the body to recipes is that walk done
once, at the declaration, where its obligations are discharged against the
body's own state. A use then rebuilds terms instead of re-executing an
assertion, and the branching stays at the declaration.

The receivers are where the difference is largest. A receiver that reaches
through the heap, as the #vm[`Node@loc(this.next)`] of @fig:node-recipes does,
costs Silicon a heap lookup on every traversal, at every level of a nested
structure and in both directions of every fold. Our recipes have that
dereference compiled away, and the value it produced is handed to the walk
instead (#pararef(<para:impl-slot-recipes>, [Slots and recipes])). A use site
builds a term for a slot address and goes on.

Precompiling costs us one class of program that Silicon accepts, which is the
resource that unfolds itself. Silicon walks such a body against the state at
hand, whereas we require the record of a resource to exist before anything
unfolds it, and a cycle of resources leaves no order in which the records can be
built.

The two verifiers also differ in what a snapshot is. Silicon keeps every
snapshot in a single uninterpreted sort, so a footprint of several locations is
one opaque term and the slots inside it are a convention the encoding maintains
rather than anything the sort records. Reading a field out of a nested predicate
is then a composition of functions the solver reasons about axiomatically.

We give each resource its own #vm[`adt`] instead, which puts that structure in
the type. A slot is a member at a known type, so the type system admits exactly
the projections that correspond to slots, and a member already has the sort its
location stores. What this buys concretely is the exactness of the round trip of
@sec:impl-fold. Silicon relates a fold to its unfold by assuming snapshot
equalities into the prover and letting it do the work, where we hand back the
same e-class.

#pagebreak()
