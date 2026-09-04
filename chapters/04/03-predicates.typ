#import "../../macros.typ": *
#import "../../figures/resource-recipes.typ": resource-recipes

== Predicates <sec:impl-predicates>

A Viper predicate packages a region of the heap, together with claims about its
contents, behind a name. @sec:bg-predicates gives the construct and the
#vi[`fold`] and #vi[`unfold`] statements that exchange an instance for its body.
This section shows what a predicate becomes in VMIR, how Helium compiles its
body once into a record of recipes, and how every later fold and unfold replays
that record without repeating the heap reads the body performed. A linked list is the example throughout.

#para[VMIR resources] VMIR provides no primitive for a predicate, because a
predicate is not the only Viper construct of this shape. Method contracts and
function preconditions also bundle heap permissions with a logical claim, and a
verifier must exchange all three the same way. VMIR therefore offers one
construct that subsumes them: a _resource_, a named and parameterised pair of a
heap delta and a boolean claim over that delta. Predicates, method contracts
(@sec:impl-methods) and function preconditions all lower to resources, so every
heap instruction treats them alike. The linked-list predicate below is the
example this section works through, and @lst:list-resource is the resource it
lowers to.

#no-numbers[```viper
predicate LinkedList(this: Ref) {
  acc(this.val, write) &&
  acc(this.next, write) &&
  this.val >= 0 &&
  (this.next != null ==>
     acc(LinkedList(this.next), write))
}
```]

#vmir(
  caption: [The predicate as a VMIR resource. A comment names the conjunct each
    group of instructions comes from, and the two field declarations become the
    location functions #vm[`val`] and #vm[`next`].],
  label: "lst:list-resource",
  placement: auto,
)[```vmir
resource LinkedList(e0: Ref) {
  // acc(this.val, write)
  e1: &[val] Int @ 1/1 := val(e0)
  h0 := empty + e1 @ 1/1 with self
  // acc(this.next, write)
  e2: &[next] Ref @ 1/1 := next(e0)
  h1 := h0 + e2 @ 1/1 with self
  // this.val >= 0
  e3: Int := *[h1] e1
  e4: Bool := e3 >=i 0
  // this.next != null ==> acc(LinkedList(this.next), write)
  e5: Ref := *[h1] e2
  e6: Bool := e5 != null
  p0 := e6 ? 1/1 : 0/1
  e7: &[LinkedList] LinkedList@snap @ *
     := LinkedList@loc(e5)
  h2 := <e6> h1 + e7 @ p0 with self
  result: (h2, e4)
}
```]

A resource's body is a sequence of instructions, like a method body. Each
#vi[`acc`] builds an address and adds a chunk for it, and #vm[`result`] delivers
the heap the adds produced together with the boolean claim.

#para[The footprint] An add marked #vm[`with self`] contributes a _slot_ to the
resource's _footprint_, the chunks an instance carries while it is folded. The
marking defers the chunk's value to whatever folds the resource, and the slots
are numbered in the order the adds appear. The linked list has three: the two
fields, and the nested instance under the guard.

Slots are ordered because a slot's address may be read out of an earlier one.
The third slot sits at #vm[`e5`], the value the #vi[`next`] chunk holds, so it
exists only once the second slot has been added. This is the same
order-dependence that makes the source body self-framing, and Helium checks it
without a pass of its own: a read placed before the add that grants it consults
an empty heap and raises the ordinary positivity obligation of @sec:impl-heap.

A conjunct that grants no permission becomes the resource's boolean claim.
#vm[`e3`] reads #vi[`this.val`] and #vm[`e4`] compares it, and the read consults
#vm[`h1`], the heap the two adds have already produced, so the claim is
evaluated against permission the body has granted itself. Where a body states no
such conjunct, the claim is #vm[`true`].

A guarded conjunct puts its guard into the permission amount rather than into
the instruction. The add of the third slot stays unconditional and takes
#vm[`p0`], which is #vm[`1/1`] where #vm[`e6`] holds and #vm[`0/1`] elsewhere, so
the slot count is fixed at declaration rather than varying with a path condition.
Presence becomes an arithmetic question instead of a structural one.

#para[Associated members] Every resource implicitly defines the two members
below, a snapshot type for the footprint and a location function for storing it.
An #vm[`@`] in a name marks a member as derived rather than declared.

#no-numbers[```vmir
adt LinkedList@snap {
  #0(Option[Int], Option[Ref], Option[LinkedList@snap])
}

function LinkedList@loc(e0: Ref): &[LinkedList] LinkedList@snap @ *
```]

The snapshot type records the values the resource holds while it is folded. It
is an #vm[`adt`] with a single constructor and one member per slot, at the type
that slot's location stores. The linked list has three slots, so
#vm[`LinkedList@snap`] has three members, and the third is a snapshot of the
resource being declared: the type is recursive because the predicate is. Every
member is wrapped in an #vm[`Option`], since a guarded slot may be absent. A
fold packs a slot's value as #vm[`0/1 <r p ? Some(v) : None`], which for an
unconditional add reduces to #vm[`Some(v)`], so the wrapper costs only at the
level of types.

The location function names the place a folded instance occupies. It maps the
resource's arguments to a location, exactly as a field declaration does at arity
one. Its group is the resource's name, so each resource owns a partition of the
heap; its stored type is the snapshot type, so a chunk in that partition holds a
whole instance; and its bound is #vm[`*`], because Viper lets a program hold any
amount of a folded predicate at once and we match that.

An unbounded partition receives no location axioms (@sec:impl-heap), so two
instances of a resource may remain possibly equal where two full field chunks
would be proven distinct. Some resources admit a tighter bound than #vm[`*`],
but VMIR gives every resource location function an unbounded one by
construction. Letting a frontend declare the bound is left to future work.

#para[Verifying a resource] A resource is verified once, at its declaration,
against fresh symbolic parameters, and the obligations its body raises are
discharged by the mechanism of @sec:impl-execution. An assertion contains no
statements, so assignments and havocs never appear. An add binding #vm[`fresh`]
is rejected: a resource must not invent a value its use site did not supply,
which would give repeated uses of the same resource inconsistent meanings.
Producing values is the calling instruction's business.

The body is then compiled away entirely, leaving a record of _recipes_. A recipe
is a pure term recording how to rebuild one part of the resource from what a use
site already holds: two per slot, one for its address and one for its permission
amount, plus one for the boolean claim. A recipe may name only the resource's
arguments and the members of its snapshot, so every
dereference the body performed to compute an address is replaced by the snapshot
member that supplies its value. @fig:list-recipes shows #vi[`this.next`], which
the body reads out of the heap at #vm[`e5`], answered in the record by
#vm[`s1`], the member slot 1 contributed. Evaluating a recipe is therefore a
pure step over terms the use site already holds, and no fold or unfold repeats
the body's heap reads.

#figure(
  caption: [The record #vi[`LinkedList`] leaves behind. A recipe names only the resource's argument and the members of its
    snapshot, so the receiver the source wrote as #vi[`this.next`] appears as #vm[`s1`], the
    member slot 1 contributed.],
  resource-recipes,
) <fig:list-recipes>

Because a recipe holds only pure operations, already verified at the
declaration, a use site rebuilds its terms without re-raising an obligation or
inventing a value. A use supplies each slot value from what it already holds:
giving a resource up reads the value out of the heap as the walk passes the
slot, and taking one on is handed a snapshot and takes member $i$ for slot $i$.
The #vm[`s1`] that slot 2's recipes name is therefore the term
#vm[`unwrap(#0@1(s))`], where #vm[`#0@1`] is the projection at the snapshot's one
constructor (@sec:impl-data).

A resource must be verified before anything that unfolds it, since unfolding
rebuilds an instance from the record the declaration left behind. A body that
unfolds a resource within its own definition, directly or through a cycle, is
therefore refused: no order over the declarations puts every record before its
use. Silicon accepts such programs, because it re-executes the assertion against
the state at hand at every use, and we have found the restriction costs nothing
in practice, as self-unfolding predicates are rare.

#para[Folding and unfolding] Two heap operations act on a whole resource rather
than a single location. An exhale, #vm[`h', s := h exhale R(args) @ p`],
relinquishes one: it walks the slots in order, evaluating recipes to subtract
each permission, asserts the resource's boolean claim, and yields the values it
removed as the snapshot #vm[`s`]. An inhale,
#vm[`h' := h inhale R(args) @ p with s`], acquires one by the same walk in the
same order, adding each permission instead of subtracting it and assuming the
boolean claim rather than asserting it. Where the exhale reads each slot's value
out of the heap, the inhale takes it from the snapshot #vm[`s`], which is what
fills the #vm[`with self`] bindings the declaration left open.

Both require strictly positive permission, which keeps a program from asserting
or assuming a claim about a footprint it neither gave nor received. The
slot-level add and subtract carry no boolean claim and so admit zero permission,
which is what lets a guarded slot be processed unconditionally.

The #vi[`fold`] and #vi[`unfold`] statements are built from these operations
paired with a slot-level counterpart, sharing one temporary, as the lowering
below shows.

#lowering(
  stacked: true,
)[```viper
fold acc(LinkedList(l), write)
//@
unfold acc(LinkedList(l), write)
```][```vmir
h1, e1: LinkedList@snap := h0 exhale LinkedList(e0) @ 1/1
h2 := h1 + LinkedList@loc(e0) @ 1/1 with e1
//@
h1, e1: Option[LinkedList@snap] := h0 - LinkedList@loc(e0) @ 1/1
e2: LinkedList@snap := unwrap(e1)
h2 := h1 inhale LinkedList(e0) @ 1/1 with e2
```]

A fold exhales the footprint and stores the snapshot it yields into a newly
added predicate chunk. An unfold subtracts the predicate chunk and inhales the
footprint from the unwrapped snapshot. Ordering the pair this way keeps an outer
instance and its inner one from occupying the heap at once when a recursive
instance is unfolded.

Building the statements from two existing instructions rather than adding
#vm[`fold`] and #vm[`unfold`] primitives keeps the identity between an instance
and its footprint exact, because the snapshot temporary threads between the two
operations. Folding a value #vm[`v`] as #vm[`Some(v)`] and unfolding it through
#vm[`unwrap`] lands back in #vm[`v`]'s own e-class by the core rewrite rules
(@sec:impl-data), so a read before a fold and the matching read after an unfold
resolve to one term and an assertion over them closes on e-class identity.

Viper also spells the exchange as an expression.
#vi[`unfolding acc(P(args), p) in e`] opens the instance for the duration of
#vi[`e`] and closes it afterwards, leaving the statement around it holding what
it held before. The lowering below reads a field through one and then exhales
the instance, which the surrounding statement still holds, and it emits the same
pair a statement #vi[`unfold`] does.

#lowering(
  stacked: true,
)[```viper
method peek(l: Ref)
  requires acc(LinkedList(l), write)
{
  assert unfolding acc(LinkedList(l), write)
    in l.val >= 0
  exhale acc(LinkedList(l), write)
}
```][```vmir
h1, e1: Option[LinkedList@snap] := h0 - LinkedList@loc(e0) @ 1/1
e2: LinkedList@snap := unwrap(e1)
h2 := h1 inhale LinkedList(e0) @ 1/1 with e2
e3: &[val] Int @ 1/1 := val(e0)
e4: Int := *[h2] e3
e5: Bool := e4 >=i 0
assert e5
h3, _ := h0 exhale LinkedList(e0) @ 1/1
```]

An #vi[`unfolding`] expression emits exactly the pair a statement #vi[`unfold`]
emits. What differs is which heap the instructions that follow read. The
sub-expression is lowered against #vm[`h2`], the heap the pair produced, so the
read into #vm[`e4`] finds the field. Afterwards nothing refers to #vm[`h2`]
again and the enclosing statement continues from #vm[`h0`], where the instance
is still folded, which is why the #vi[`exhale`] on the last line succeeds and
why no matching fold has to be emitted. Scoping an effect is a matter of which
temporary an instruction names.

One consequence is worth stating. A pure fact learned inside the sub-expression
enters the same e-graph as everything else and is not retracted when the
sub-expression ends, whereas Viper scopes the #vi[`unfolding`] to the expression
it wraps. Helium therefore keeps facts that Viper may not, which is a divergence
in the direction of accepting more programs.

#para[Abstract predicates] A Viper predicate declared without a body is
abstract. Such a predicate hides an assertion whose definition must stay opaque,
and it can be neither folded nor unfolded. Rather than lower it to a bodiless
resource, we lower it to the two components it actually needs: a domain for the
folded value and a location function for storing that value in the heap.

#lowering(
)[```viper
predicate Opaque(this: Ref)
```][```vmir
domain Opaque#snap

function Opaque(e0: Ref):
  &[Opaque] Opaque#snap @ *
```]

The domain represents the predicate's folded value and the location function
puts that value on the heap, differing from a field's only in holding an
unbounded amount rather than a fixed #vm[`1/1`]. The encoding also makes folding
and unfolding impossible by construction, since it generates no resource for an
inhale or an exhale to name.

#para[Comparison with Silicon] Silicon keeps a predicate as the body expression
the programmer wrote, and re-runs its produce and consume rules over that
expression at every use. Each #vi[`acc`] in it has its receiver and its
permission expression evaluated afresh in the state at hand, which may branch,
may query the solver, and may raise obligations of its own
@silicon[Section 3.3]. Helium performs that walk once, at the declaration, where
the body's obligations are discharged against its own state. A use then rebuilds
terms instead of re-executing an expression, and the branching stays at the
declaration.

The difference is largest at the receivers. A receiver that reaches
through the heap, as the third slot's #vi[`this.next`] does, costs Silicon a heap
lookup on every traversal, at every level of a nested structure and in both
directions of every fold. Our recipes have that dereference compiled away, and
the value it produced is handed to the walk instead, so a use site builds a term
for a slot address and goes on.

The two verifiers also differ in what a snapshot is. Silicon keeps every
snapshot in a single uninterpreted sort, so a footprint of several locations is
one opaque term and the slots inside it are a convention the encoding maintains
rather than anything the sort records. Reading a field out of a nested predicate
is then a composition of functions the solver reasons about axiomatically.

We give each resource its own #vm[`adt`] instead, which puts that structure in
the type. A slot is a member at a known type, so the type system admits exactly
the projections that correspond to slots, and a member already has the sort its
location stores. The advantage is the exactness of the fold and unfold round
trip: Silicon relates a fold to its unfold by assuming snapshot equalities into
the prover and letting it do the work, whereas Helium returns the same e-class.
