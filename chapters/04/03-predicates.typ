#import "../../macros.typ": *
#import "../../figures/resource-recipes.typ": resource-recipes

== Predicates <sec:impl-predicates>

Predicates are Viper's mechanism for encapsulating a portion of the heap, along
with claims about its contents, into a single opaque unit. This encapsulation is
essential for describing unbounded memory structures, such as linked lists or
trees. This section details how VMIR represents predicates and implements their
associated concepts, starting from @lst:cell-pred, the simplest predicate
holding a single integer field.

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

While hiding the internal contents of a predicate provides modularity, it
simultaneously complicates direct access. @lst:pred-fails illustrates a method
holding an instance of #vi[`Cell`] attempting to access its encapsulated field.
The precondition places a single chunk on the heap representing the predicate
instance itself, not the underlying #vm[`val(c)`] location. Consequently, the
exhale fails due to insufficient permission. Recovering the field requires
explicitly unfolding the predicate (@sec:impl-fold).

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

=== VMIR resources

VMIR provides no direct primitive for a "predicate", because predicates are
not the sole Viper construct exhibiting this shape. Method contracts and
function preconditions similarly bundle heap permissions with logical claims,
and a verifier must handle exchanging all three uniformly. Therefore, VMIR
introduces a single, general construct capable of subsuming them: a _resource_.
A resource is a named, parameterised pair comprising a heap delta and a boolean
claim over that delta. Predicates, method contracts (@sec:impl-calls), and
function preconditions all lower to resources, allowing each heap instruction
to treat them uniformly. @lst:cell-resource is the
#vi[`Cell`] predicate lowered to one.

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

A resource's body is a sequence of instructions akin to a method body. In
@lst:cell-resource, #vm[`e1`] builds the address, #vm[`h0`] adds a chunk for it,
and #vm[`result`] delivers the resulting heap and boolean claim (here #vm[`true`],
as the body asserts no pure conditions). The addition introduces #vm[`with self`],
a construct unique to resources that explicitly marks the chunk as part of the
resource's contributed _footprint_ (#pararef(<para:impl-snapshots>, [Snapshots])).

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

Because unbounded partitions receive neither injectivity axiom
(#pararef(<para:impl-location-axioms>, [Location axioms])), two instances of a
resource may remain possibly equal where full field chunks would be proven
distinct. While some resources theoretically admit a tighter bound than #vm[`*`],
VMIR currently forces all resource location functions to be unbounded by
construction. Making this bound declarable by frontends is left to future work.

=== Lowering a predicate body

Deriving the snapshot type and executing resource operations both require the
footprint: the specific chunks the resource contributes. We extract this list
syntactically from the body.

#para[Snapshots] <para:impl-snapshots> A snapshot records the delta an instance
folded away. It is constructed from additions marked #vm[`with self`], which
defers the choice of the chunk's value to the calling context. Each such
addition contributes one sequentially ordered _slot_ to the footprint, producing
a corresponding member in the snapshot type. For instance, #vi[`Cell`] has one
slot, yielding a single-member snapshot. To illustrate more complex shapes,
@lst:pred-two-slots builds a #vi[`Node`] predicate with multiple fields.

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

Only instructions marked #vm[`with self`] contribute to the snapshot; all other
operations leave it unaffected. Every snapshot member is wrapped in an
#vm[`Option`] to support conditional footprints
(#pararef(<para:impl-gate-split>, [Conditional footprints])). Additionally, while
previous examples claimed #vm[`true`], adding a pure conjunct incorporates a
substantive boolean claim (@lst:pred-bool).

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

The violation is explicitly captured in VMIR: reading from #vm[`empty`] triggers
the standard positivity obligation, failing due to insufficient permission.
Helium evaluates self-framing naturally through these standard read obligations,
requiring no separate verification pass.

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
  p0 := e4 ? 1/1 : 0/1
  e5: &[Cell] Cell@snap @ *
     := Cell@loc(e3)
  h2 := <e4> h1 + e5 @ p0 with self
  result: (h2, true)
}
```]

To support linked structures, slots may be guarded by conditions
(@lst:pred-conditional). Rather than gating the instruction itself --- which would
dynamically alter the slot count based on path conditions --- VMIR pushes the
guard into the permission amount (#vm[`p0`]), keeping the addition
unconditional. This shifts presence from a structural question to an arithmetic
one.

Consequently, snapshot members are uniformly wrapped in #vm[`Option`] types,
ensuring safety at declaration time when runtime values are unknown. A fold
dynamically packs a slot's value as #vm[`0 < p ? Some(v) : None`]. For
unconditional adds, this trivially reduces to #vm[`Some(v)`], imposing only a
superficial type-level cost.

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
address, and the snapshot type becomes recursive with it, holding an
#vm[`Option[Node@snap]`] at its third member. Helium handles this with the
machinery it already has, because the body still describes one level. The third slot's address is built by a call to
#vm[`Node@loc`], and building an address is a pure step over the arguments, so
Helium records no dependency of #vi[`Node`] on itself. A recursive predicate is
therefore verified in one ordinary pass, like any other, with no depth limit.

We intentionally reject one specific shape. A body that unfolds a resource within
its own definition---whether directly or through a cycle---is refused prior to
verification. Unfolding a resource fundamentally reconstructs it from the record
produced during its own verification (#pararef(<para:impl-slot-recipes>, [Slots and recipes])).
We must therefore schedule a resource after everything it unfolds, and a cyclic
dependency admits no such topological order. While Silicon accepts such programs
by re-executing assertions against the current state at every use, we have found
this restriction poses no issue in practice, as self-unfolding predicates are
exceedingly rare.

=== Verifying a resource

A resource is verified once at declaration using fresh symbolic parameters,
raising standard obligations handled uniformly by @sec:impl-execution.
Assertions contain no statements, so assignments and havocs naturally never
appear. Additionally, additions binding #vm[`fresh`] are strictly prohibited; a
resource must not invent values unsupplied by the use site, as this would assign
inconsistent semantics to repeated uses of the same resource. Freshness is
strictly the responsibility of the calling instruction.

#para[Slots and recipes] <para:impl-slot-recipes> During verification, the resource
body is compiled away entirely, leaving only a record of _recipes_: two pure
terms per footprint slot (computing address and permission) plus one for the
boolean claim. A recipe may only reference the resource's arguments and preceding
snapshot members. For instance, in @fig:node-recipes, the initial dereference is
eliminated entirely; #vm[`e3`] simply refers directly to the snapshot member
provided by slot 1.

#no-numbers[```vmir
e3: Ref := *[h1] e2
e4: Bool := e3 != null
p0 := e4 ? 1/1 : 0/1
e5: &[Node] Node@snap @ * := Node@loc(e3)
h2 := <e4> h1 + e5 @ p0 with self
```]

#figure(
  caption: [The record #vi[`Node`] leaves behind. A recipe may name the
    resource's argument and the members of its snapshot, and nowhere else. The
    receiver the source wrote as #vi[`this.next`] is answered by the snapshot
    member that slot 1 contributed.],
  resource-recipes,
) <fig:node-recipes>

Because recipes consist exclusively of pure operations verified during
declaration, a use site simply reconstructs the resulting terms without
re-raising any obligations or inventing new values.

A use site supplies each slot value from what it already holds. Giving a
resource up reads the value out of the heap as the walk passes the slot. Taking
one on is handed a snapshot and takes member $i$ for slot $i$, so the arrow into
slot 2 in @fig:node-recipes is the term #vm[`unwrap(#0@1(s))`], where
#vm[`#0@1`] is the projection at the snapshot's one constructor
(@sec:impl-adts). The two instructions that run
these walks are the subject of @sec:impl-fold.

=== Folding and unfolding <sec:impl-fold>

To interact with resources, VMIR introduces two dedicated heap operations
operating over entire resources rather than individual locations:

#align(center)[#vm[`h', s := h exhale R(args) @ p`]]

An exhale relinquishes a resource. It traverses the slots in order, evaluating
recipes to subtract permissions and asserting the resource's boolean claim. It
dynamically extracts the stored values from the heap, yielding them collectively
as the snapshot #vm[`s`]. The permission #vm[`p`] must be strictly positive.

#align(center)[#vm[`h' := h inhale R(args) @ p with s`]]

An inhale acquires a resource by reversing this traversal. It adds permissions
sequentially and assumes the resource's boolean claim. Instead of reading from
the heap, it populates the new chunks using the provided snapshot #vm[`s`],
fulfilling the #vm[`with self`] bindings from the resource's declaration. Like
exhale, it requires strictly positive permission.

This strict positivity requirement prevents asserting or assuming claims about
footprints that were neither given nor received. In contrast, primitive
slot-level additions and subtractions carry no boolean claims and thus safely
admit zero permissions, a property essential for unconditionally processing
guarded slots.

The #vi[`fold`] and #vi[`unfold`] statements are built upon these operations
(@lst:fold-unfold).

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

Each statement pairs a resource operation with its corresponding slot-level
counterpart, linked by a shared temporary. A fold exhales the internal footprint
and stores the yielded snapshot into a newly added predicate chunk. An unfold
subtracts the predicate chunk and inhales the footprint using the unwrapped
snapshot. This specific instruction ordering prevents overlapping permissions when
unfolding recursive instances, ensuring outer and inner instances never
simultaneously occupy the heap.

By constructing these as pairs of fundamental instructions rather than
introducing dedicated #vm[`fold`]/#vm[`unfold`] primitives, VMIR simplifies the
IR while elegantly preserving the identity between an instance and its footprint.
Because the snapshot temporary seamlessly threads between the two operations, the
structural round-trip remains exact.

This exactness ensures that folding a value #vm[`v`] as #vm[`Some(v)`] and
subsequently unfolding it via #vm[`unwrap`] lands precisely in #vm[`v`]'s
original e-class via core rewrite rules (@sec:impl-adts). Consequently,
equivalent reads before a fold and after an unfold resolve to the identical term,
allowing assertions to discharge instantly via e-class identity
(@lst:pred-succeeds).

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
that snapshot. The exhale is the slot-level subtraction of
@sec:impl-heap-ops with its results discarded,
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

We translate an #vi[`unfolding`] expression precisely as we translate an
#vi[`unfold`] statement, utilizing the same instruction pair. The distinction
lies strictly in which heap subsequent instructions read. The sub-expression is
lowered against #vm[`h2`], the explicitly produced heap, enabling the read into
#vm[`e4`] to successfully locate the field. Upon concluding the sub-expression,
#vm[`h2`] is no longer referenced, and the enclosing statement seamlessly resumes
from #vm[`h0`]. The instance remains open in a now-unreferenced heap value; thus,
emitting a matching fold is redundant, and we omit it. Consequently, scoping an
effect merely involves manipulating which temporary an instruction targets.

=== Abstract predicates

A Viper predicate may be declared without a body, rendering it abstract. These
predicates encapsulate assertions whose definitions must remain opaque to
enforce information hiding; consequently, they cannot be folded or unfolded.
While a naive translation to VMIR might represent them simply as bodiless
resources, we instead lower abstract predicates directly into their fundamental
conceptual components: a domain and a corresponding heap storage mechanism.
@lst:pred-abstract illustrates the translation of an abstract predicate into
VMIR primitives.

#lowering(
  caption: [An abstract predicate is translated to a domain and a location function
    in VMIR.],
  label: "lst:pred-abstract",
)[```viper
predicate Opaque(this: Ref)
```][```vmir
domain Opaque#snap

function Opaque(e0: Ref):
  &[Opaque] Opaque#snap @ *
```]

During translation, we lower the abstract predicate into a domain, which
represents the folded value of the predicate, alongside a location function
that enables storing and retrieving the instance from the heap. This approach
leverages the expressiveness of VMIR location types; the location function for
an abstract predicate differs from a standard field solely by holding an
unbounded amount, rather than a fixed #vm[`1/1`] fraction.

Furthermore, this encoding structurally prevents the folding and unfolding of
abstract predicates, as the translation does not generate a VMIR resource
member to inhale or exhale.

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
