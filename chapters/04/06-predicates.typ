#import "../../macros.typ": *

== Predicates <sec:impl-predicates>

Viper's second declaration form is the one with something inside it, and the
instructions of @sec:impl-heap-interaction are what that something is made of. A
predicate names an assertion — permission to some piece of the heap, together with
whatever invariant is claimed of what that piece holds — and abstracts over it, so
that a program can hold, pass and give back the whole bundle without naming its
parts, and so that a recursive body can describe a structure of unbounded size
@viper-tutorial. The body must be _self-framing_: it has to grant the permissions
its own heap reads go through, which is what makes the assertion mean the same
thing wherever it is unfolded.

A predicate declaration lowers to a #vm[`resource`], whose body is not an
assertion in Viper's sense but ordinary straight-line VMIR.

#lowering(caption: [A predicate becomes a resource whose body yields a heap and a value.], label: "lst:predicate-decl")[```viper
predicate gt(x: Ref, b: Int) {
  acc(x.f) && x.f > b
}
```][```vmir
resource gt(e0: Ref, e1: Int) {
  e2: &[f] Int @ 1/1 := f(e0)
  h0 := empty + e2 @ 1/1 with self
  e3: Int := *[h0] e2
  e4: Bool := e3 > e1
  result: (h0, e4)
}
```]

Every line of it has appeared before. What is worth stating is that checking such
a body well-formed is not a separate discipline: the instructions mean what they
mean anywhere else, and the obligations they raise — the read of #vm[`h0`]
demanding positive permission at #vm[`e2`], say — are discharged by the route of
@sec:impl-execution. Viper's requirement that a predicate body be self-framing is
that obligation and nothing more.

The one line that is new is the bind point. Inside a resource body an add writes
#vm[`with self`], which binds the chunk to the next slot of the resource's _own_
footprint — the value whoever uses this resource supplies for it. It is
deliberately unnumbered: the slot's ordinal is a consequence of where the add
stands in the body, never something the body states, so a body cannot name a slot
it did not declare or name one out of order. What the footprint _is_ is read off
these markers, which is #pararef(<para:impl-snapshots>, [Snapshots]) below.

What a resource context does is restrict which instructions may appear. The rule
is one line — a body may never mint a fresh value — and #vm[`with self`] is what
lets it hold structurally rather than by prohibition: every add in a body is bound
to something in scope, so a body cannot invent a value even though the instruction
that could is available to it. There are no assignments and no havocs either, so a
body cannot mutate a heap; the only unconstrained values in it are the parameters,
and they are bound to concrete arguments wherever the resource is used. A body is
therefore a recipe over its parameters rather than a piece of program. Freshness
is a property of the _instruction that uses_ a resource, and never of the resource.

#para[Resources] The last line is what the name #vm[`resource`] refers to. A body
evaluates to a _pair_: a heap and a value. The heap is a delta — what holding this
adds, here one chunk at #vm[`f(e0)`]. The value is an assertion _about_ that delta:
a pure condition claimed to hold of what the delta contains, here that the field
read out of it exceeds #vm[`e1`]. An all-permission body has nothing to claim and
its value is simply #vm[`true`].

Being a named, parameterised delta-plus-assertion pair is all a resource is, and
that is more general than a predicate. A method's precondition and postcondition
and a function's precondition all lower to resources too (@sec:impl-cfg), which is
why the construct is worth having under its own name. Permission-carrying things
themselves are _locations_ in VMIR (@sec:impl-heap), so a predicate instance sits
in the heap on the same terms as a field does.

#para[Derived members] Naming a bundle costs two members the source program never
writes. Every resource brings into being a snapshot type and a location function.

#vmir[```vmir
adt gt@snap { #0(Option<Int>) }

function gt@loc(e0: Ref, e1: Int): &[gt] gt@snap @ *
```]

An #vm[`@`] in a name marks a member as derived rather than declared, so both
carry one: #vm[`gt@snap`] for the type and #vm[`gt@loc`] for the function, over
the resource's own name.

The location function is @lst:field-decl at the predicate's arity, and its
components are fixed the same way. The group is the predicate's name, so each
predicate owns a partition. The stored type is the derived snapshot type. The
bound is #vm[`*`], following Viper, which puts no limit on how many instances of
one predicate a program may hold; a partition of unbounded kind is then the one
that receives neither of the axioms of @sec:impl-heap. Nothing forces that choice
to be uniform, though. The bound is a component of a location type like any other,
so it could be picked per resource — a predicate known to be exclusive would then
buy the axioms a field enjoys — and settling how a declared bound is to be checked
is left for later work.

#para[Snapshots] <para:impl-snapshots> The snapshot is what is stored at a
predicate location — what an instance remembers of the delta it folded away. Its
type is read off the body syntactically: every #vm[`with self`] in the body
contributes one slot, in order, typed by what is stored at the location added.

Marking the slots rather than inferring them is what makes that reading exact. A
body may contain adds that are not footprint — an
#pararef(<para:impl-unfolding>, [`unfolding`]) inside it produces the chunks of
_another_ predicate's footprint, which have nothing to do with this one's — so
"every add is a slot" would be wrong, and it is wrong in the direction that
silently changes a predicate's meaning. The check that the marking is honest is a
bijection: a body's heaps form a chain from #vm[`empty`] to the one its
#vm[`result`] delivers, and every add on that chain carries #vm[`with self`] while
every #vm[`with self`] lies on it. A scoped heap, being off the chain, is excluded
by construction.

Silicon carries the same information in a different shape. Its snapshots live in a
single uninterpreted sort: a footprint of several locations is a right-nested tree
of #vm[`Combine`] pairs taken apart by #vm[`First`] and #vm[`Second`], and a value
of any other sort enters and leaves it through sort wrappers. What a slot _is_ is
therefore not recoverable from the term — the shape of the tree is a convention
the encoding maintains, the projections are functions the solver reasons about
axiomatically, and reading a field back out of a nested predicate means composing
a path of projections and unwrappers and trusting that it matches the path the
fold built.

Giving each resource its own #vm[`adt`] makes that structure part of the type
instead. A slot is a named member at a known type, so a projection that does not
correspond to a slot cannot be written; the accessor is a constructor--projection
reduction of the core (@sec:impl-adts) rather than an axiom; and no wrapping is
needed, since the member already has the sort the location stores. The
#pararef(<para:impl-roundtrip>, [Exactness of the round trip]) below is what this
buys concretely.

The slots are #vm[`Option`]-typed because @lst:guarded-add made an add
unconditional and put the condition in the amount. Presence is therefore a question
about the amount rather than about the instruction, and the slot is packed as
#vm[`0 < p ? Some(v) : None`] — present exactly where positive permission was
contributed. Where the add was unconditional the discriminant folds to #vm[`true`]
and the projection reductions peel the slot back to the value, so an unconditional
footprint pays nothing for the wrapper.

#para[Inhaling and exhaling an instance] Taking and giving back an instance needs
no new instruction. An #vi[`acc`] naming a predicate is an #vi[`acc`] like any
other: the location is the derived location function applied to the arguments, and
the assertion lowers to the add and the subtract of @sec:impl-heap-interaction.

#lowering(caption: [A predicate instance is added and subtracted like any other chunk.], label: "lst:resource-inhale")[```viper
inhale acc(gt(x, b))
//@
exhale acc(gt(x, b))
```][```vmir
h1 := h0 + gt@loc(e0, e1) @ 1/1
      with fresh
//@
h2, _ := h1
         - gt@loc(e0, e1) @ 1/1
```]

Everything the two directions do differently is what @sec:impl-heap-interaction
already established. The add is total and takes the value of the new chunk from
its bind point — here #vm[`fresh`], since an #vi[`inhale`] hands the instance over
without saying anything about it; the subtract raises the sufficiency obligation,
discharged under the path condition in force. The only thing specific to a
predicate here is what the value _is_ — a snapshot, at the derived type, rather
than a field's stored value.

Neither direction interprets the body at the site it is used. The chunk sits at
the predicate's own location, holds an opaque snapshot, and says nothing about the
fields the body would have named. That is exactly the point of a predicate, and it
is what the two paragraphs below have to undo.

#para[The resource operations] <para:impl-resource-ops> VMIR also has
#vm[`inhale`] and #vm[`exhale`] instructions, and they are a different thing from
the add and the subtract above: they take a whole resource rather than one
location. Each walks the body's slots, rebuilding every slot's address and
permission — the body is a recipe over the parameters, so this is an instantiation
of that recipe at the actual arguments — and applies the delta one slot at a time,
in the body's order. The body's boolean comes with it: #vm[`exhale`] asserts it,
#vm[`inhale`] assumes it.

They are the two directions of the same walk, and they carry the two parameters of
@sec:impl-heap-interaction for the same reasons the slot-level pair does. An
#vm[`exhale`] is read-shaped: it reads each slot's value out of the heap on its
way past, and _yields_ the snapshot assembled from what it read. An #vm[`inhale`]
is write-shaped: it has no values of its own, so it takes a bind point, and what
is bound there is a whole snapshot — slot $i$ of the walk is bound to projection
$i$ out of it, which is exactly what #vm[`with self`] in the body names.

One obligation is stricter here than at a slot. A resource operation demands

$ p > 0 $

rather than mere non-negativity, because it carries a boolean about a footprint:
at zero permission it would assume or assert facts about chunks it neither
received nor gave, which is a claim about nothing. Viper rejects the same
programs. The slot-level pair keeps $p >= 0$, since it says nothing and since a
guarded #vi[`acc`] is exactly zero on the path its guard excludes
(#pararef(<para:impl-amounts>, [Conditional permission amounts])).

Contract application is where these appear first — a call is an exhale and an
inhale of the callee's contracts (@sec:impl-calls) — but they are reached from a
source program too, by the next paragraph.

#para[Folding and unfolding] An inhale hands over an instance without ever looking
at what it stands for. A #vi[`fold`] is the operation that does look: it exchanges
the chunks the body's delta names for the instance itself, and the instance it
produces remembers what those chunks held. An #vi[`unfold`] runs the exchange the
other way. Together they are the hot path of a Prusti encoding — #vi[`unfold`] is
second in frequency only to #vi[`exhale`] — and between them they are what makes a
predicate usable rather than merely holdable.

Neither is an instruction. Each is a _pair_ of instructions already in hand: the
resource operation of #pararef(<para:impl-resource-ops>, [The resource
operations]), which walks the body, alongside the slot-level add or subtract at the
predicate's own location, which moves the chunk. What the pair does that neither
half does alone is share one value between them.

#lowering(caption: [Folding and unfolding an instance.], label: "lst:fold-unfold")[```viper
fold acc(gt(x, b))
//@
unfold acc(gt(x, b))
```][```vmir
h1, e2 := h0 exhale gt(e0, e1) @ 1/1
h2 := h1 + gt@loc(e0, e1) @ 1/1
      with e2
//@
h1, e2 := h0
          - gt@loc(e0, e1) @ 1/1
h2 := h1 inhale gt(e0, e1) @ 1/1
      with unwrap(e2)
```]

A fold exhales the resource: the walk subtracts each slot's permission, raising the
sufficiency obligation of
#pararef(<para:impl-subtract>, [Giving permission back]) exactly as an
#vi[`exhale`] of the same #vi[`acc`] would, reads the value the heap held there,
and asserts the body's boolean, since a fold claims the assertion holds of what it
is folding away. What it yields is the snapshot assembled from the values just
read, and the add then puts one chunk at the predicate's own location bound to it.

An unfold is the same two instructions with every direction reversed. The
predicate chunk is subtracted first, which hands back the snapshot it held; the
resource is then inhaled bound to that snapshot, so each slot's permission is added
back with its value bound to the slot's projection out of the snapshot, and the
body's boolean is _assumed_ rather than asserted, because the instance being held
is what entitles the program to it.

The order is forced in both directions, and by permission accounting rather than
by anything about the boolean: the predicate chunk must be gone before the body's
slots are produced and the slots must be gone before the chunk is produced, or a
predicate whose body mentions its own instance would briefly hold both. The pair
expresses that bracketing positionally.

Which half carries the boolean is the reason to write the pair this way round
rather than the other. The chunk-side instruction is the slot-level pair, which
assumes and asserts nothing at all, so the body's boolean can only land on the
body side — assumed by the unfold's inhale, asserted by the fold's exhale, the
right polarity in each direction by construction. Had the resource operation gone
on the chunk side instead, one half of each pair would assume a boolean the other
half was supposed to have just proved, and the desugaring would be sound only
under a side condition about the order the two were emitted in.

A slot's address may depend on an earlier slot's value — Prusti's linked
structures are full of #vi[`P(this.next)`] — so the walk threads the values it has
recovered back into the addresses it has yet to build. This is why the slots have
an order at all, and it is the same order-dependence that makes a Viper assertion
self-framing: the conjunct granting permission must precede the one reading
through it. The addresses come from the snapshot the bind point supplied, never
from a read of the heap being built, so the walk never depends on a slot it has
not yet produced.

#para[The seam] <para:impl-seam> The unfold's #vm[`unwrap`] is the one coercion in
either pair, and it is where the two obligations of
#pararef(<para:impl-resource-ops>, [The resource operations]) meet. A subtract
yields an #vm[`Option`], because at zero permission it removes nothing and has
nothing to report; an inhale takes a plain snapshot, because it demands positive
permission and so cannot be applied where nothing was there.

It is not a proof obligation. Presence is built from the amount the instruction
was written with — #vm[`0 < 1/1`] here — so it const-folds to #vm[`true`], the
yield is concretely a #vm[`Some`], and the unwrap is peeled by the reduction of
@sec:impl-adts before anything is asked to prove anything. Where the amount is a
#vm[`wildcard`] the same holds structurally, a wildcard being positive by
construction. The alternative — emitting an assertion that the yield is present —
would put a proof search where there is currently a hashmap lookup, and would make
the pair cost more than a single instruction would have.

What the pair buys for that is the thing a single instruction would have had to
enforce: the snapshot the unfold reproduces the body from is the same value the
chunk held, because it is _literally the same temporary_, threaded from one
instruction to the next. The equation between an instance and its footprint is
emergent rather than maintained. That is also why a fold and an unfold may be
written as ordinary instructions at all — an inhale that minted a fresh snapshot
would lose the equation, and there would be no way to state it after the fact.

#para[Exactness of the round trip] <para:impl-roundtrip> The reason to state the two operations together
is that their composition has to be the identity, and here it is one by
construction rather than by proof. A fold packs slot $i$'s value $v$ into the
snapshot as #vm[`Some(v)`]; an unfold recovers it as
#vm[`unwrap(proj_i(cons(..)))`]. Both reductions — a projection applied to a
constructor, and an unwrap applied to a #vm[`Some`] — are rewrite rules of the core
(@sec:impl-adts), so the recovered term is not merely provably equal to $v$, it
_is_ $v$: the same e-class, reached by two reductions and no obligation.

That is what makes the framing question disappear. A field read before a fold and
the same field read after the matching unfold are the same term in the same
e-class, so an assertion relating them is discharged by a comparison of class
identifiers. Silicon reaches the same conclusion by a different road — it emits
snapshot equalities and lets the solver connect them — and the difference is that
here there is nothing to connect.

The reductions are also why the verifier normalises after each of these
instructions. A repeated fold–unfold cycle builds a tower of constructors and
projections over one another, and an address reaching _through_ such a tower —
which is what a nested predicate's slot address does — only becomes e-class-equal
to the chunk actually held once the tower has collapsed. Since chunk lookup is an
e-class match, that collapse has to happen before the next lookup rather than at
the next obligation, so the terminating reductions are run at every fold and
unfold. They are a strict subset of the full rule set, chosen for termination, so
this costs a fixpoint over the reductions and not a saturation.

#para[Unfolding in an expression] <para:impl-unfolding> Viper also spells the
exchange as an expression. #vi[`unfolding acc(P(args), p) in e`] opens the instance
for the duration of #vi[`e`] and closes it again, and Prusti uses it in every
heap-dependent function body — #vi[`p_Account_snap`] of @lst:example-viper is the
canonical shape.

It lowers to the same pair, applied to the heap in hand and producing a new one;
#vi[`e`] is then lowered against _that_ heap, while the
expression surrounding it keeps reading the original. Nothing puts the unfolded
heap back, because nothing needs to: heaps are values, the enclosing expression
already names the one it wants, and the unfolded one is simply not mentioned again.
Scoping an effect is thereby a matter of which temporary an instruction reads,
which is the same observation
#pararef(<para:impl-threading>, [Taking permission]) started from.

One wrinkle is worth stating. Because #vi[`unfolding`] is an expression, it can sit
under a condition that no statement does — inside a ternary arm, say — and so its
two instructions are the only heap instructions that may carry a path condition
finer than their block's.
The effect is scoped and fabricates no permission, so this is benign; but it is
the one place where "heap instructions operate at block granularity", which
@sec:impl-cfg leans on, is not literally true.

#para[Abstract predicates] A predicate declared without a body has no delta to read
a snapshot type off, so it does not get one. The snapshot type is an opaque domain
instead of an #vm[`adt`], and values of it are only ever passed around, never
constructed or projected. Nothing else changes: there is still a derived location
function at the same arity, into a partition of the same kind, and an instance is
added and subtracted by @lst:resource-inhale like any other. What is lost is only
the relation to a footprint — with no body there is no walk for a resource
operation to run, and so nothing to fold or unfold. Such an instance can be held,
given away and taken back, and nothing more.

Prusti's #vi[`p_Param`], the one abstract predicate in the worked example, is
exactly this case: a value of a generic type parameter whose representation is not
known where the encoding is generated, and about which the verifier is therefore
expected to conclude nothing.

#note[
  *Listing notation.* The listings in these three sections use
  #vm[`e1 @ 1/1`] and #vm[`assign(e1, 42)`], following the rest of the
  chapter. A real translation dump prints these without the punctuation —
  #vm[`h0 + e1 1/1 with fresh`], #vm[`h0 assign e1 42`] — while
  #vm[`result: (h0, e4)`], the bind points and the resource operations are
  verbatim. The #vm[`@loc`] suffix is ahead of
  the implementation, which still prints a location function under the resource's
  bare name. Worth settling in one pass over the chapter rather than per section.
]
