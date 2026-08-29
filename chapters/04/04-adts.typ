#import "../../macros.typ": *
#import "../../figures/forall-node.typ": forall-node

== ADTs, Domains and Quantifiers <sec:impl-data>

Viper has two declaration forms that allow defining new datatypes. An
#vi[`adt`] declares a datatype by listing its constructors. A #vi[`domain`]
declares a type together with uninterpreted functions over it. Axioms then state
what those functions satisfy, usually for every value, which is where
quantifiers appear. This section describes how each of these is encoded
in VMIR and how Helium reasons about them.

@sec:impl-predicates has already used two of them. A resource's snapshot type is
an #vm[`adt`], and an abstract predicate's snapshot type is a #vm[`domain`]. We
now describe how such types behave generally.

=== ADTs <sec:impl-adts>

@lst:adt-shape declares a two-variant datatype and asks a verifier for the two
things a datatype is for: reading a field back out of a value, and telling which
constructor built one.

#viper(
  caption: [A datatype, a value built from one of its constructors, and the two
    questions a program asks about such a value.],
  label: "lst:adt-shape",
)[```viper
adt Shape {
  Circle(r: Int)
  Square(s: Int)
}

var x: Int
var c: Shape := Circle(x)
assert c.r == x
assert c.isCircle
```]

A datatype is one of the few Viper constructs that survives lowering as itself.
@lst:adt-lowering is what the declaration and the body become.

#vmir(
  caption: [The declaration stays a declaration. Construction, field access and
    the variant test become instructions of their own.],
  label: "lst:adt-lowering",
)[```vmir
adt Shape { Circle(Int) | Square(Int) }

e0: Int   := fresh
e1: Shape := Shape::Circle(e0)
e2: Int   := Shape::Circle.0(e1)
e3: Bool  := e2 == e0
assert e3
e4: Int   := Shape@tag(e1)
e5: Bool  := e4 == 0
assert e5
```]

There are three operations define on an ADT: a construction, a projection and a
discriminator. In VMIR, all three look like function calls, since they essentially
are. Field names are dropped
along the way, since a constructor's fields are positional, and #vi[`c.r`]
becomes #vm[`Shape::Circle.0`], written as the constructor followed by the index
of the field. #vm[`Shape@tag`] maps a value of the datatype to the index of the
constructor that built it, so #vi[`c.isCircle`] becomes a comparison of that
index against zero.

A ADT declaration reaches Helium directly. From it the verifier mints, once
per datatype, one e-graph function per
constructor, one per field of each constructor, and one for the discriminator, together
with rewrite rules relating them. In what follows $D$ is a datatype with
constructors $C_0, ..., C_m$, and $C@i$ is the projection at field $i$ of the
constructor $C$.

The first is the projection reduction. A projection applied to a matching
construction gives the field back,

$ C@i (C(a_0, ..., a_n)) => a_i "." $

The rule also descends into a ternary. Where the argument is a choice between
two constructions rather than a single construction, the projection is pushed
into both arms:

$ C@i (b ? C(a_0, ..., a_n) : C(a'_0, ..., a'_n)) => b ? a_i : a'_i $

Both arms have to be built by the same constructor, since the projection has to
yield a value on each.

The second is the discriminator reduction, one per constructor,

$ D@"tag"(C_k (...)) => k $

so a variant test on a known construction folds to a comparison between two
integer literals, which the constant folding of @sec:impl-execution decides.

A datatype may take type parameters, and #vm[`Option`] is the one VMIR declares
for itself:

#no-numbers[```vmir
adt Option[T] { Some(T) | None() }
```]

#vm[`unwrap`] is its projection at the one field of #vm[`Some`], spelled short
because it is spelled often. Being builtin is why @sec:impl-heap could hand back
an #vm[`Option[Int]`] and @sec:impl-predicates could build snapshot members out
of #vm[`Some`] and #vm[`None`] before this section named either. Helium does not
monomorphise a generic datatype: it mints one function per concept and carries
the ground type arguments on the e-node, so #vm[`Some[Int]`] and
#vm[`Some[Bool]`] are distinct terms sharing one rule.

@lst:adt-gap is what the two rules above do not reach.

#viper(
  caption: [Two assertions Helium does not prove. Both are about the
    discriminator, and neither mentions a constructor for a rule to fire on.],
  label: "lst:adt-gap",
)[```viper
var s: Shape
assume !s.isCircle
assert s.isSquare               // fails

var t: Shape
assert t.isCircle || t.isSquare // fails
```]

Nothing constrains the discriminator's range, so a value ruled out of every
variant but one is not thereby known to be the last. Behind that sits the
broader limit: an e-graph stores equalities and has no place to put a
disequality, so what Helium can refute it reconstructs by equality refutation
over the constructor labels a class carries. We left both
open deliberately, since verifying a specification-free program turns on neither,
and both remain future work.

=== Domains <sec:impl-domains>

A domain declares a type together with uninterpreted functions over it, and
@lst:domain-fails declares two of them that are meant to be inverse.

#viper(
  caption: [Two functions and no axiom. Nothing relates a round trip through
    them to the value it started from.],
  label: "lst:domain-fails",
)[```viper
domain Box {
  function box(v: Int): Box
  function unbox(w: Box): Int
}

method use() {
  assert unbox(box(0)) == 0  // fails
}
```]

The functions are uninterpreted, so the assertion fails. The program
contains no information about how these two functions relate to one
another. An axiom is
how a domain makes this link, and @lst:domain-lowering adds one.

#lowering(
  caption: [A domain flattens into a type, two ordinary function declarations
    and a top-level axiom.],
  label: "lst:domain-lowering",
)[```viper
domain Box {
  function box(v: Int): Box
  function unbox(w: Box): Int

  axiom base {
    unbox(box(0)) == 0
  }
}
```][```vmir
domain Box

function box(e0: Int): Box
function unbox(e0: Box): Int

axiom base {
  e0: Box  := box(0)
  e1: Int  := unbox(e0)
  e2: Bool := e1 == 0
  result: e2
}
```]

In VMIR a #vm[`domain`] declares a type, and that is the whole of it. The domain
functions become ordinary function declarations at the top level, with no body,
and the axiom becomes a top-level #vm[`axiom`] declaration. Nothing ties the
axiom back to the domain it was written inside: a Viper domain supplies the
source syntax that groups the three, and VMIR keeps them completely separate.

An axiom's body is ordinary pure VMIR, and its #vm[`result`] is the boolean it
claims. Helium assumes every axiom in the program into the e-graph before it
walks the unit it is verifying. The
facts of an axiom are therefore available from the first instruction of every
verification unit.

Axioms are trusted, which is how Viper defines them: Helium raises no obligation
on an axiom body either, and the programmer is responsible for not declaring an
inconsistency.

#para[No generic domains] While a domain in Viper may declare type parameters,
our verifier currently has no support for these. The reason is that VMIR
has no notion of a type-generic axiom. An axiom is a closed fact merged into the
state up front, whereas a generic domain's axiom is a family of facts, one per
instantiation of the domain's parameters. Silicon (Silver) resolves that by monomorphising
a domain as soon as one of its members is referenced, and a reference need not
determine every parameter: whatever it leaves open is filled with the default
type, #vi[`Int`]. @lst:domain-generic is what that costs.

#viper(
  caption: [Calling #vi[`f`] constrains nothing about #vi[`T`], so Silver
    instantiates the domain at the default type and asserts its axiom there.],
  label: "lst:domain-generic",
)[```viper
domain D[T] {
  function f(x: Int): Int
  axiom { false }
}
```]

A program that never mentions #vi[`D`] is consistent, and one that calls
#vi[`f`] is not. Rather than reproduce a rule of that kind we refuse the
declaration for now.

Returning to #vi[`Box`], its axiom is weaker than the domain it belongs to.
Asking the same round trip at any other integer fails:

#no-numbers[```viper
assert unbox(box(3)) == 3  // fails
```]

One closed axiom fixes one value. The two functions are meant to be inverse at
every integer, and stating that takes a quantifier.

=== Quantifiers <sec:impl-quantifiers>

A universally quantified assertion becomes a #vm[`forall`] instruction, and it
is the only quantifier VMIR provides. This subsection describes the instruction,
what Helium keeps of a quantifier body, how an instance is released, and where
proving a quantifier stops.

@lst:quant-lowering states the round trip of #vi[`Box`] over every integer,
beside the VMIR it lowers to, and the assertion at #vi[`3`] succeeds under it.

#lowering(
  caption: [A quantified axiom. The #vm[`forall`] is one instruction and its
    body is a nested instruction sequence.],
  label: "lst:quant-lowering",
  stacked: true,
)[```viper
axiom round_trip {
  forall v: Int :: {box(v)}
    unbox(box(v)) == v
}
```][```vmir
axiom round_trip {
  e0: Bool := forall e0: Int :: {box(e0)} {
    e1: Box  := box(e0)
    e2: Int  := unbox(e1)
    e3: Bool := e2 == e0
    result: e3
  }
  result: e0
}
```]

One instruction carries the whole quantifier. The temporary #vm[`e0`] serves
as the binder, one per entry of the list of types the
instruction binds. #vm[`{box(e0)}`] is its trigger group, carried over from the
source and written over the binders. The
braces enclose the body, an instruction sequence of its own whose #vm[`result`]
holds the proposition being quantified.

A #vm[`forall`] is a normal value: its boolean occupies a temporary like any other
computation, and it can be asserted, assumed or passed on as an operand. The
body being an instruction sequence is what makes nesting ordinary, since an
inner quantifier is one more instruction of an outer body.

The first binder takes the quantifier's own temporary, and further binders and
the steps of the body follow it. Reusing that temporary is what puts the
quantifier's boolean out of reach of its own body, so a quantifier cannot refer
to itself. A temporary below it is a value the enclosing scope supplies, and
@lst:quant-capture names one inside the body.

#lowering(
  caption: [A quantifier over a value the enclosing scope supplies. #vm[`e0`] is
    below the quantifier's own temporary, so naming it inside the body captures
    it.],
  label: "lst:quant-capture",
  stacked: true,
)[```viper
var k: Int
assume forall v: Int :: {box(v)}
  unbox(box(v)) == v + k
```][```vmir
e0: Int  := fresh
e1: Bool := forall e1: Int :: {box(e1)} {
  e2: Box  := box(e1)
  e3: Int  := unbox(e2)
  e4: Int  := e1 + e0
  e5: Bool := e3 == e4
  result: e5
}
assume e1
```]

#vm[`e0`] is the enclosing #vi[`k`], and the body reaches it at #vm[`e4`],
below the quantifier's own #vm[`e1`]. An inner quantifier's binders are numbered
above an outer's by the same rule.

What Helium keeps of that body is a _recipe_, drawn in @fig:forall-node: the
body as a term graph, with the capture and the binder left open at the bottom.

#figure(
  forall-node,
  caption: [The quantifier of @lst:quant-capture, and one firing of it. The node
    holds its recipe and one child per capture, so the two holes are filled from
    opposite sides: #vm[`t0`] by the node's child, #vm[`t1`] by the term the
    trigger matched.],
) <fig:forall-node>

The recipe and the triggers are compiled once and kept in a table for the remainder
lifetime of the verified unit. What the quantifier e-node carries is a reference
into that table and one child per capture, so the body itself never appears in
the e-graph.

A single rewrite rule is responsible for instantiating every quantifier in the program. It finds the
e-classes holding a #vm[`forall`] node, matches the triggers of each one against
the e-graph, and replays its recipe at every new binding a match supplies. The same
rule covers nesting: an inner quantifier is a step of the outer recipe, so an
instance builds it as an ordinary node with the outer binding in its children,
and the rule picks it up as soon as it is in the graph. This is why a quantifier
is data rather than a rule of its own, since egg fixes the rule set before a
saturation run and a rule cannot be added in the middle of one.

An instance is released under a guard, because a quantifier need not be true
where its trigger matches. @lst:quant-guard assumes one under an implication.

#viper(
  caption: [A quantifier assumed under an implication. The trigger matches at
    both assertions, and the instance is released by the #vi[`assume`] between
    them.],
  label: "lst:quant-guard",
)[```viper
var b: Bool
assume b ==> forall v: Int :: {box(v)}
  unbox(box(v)) == v

assert unbox(box(3)) == 3   // triggers forall, but fails assertion
assume b
assert unbox(box(3)) == 3   // succeeds
```]

Both assertions build #vi[`box(3)`], so the trigger matches at the first one
already. What a match adds is the implication

$ q ==> "body" $

where $q$ is the quantifier itself, so an instance contributes its body once $q$
is #vm[`true`]. At the first assertion only the assumed implication is known,
$q$ is open, and the goal stands unproven. The #vi[`assume`] between the two
puts #vi[`b`] at #vm[`true`] and $q$ with it, and the instance already in the
graph closes the second assertion. Matching a quantifier whose truth is open is
therefore sound, and the verifier is free to match one on a path it is still
exploring, or one it is checking rather than using. A precondition token the
body carries rides the same guard, so a callee's facts arrive with the
quantifier's truth.

Well-definedness is confirmed where the quantifier is stated. An axiom is
trusted, so this concerns a quantifier in a method or a function body. The
check runs in a throwaway copy of the live state with the binders replaced by
fresh values.

Proving a quantifier is where Helium stops. There is no skolemisation, so an
#vi[`assert forall ...`] is discharged where the same quantifier is already
#vm[`true`] in the state, from an earlier assumption.
Existential quantifiers are rejected by the verifier, and their implementation
remains future work.
