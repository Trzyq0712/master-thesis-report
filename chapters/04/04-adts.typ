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
an #vm[`adt`], and an abstract predicate's snapshot type is a #vm[`domain`].

#para[ADTs] A datatype is one of the few Viper constructs that survives lowering
as itself. @lst:adt-lowering pairs a two-variant declaration, and the two
questions a program asks of such a value, with what each becomes: reading a
field back out, and telling which constructor built one.

#lowering(
  caption: [The declaration stays a declaration. Construction, field access and the variant test become instructions of their own.],
  label: "lst:adt-lowering",
  placement: auto,
)[```viper
adt Shape {
  Circle(r: Int)
  Square(s: Int)
}
//@
var x: Int
var c: Shape := Circle(x)
assert c.r == x
assert c.isCircle
```][```vmir
adt Shape {
  Circle(Int) | Square(Int)
}
//@
e0: Int   := fresh
e1: Shape := Shape::Circle(e0)
e2: Int   := Shape::Circle.0(e1)
e3: Bool  := e2 == e0
assert e3
e4: Int   := Shape@tag(e1)
e5: Bool  := e4 == 0
assert e5
```]

The declaration keeps its shape and loses only the field names, since a
constructor's fields are positional in VMIR: #vi[`c.r`] becomes
#vm[`Shape::Circle.0`], the constructor followed by the field index.
#vm[`Shape@tag`] maps a value to the index of the constructor that built it, so
the variant test #vi[`c.isCircle`] becomes a comparison against zero.
Construction, projection and discrimination are all function applications, and
each statement becomes one instruction over them.

Helium answers a projection or a variant test from the constructor that built
the value: a projection applied to a matching construction gives the field back,
and a variant test on a known construction folds to a comparison between two
integer literals, which the constant folding of @sec:impl-execution decides.
@sec:appendix-rewrites states the rules that do this.

A datatype may take type parameters, and VMIR declares one for itself:
#vm[`adt Option[T] { Some(T) | None() }`].
#vm[`unwrap`] is its projection at the one field of #vm[`Some`], abbreviated for
brevity. Being builtin is why @sec:impl-heap could return
an #vm[`Option[Int]`] and @sec:impl-predicates could build snapshot members out
of #vm[`Some`] and #vm[`None`] before this section named either. We do not
monomorphise a generic datatype: we mint one function per concept and carry
the ground type arguments on the e-node, so #vm[`Some[Int]`] and
#vm[`Some[Bool]`] are distinct terms sharing one rule.

Helium reduces a projection against a visible
construction and a discriminator against a visible constructor, which are the
destruction and tagging axioms of @sec:bg-viper. It states no counterpart of
exclusivity, so the discriminator of a value no constructor built is
unconstrained. Helium proves neither assertion below, since both are about the
discriminator and neither mentions a constructor to reduce against.

#no-numbers[```viper
var s: Shape
assume !s.isCircle
assert s.isSquare               // fails

var t: Shape
assert t.isCircle || t.isSquare // fails
```]

Ruling such a value out of every variant but one therefore does not prove it
belongs to the remaining one. The second assertion fails for the same reason: a
case analysis over the variants is complete only under exclusivity. Behind both
is that an e-graph stores equalities and has no natural representation for a
disequality, so a refutation has to be reconstructed by equality refutation over
the constructor labels an e-class carries. Verifying specification-free programs
relies on neither capability, so we left both open for future work.

#para[Domains] A domain groups a type, its uninterpreted functions, and the
axioms that give them meaning. VMIR keeps none of that grouping:
@lst:domain-lowering flattens the domain into a type declaration, ordinary
top-level function declarations, and a top-level axiom.

#lowering(
  caption: [A domain flattens into a type, two ordinary function declarations and a top-level axiom.],
  label: "lst:domain-lowering",
  placement: auto,
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

In VMIR a #vm[`domain`] declares a type. The domain
functions become ordinary function declarations at the top level, with no body,
and the axiom becomes a top-level #vm[`axiom`] declaration. Nothing ties the
axiom back to the domain it was written inside: a Viper domain supplies the
source syntax that groups the three, and VMIR keeps them completely separate.

An axiom's body is ordinary pure VMIR, and its #vm[`result`] is the boolean it
claims. Helium assumes every axiom in the program into the e-graph before it
walks the unit it is verifying. The
facts of an axiom are therefore available from the first instruction of every
verification unit. Axioms are trusted, which is how Viper defines them: Helium
raises no obligation on an axiom body either, and the programmer is responsible
for not declaring an inconsistency.

While a domain in Viper may declare type parameters,
our verifier currently has no support for these. The reason is that VMIR
has no notion of a type-generic axiom. An axiom is a closed fact merged into the
state up front, whereas a generic domain's axiom is a family of facts, one per
instantiation of the domain's parameters. Silicon (Silver) resolves that by monomorphising
a domain as soon as one of its members is referenced, and a reference need not
determine every parameter: whatever it leaves open is filled with the default
type, #vi[`Int`], so the axiom is asserted at a type the program never mentions.
Calling #vi[`f`] below constrains nothing about #vi[`T`], so Silver instantiates
the domain at the default type and asserts its axiom there.

#no-numbers[```viper
domain D[T] {
  function f(x: Int): Int
  axiom { false }
}
```]

A program that never mentions #vi[`D`] is consistent, and one that calls
#vi[`f`] is not, so whether the program holds a contradiction depends on which
members of it happen to be referenced. Rather than reproduce a rule of that kind
we refuse the declaration for now.

Returning to #vi[`Box`], its axiom is weaker than the domain it belongs to. It
fixes the round trip at #vi[`0`] and says nothing about any other integer, so
asking the same round trip one integer over fails:

#no-numbers[```viper
assert unbox(box(3)) == 3  // fails
```]

One closed axiom fixes one value, and the two functions are meant to be inverse
at every integer. Stating that takes a quantifier, which is the last construct
this section admits.

#para[Quantifiers] A universally quantified assertion becomes a #vm[`forall`]
instruction, the only quantifier VMIR provides. The lowering below states the
#vi[`Box`] round trip over every integer, with the #vm[`forall`] one instruction
whose body is a nested instruction sequence.

#lowering(
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

A #vm[`forall`] is a normal value: the instruction binds its boolean result to a
temporary, as every other computation does, and that temporary can then be
asserted, assumed or passed on as an operand. Nesting demands no further
mechanism, since the body is an instruction sequence and an inner quantifier is
one more instruction of it.

The first binder takes the quantifier's own temporary, and further binders and
the steps of the body follow it. Reusing that temporary puts the quantifier's
boolean out of reach of its own body, so a quantifier cannot refer to itself. A
temporary numbered below the quantifier's own is not a binder but a value the
enclosing scope supplies, which the body captures by naming it.
@lst:quant-capture captures a variable and divides by it, quantifying over a
domain function #vi[`f`] from integers to integers that carries the trigger.

#lowering(
  caption: [A quantifier over a value the enclosing scope supplies. #vm[`e0`] is
    below the quantifier's own temporary, so naming it inside the body captures
    it, and the division it feeds is an obligation of the body.],
  label: "lst:quant-capture",
  stacked: true,
)[```viper
var k: Int
assume forall x: Int :: {f(x)}
  f(x) > 1 \ k
```][```vmir
e0: Int  := fresh
e1: Bool := forall e1: Int :: {f(e1)} {
  e2: Int  := f(e1)
  e3: Int  := 1 /i e0
  e4: Bool := e2 >i e3
  result: e4
}
assume e1
```]

#vm[`e0`] is the enclosing #vi[`k`], and the body reaches it at #vm[`e3`],
below the quantifier's own #vm[`e1`]. An inner quantifier's binders are numbered
above an outer's by the same rule.

Quantifiers outside of axioms are checked for well-definedness. Helium makes a
copy of the e-graph before the quantifier, replaces the binders with fresh
values, and then evaluates the body, discharging the side conditions as they
arise and recording the recipe. In an axiom the same walk runs with the
obligations skipped. The side condition of @lst:quant-capture is the divisor at
#vm[`e3`], so the #vi[`assume`] verifies only where #vi[`k != 0`] holds.

Helium keeps the body as a recipe, drawn in @fig:forall-node: the body as a term
graph, with the capture and the binder left open at the bottom.

#figure(
  forall-node,
  caption: [The quantifier from @lst:quant-capture firing on a trigger match. The
    node holds its recipe and one child per capture, so the two holes are filled from
    opposite sides: #vm[`t0`] by the node's child, #vm[`t1`] by the boxed term
    the trigger matched.],
) <fig:forall-node>

The recipe and the triggers are compiled once and kept in a table for the
lifetime of the verified unit. The quantifier e-node carries a reference into
that table and one child per capture, so the body itself never appears in the
e-graph.

A single rewrite rule is responsible for instantiating every quantifier in the program. It finds the
e-classes holding a #vm[`forall`] node, matches the triggers of each one against
the e-graph, and replays its recipe at every new binding a match supplies. VMIR requires every quantifier to
carry at least one trigger group covering all of its binders, since it has no
mechanism to infer one. The same
rule covers nesting: an inner quantifier is a step of the outer recipe, so an
instance builds it as an ordinary node with the outer binding in its children,
and the rule picks it up as soon as it is in the graph. This is why a quantifier
is data rather than a rule of its own, since egg fixes the rule set before a
saturation run and a rule cannot be added in the middle of one.

A match releases the body as the implication $q ==> "body"$, where $q$ is the
quantifier itself, so an instance contributes its body only once $q$ is
#vm[`true`]. Silicon releases an instance under the same guard.

Helium stops short of proving a quantifier. There is no skolemisation, so an
#vi[`assert forall ...`] is discharged where the same quantifier is already
#vm[`true`] in the state, from an earlier assumption.
Existential quantifiers are rejected by the verifier, and their implementation
remains future work.

#para[Comparison with Silicon] The two verifiers differ mainly in their handling of quantifiers. Silicon relies on the underlying SMT solver to handle instantiation, whereas Helium manages this process internally using the rewrite engine. This design grants Helium more granular control over when and how quantifiers are instantiated, but consequently places a greater burden on the verifier to perform these instantiations correctly and efficiently.

The ultimate goal is for Helium to handle quantifiers robustly enough that, should an SMT solver be integrated in the future, the encoding could rely on a fully instantiated, quantifier-free state, eliminating the need for solver-side instantiation entirely.
