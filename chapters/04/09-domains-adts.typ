#import "../../macros.typ": *

== Domains and ADTs <sec:impl-adts>

The two declaration forms left are the ones that carry no permission at all. A
domain is a set of uninterpreted functions and the axioms relating them; an
#vi[`adt`] is a datatype with constructors that a verifier is expected to know
something about. Prusti uses both heavily and for one purpose: a domain per
primitive Rust type, and an #vi[`adt`] per struct or enum whose values are the
snapshots that predicates store.

#para[Domains] A domain declaration flattens. Its functions become ordinary
function declarations and its axioms become top-level axioms; the domain itself
survives only as a type.

#lowering(caption: [A domain flattens into functions, a type, and axioms.], label: "lst:domain")[```viper
domain Box {
  function box(v: Int): Box
  function unbox(b: Box): Int

  axiom ax_roundtrip {
    forall v: Int :: { box(v) }
      unbox(box(v)) == v
  }
}
```][```vmir
domain Box

function box(e0: Int) -> Box
function unbox(e0: Box) -> Int

axiom ax_roundtrip {
  e0: Bool := forall e1: Int :: {box(e1)} {
    e2: Box := box(e1)
    e3: Int := unbox(e2)
    e4: Bool := e3 == e1
    result: e4
  }
  result: e0
}
```]

An axiom's body is ordinary pure VMIR, and executing it is the same walk as any
other body: each instruction adds its term, and the result is merged with
#vm[`true`]. Axioms are made available up front, before the unit being verified is
walked, and they are _trusted_ — no obligation is checked on an axiom body, not
even division by zero, since an axiom is an assumption about the model rather than
a claim to be discharged.

Nothing about this is heap-dependent, and nothing about it needs quantifiers.
A closed axiom without a #vi[`forall`] is simply a fact merged into the state at
the start. A quantified one is a single value — the #vm[`forall`] on the first
line above — whose instantiation is @sec:impl-quantifiers's subject.

#para[Constructors and projections] An #vi[`adt`] does not introduce anything into
the IR. Its constructors, its field projections and its discriminator are all
ordinary function applications, and what makes them mean something is a side table
the verifier keeps: which function is a constructor of which datatype, at which
variant index, and which function projects which field of it. Nothing in the
instruction language grew a case for datatypes, and no match site in the verifier
had to learn about them; a constructor application is executed exactly as any
other application is.

What the side table buys is a family of rewrite rules, minted once per datatype as
it is first encountered. The first is the projection reduction: a projection
applied to a matching constructor gives the field back,

$ "proj"_i (C(a_0, ..., a_n)) => a_i $

which is what makes the fold–unfold round trip of @sec:impl-predicates exact, and
what makes a snapshot readable without an axiom relating the two.

The rule also commutes into a conditional. Where the argument's class does not
hold the constructor directly but a ternary over two constructions, the
projection is pushed inside and applied to each arm. This is not a convenience:
an enum discriminator's body is a tower of ternaries over boxed values, and a
program comparing the _unboxed_ value never sees a constructor under the
projection unless the rule descends. Because the argument is typically a shared
graph rather than a tree, the descent memoises per class; without that, a graph
with $d$ shared classes is walked along up to $2^d$ paths.

#para[Discriminators] Viper's #vi[`x.isC`] tests which variant a value is. The
obvious encoding gives each variant its own predicate function and each pair of
variants a rule relating them, which is quadratic in the number of variants — and
Prusti's enums are wide.

Instead each datatype gets _one_ discriminator function into the integers, and
#vi[`x.isC`] is lowered to an ordinary equality against the variant's index:

$ "tag"(C_i (...)) => i $

One rule per constructor, not per pair, and the comparison that remains is a
plain equality between integers. Where the scrutinee is a known constructor the
rule fires, the equality's two sides fold to literals, and constant folding
decides it — so a discriminator test on a known value is answered by the analysis
that is running anyway rather than by any datatype reasoning.

Constructor distinctness then comes for free. If a program ever forces two
distinct constructors of one datatype into the same class, congruence merges their
discriminators, and two different integer literals collide in one e-class. That is
a constant-folding contradiction, which is the state saying it is inconsistent —
and an inconsistent state discharges every obligation asked of it, which is
exactly the treatment an unreachable path should get. No disequality edge, no
axiom, and no case split.

Injectivity is stated rather than derived, and it is stated because congruence
runs only forwards. Congruence gives that equal arguments make equal
applications; the converse — two applications of one constructor in a single
e-class force their arguments together, pairwise — is a rule of its own, and it is
sound precisely because constructors are free. This is information that is
otherwise unreachable: the projection rule recovers the same equalities, but only
where an application of the projection already exists, and two constructor terms
can meet with no projection over them anywhere. The contrast with a location
function is worth one clause: those get no such rule, because nothing says a
field's location function is injective, and @sec:impl-heap derives what a program
needs about distinct locations from permission arithmetic instead.

#para[What we do not decide] Everything above runs _forwards_, from a known
constructor or a known discriminator value to its consequences. The two inverse
directions are not available, and they are the honest gap in this section.

The first is inversion: from a discriminator value back to a constructor. Knowing
#vi[`x != one()`] does not yield #vi[`!x.isone`], because nothing states that the
discriminator determines the constructor — and in general it does not, since two
applications of one constructor with different arguments share a tag. For a
nullary variant it does, and that is the case Prusti's enums are full of.

The second is exhaustiveness: from "not this variant and not that one" to "then
it is the remaining one". The discriminator is an ordinary integer-valued
function and nothing constrains its range, so a scrutinee ruled out of every
variant but one is not thereby known to be that one.

Both stay undischarged because an e-graph stores equalities and not their
negations: the reasoning available _from_ a disproven equality is there — a
disproven equality propagates through conditionals, and the contrapositive of
congruence fires where every argument pair but one is already merged — but there
is no store to put a disequality into that is not derived from something already
in the graph.

Two directions would close it. The cheaper is to state what is missing as ordinary
axioms at the declaration: that the discriminator ranges over the declared
variants, and that its value determines the constructor for each nullary variant.
Neither needs new machinery — they are facts of the kind the axiom mechanism
already handles — and the second is what makes the case-splitting tier able to
reason over variants at all. The more invasive is to give the e-graph native
disequality edges, so that distinctness is stored and detected at a merge rather
than being reconstructed from a constant-folding collision. That is a change to
the engine rather than to the encoding, and it is the one that would also make a
program's own #vi[`assume a != b`] first-class under a path condition.

#para[What we record] A discriminator test that cannot be decided is left as an
equality between an application and a literal, in the state, with both sides
intact. Nothing is approximated: the term the verifier could not fold is the term
the program wrote, and a procedure with a theory of datatypes would find it
exactly where it was left.
