#import "../../macros.typ": *
#import "../../figures/egraph-congruence.typ": egraph-congruence

== Equality Reasoning and E-Graphs <sec:bg-equality>

A core proof asks one question over and over, whether two syntactically
different terms denote the same location. A location is identified by the terms
naming its receiver, and Prusti's encoding reaches a field through a function
applied to that receiver, so one location acquires many spellings
over an execution. Establishing that a permission is held where the program
reads memory means establishing that two such spellings agree.
Permission amounts behave the same way. A caller passing a fraction $p$ to a
callee retains $1 - p$, and when the callee returns the fraction the caller must
establish full permission again, $(1 - p) + p = 1$. Both questions are equalities
between applications of uninterpreted symbols, and equality reasoning alone
settles them.

Equality is reflexive, symmetric and transitive, so a set of assumed equalities
partitions terms into equivalence classes, and two terms are equal exactly when
they share a class. _Congruence_ carries that partition into the structure of
terms: if $x = y$ then $f(x) = f(y)$. From $x = y$ and $f(y) = z$ it therefore
follows that $f(x) = z$. Congruence also propagates. Merging two classes can
make other terms congruent and force further merges, so from $f(x) = z$ and
$f(y) = w$, merging the classes of $x$ and $y$ merges the classes of $z$ and $w$
as well. Repeating until no further merge is possible gives a fixpoint, the
_congruence closure_ of the assumptions.

An _e-graph_ computes that closure. It holds _e-classes_, each an equivalence
class of terms known to be equal, and each e-class holds one or more _e-nodes_.
An e-node applies an operator to e-classes rather than to terms, so one e-node
stands for every term formed by choosing a member of each argument class, and a
graph of modest size represents a large set of terms. Adding a term is a lookup:
an e-node with the same operator over the same argument classes is either
already present or created. Two terms are then equal exactly when the lookup
returns the same class for both, which reduces an equality query to a comparison
of two class identifiers.

After a merge, e-nodes that were distinct may have become congruent, because
their arguments now name the same classes, and every such pair has to be merged
in turn. @fig:egraph-congruence shows one step.
Restoring the invariant until no congruent pair is left is the fixpoint above,
so an e-graph with its invariant restored is a congruence closure.

#figure(
  egraph-congruence,
  caption: [Congruence in an e-graph. A solid box is an e-node, a dashed box is
    the e-class holding it, and an arrow runs from a node to the class of each
    of its arguments. Merging the classes of $x$ and $y$ leaves the two #vm[`f`]
    nodes applied to the same class, so they are congruent and their classes
    merge as well.],
) <fig:egraph-congruence>

Congruence derives only the equalities that follow from the assumptions. A
_rewrite rule_ adds the rest. A rule is a pattern paired with a replacement, and
finding where it applies means matching the pattern against the graph: the match
walks e-nodes from the operator at the pattern's root, binding each pattern
variable to an e-class, and yields one substitution per way the pattern fits.
Applying the rule builds the replacement under that substitution and merges the
result with the class that matched. Because an e-node ranges over classes rather
than terms, a single match covers every term those classes contain, and a single
application speaks for all of them.

_Equality saturation_ applies every rule everywhere it matches, repeatedly,
until no rule produces anything new or a limit is reached. The result extends
the closure with equalities congruence alone does not give, and reaches them
without an explicit proof search over the rules.

Proving two terms equal and proving them different are not symmetric tasks. A
merge proves an equality, and congruence carries it upward at no cost, since
equal arguments make equal applications. Two terms in different classes prove
nothing, because a class records the equalities the assumptions force rather
than the distinctions they permit. A disequality therefore has to be derived.

Arithmetic meets the same boundary from the other side. The laws of arithmetic
are rewrite rules like any other, so saturating over them derives their
consequences, but the rules that make arithmetic useful are also the ones that
enlarge the graph fastest. Commutativity and associativity together generate an
e-node for every permutation of a term's arguments, and distributivity turns a
product of sums into a sum of products. A rule set rich enough for general
arithmetic therefore exhausts the representation long before saturation reaches
the goal, which confines a verifier built on an e-graph to a rule set that
saturates quickly.

None of this machinery is unusual in a prover. An SMT solver maintains an
e-graph of its own, holding the equalities it has derived, and matches a
quantifier's triggers against it, which is e-matching.
The structure is the same one described here. A solver layers theory solvers
and a case-splitting search over that graph, and those layers separate a solver
from the bare congruence closure underneath.

We adopt _egg_ @egg, a Rust library implementing e-graphs and equality
saturation, as the engine for the equality reasoning this work rests on. Its
rules and analyses are written as types in the host language rather than as
patterns in a rule language of its own, so a rule may consult state outside the
graph, memoise its work, or construct a term
conditionally, none of which a pattern expresses. Its one limitation worth
naming is the absence of an undo: an e-graph can be cloned but not rolled back,
so assuming a condition for the duration of a proof means copying the whole
graph.

Egg introduced two techniques of its own. _Rebuilding_ addresses the cost of
restoring congruence after every merge, which repeats work the next merge may
undo. Egg defers the restoration and runs it in batches, which amortises the
cost over a run of merges, so a rebuild stands for the whole congruence closure:
after one, the graph holds every equality the assumptions entail.

An _e-class analysis_ attaches a value drawn from a lattice to each class and
maintains it across merges, so a fact about every term in a class is computed
once and held in one place. The mechanism is abstract interpretation lifted to
the e-graph. Merging two classes joins their values, and a value that changes
propagates to the classes built on top of it, again to a fixpoint.


