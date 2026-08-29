#import "../../macros.typ": *

== Verification Pipeline <sec:impl-pipeline>

A VMIR program is a flat list of declarations of six kinds. Nothing nests: a
predicate body, a method contract and a domain axiom all sit at the top level.
Helium works over that list in two steps. It fixes an order on the declarations,
and then walks each one in turn.

Three of the six kinds are verification units. A #vm[`resource`] and a
#vm[`method`] each carry a body to walk, a #vm[`function`] carries one unless it
is left uninterpreted, and each walk yields one result. The other three declare
the vocabulary those walks use: a
#vm[`domain`] and an #vm[`adt`] declare a type, and an #vm[`axiom`] states a
fact Helium assumes into the e-graph of every unit before the walk begins
(@sec:impl-data). A contract is a declaration in its own right, so it is a unit
in its own right. A method's precondition and postcondition are verified as
separately as the method is (@sec:impl-methods), a function's clauses the same
way (@sec:impl-functions), and verifying a clause on its own is what confirms
the clause is well defined.

// A three-column summary. The house style of the lowering reference: a rule
// under the header, a hairline between rows, and a ragged prose column, since
// justifying a column this narrow opens rivers in every second row.
#let decl-table(..rows) = {
  set par(justify: false)
  set text(size: 0.95em)
  let head(it) = text(size: 0.78em, weight: "bold")[#it]
  table(
    columns: (auto, auto, 1fr),
    align: (left + top, left + top, left + top),
    inset: (x: 0.5em, y: 0.45em),
    stroke: (x, y) => (
      top: if y == 1 { 1pt + luma(40%) } else if y > 1 { 0.5pt + luma(80%) } else { none },
    ),
    table.header(head[VMIR declaration], head[Unit], head[Leaves behind]),
    ..rows
  )
}

#figure(
  caption: [What each kind of VMIR declaration leaves for the units verified
    after it. Only a resource, a function and a method are walked, and the other
    three kinds supply vocabulary those walks use.],
  decl-table(
    vm[`domain`], [no],
    [a type],

    vm[`adt`], [no],
    [a type, with its constructor, projection and #vm[`@tag`] operations],

    vm[`axiom`], [no],
    [a boolean, assumed into the e-graph of every unit before its walk begins],

    [#vm[`function`] with a body], [yes],
    [the equation #vm[`f(args) == body`], installed as a rewrite rule the first
     time a later unit meets an application of #vm[`f`]],

    [#vm[`function`] with no body], [no],
    [an uninterpreted symbol, and, where the declaration links to an
     #vi[`ensures`], a guarded axiom over the result],

    vm[`resource`], [yes],
    [a record of recipes: two per footprint slot and one for the boolean],

    vm[`method`], [yes],
    [one result],
  ),
) <tbl:decl-summary>

Two rows of @tbl:decl-summary carry more than one Viper construct, which is
what the collapse of @sec:principles buys. A field, a domain function and an
abstract predicate's location are all bodyless functions, so each leaves an
uninterpreted symbol and none of the three is walked. A predicate body and a
method contract are both resources, so both are verified once at their
declaration and both leave a record of recipes. A resource derives its own
location function and snapshot type on demand, which is why those two get no row
of their own.

The order is a topological one over a dependency graph whose nodes are the
units. An edge runs from a dependency to its dependent, and Helium draws one for
the callee of a function call, the resource of an inhale or an exhale, the
contract a declaration links to, and the head of a trigger term. Forming a
location is the one application that draws no edge. Building an address needs no
certificate, and a resource's location function carries the resource's own
identifier, so an edge there would make the recursive predicate of
@sec:impl-predicates depend on itself. A fold and an unfold are ordered
correctly all the same, because each pairs that application with an inhale or an
exhale naming the resource, which is where the edge is recorded.

Helium then takes the strongly connected components of the graph in
dependency-first order. A component of more than one member is a recursion
cycle, and we admit one only where every member is a function, which is what the
limited twins of @sec:impl-functions handle. A recursive resource, a recursive
method, or a function cycle that draws in a resource is rejected by name, so the
scoping principle of @sec:principles reaches the schedule as a refusal rather
than a wrong answer. One refinement then applies to the component order: every
function and resource component runs ahead of every method component. That holds
the dependency order, because nothing depends on a method, and it splits no
cycle, because a method component is always a singleton. Helium verifies one
unit at a time, and a failure ends that unit rather than the run, so every unit
is reported.

Each unit runs in a fresh e-graph over a fresh space of identifiers, so a merge
an earlier unit made does not reach a later one. What crosses is the
certificate. A verified resource leaves its record of recipes
(#pararef(<para:impl-slot-recipes>, [Slots and recipes])), from which a use site
rebuilds its footprint. A verified function leaves its definitional equation,
installed as a rewrite rule the first time a later unit's saturation meets an
application of it. A recursive group is verified against limited twins and
publishes its certificates only once every member of the group is done, so no
member meets another's equation while it is being checked. Scheduling a unit
after everything whose certificate it uses is what puts those records in hand by
the time the walk reaches them.

A resource body, a function body and a method body raise one list of obligations
between them. A dereference demands positive permission, an #vi[`acc`] demands a
non-negative amount, and a division demands a non-zero divisor. Whichever body
raises one, the mechanism of @sec:impl-execution discharges it.
