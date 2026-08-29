#import "../../macros.typ": *

== Verification Pipeline <sec:impl-pipeline>

A VMIR program comprises a flat sequence of declarations falling into six
distinct categories. Importantly, these declarations never nest: predicate
bodies, method contracts, and domain axioms all exist exclusively at the top
level. Helium processes this flat list in two consecutive phases. First, it
computes a dependency-based execution order over the declarations; subsequently,
it verifies each unit in that established sequence.

Of these six declaration types, exactly three constitute active verification
units. Specifically, a #vm[`resource`], a #vm[`function`], and a #vm[`method`]
each encapsulate a body requiring traversal, yielding a distinct verification
result. Conversely, the remaining three declaration types establish the
vocabulary utilized during these traverses: a #vm[`domain`] and an #vm[`adt`]
introduce novel types, while an #vm[`axiom`] asserts a universal fact that Helium
assumes into the e-graph prior to verifying any unit (@sec:impl-data). Notably,
a method contract constitutes an independent declaration, making it a
verification unit in its own right. Consequently, a method's precondition and
postcondition are verified entirely separately from the method body itself
(@sec:impl-methods). The same isolation applies to a function's clauses
(@sec:impl-functions). Verifying these clauses independently intrinsically
confirms their well-definedness.

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

    [#vm[`resource`] with a body], [yes],
    [a record of recipes: two per footprint slot and one for the boolean],

    [#vm[`resource`] with no body], [no],
    [an opaque snapshot type, exchanged whole at a use site],

    vm[`method`], [yes],
    [one result],
  ),
) <tbl:decl-summary>

Two rows of @tbl:decl-summary carry more than one Viper construct, which is
what the collapse of @sec:principles buys. A field and a domain function are
both bodyless functions, so both leave an uninterpreted symbol and
neither is walked. A predicate body and a method contract are both resources, so
both are verified once at their declaration and both leave a record of recipes.
A resource's location function and its snapshot type are derived from the
declaration on demand, which is why the table gives them no row of their own.

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
