#import "../../macros.typ": *

== Verification Pipeline <sec:impl-pipeline>

A VMIR program is a flat sequence of declarations. Nothing nests: a predicate
body, a method contract and a domain axiom are all top-level declarations.
Helium computes a dependency order over them and then verifies each unit in that
order.

The order exists because a unit's walk consumes what earlier declarations left
behind. A domain's axioms are assumed into the e-graph before the walk begins, a
function's equation is available to be instantiated, and a resource's recipes are
already recorded, so no walk reconstructs a fact that another declaration is
responsible for. Verifying a unit means walking its body and discharging the
obligations that walk raises, against a state the earlier units have furnished.

Several Viper constructs collapse onto one VMIR declaration, which is why the
kinds are fewer than the constructs. A field and a domain function are both
bodyless #vm[`function`]s, each leaving an uninterpreted symbol and needing no
walk. A predicate body and a method contract are both #vm[`resource`]s, each
walked once at its declaration and leaving a record of recipes.

Helium draws the graph from what each unit names. A unit records the global
names it introduces and the identifiers it mentions, and an edge runs from the
unit introducing a name to every unit that mentions it. The second set is an
over-approximation, since a local variable shadowing a global name still counts
as a mention. That costs an edge, which constrains the order without changing
what any unit proves.

@tbl:decl-summary gives what each kind leaves for the units that follow. Three
of its rows carry a body the verifier walks. The other four declare vocabulary
that later units use without being verified themselves.

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
    table.header(head[VMIR declaration], head[Verified?], head[Leaves behind]),
    ..rows,
  )
}

#figure(
  caption: [What each kind of VMIR declaration leaves for the units verified after it.],
  decl-table(
    vm[`domain`],
    [no],
    [a type],

    vm[`adt`],
    [no],
    [a type, with its constructor, projection and #vm[`@tag`] operations],

    vm[`axiom`],
    [no],
    [a boolean, assumed into the e-graph of every unit before its walk begins],

    [#vm[`function`] with a body],
    [yes],
    [the equation #vm[`f(args) == body`], guarded by the precondition token and
      triggered on it, so it fires wherever a call released that token],

    [#vm[`function`] with no body],
    [no],
    [an uninterpreted symbol, and, where the declaration links to an
      #vi[`ensures`], a guarded axiom over the result],

    vm[`resource`],
    [yes],
    [a record of recipes: two per footprint slot and one for the boolean],

    vm[`method`],
    [yes],
    [nothing: a method body is a terminal node no other unit depends on],
  ),
) <tbl:decl-summary>

A method's contract is a #vm[`resource`] declaration of its own, so its clauses
are verified apart from the body that carries them (@sec:impl-methods), and a
function's clauses are verified apart from the function (@sec:impl-functions).
The well-definedness of a contract is therefore established once, however often
that contract is later used.

No unit may form a dependency cycle. A recursive function would be the one
construct that does, and @sec:impl-functions removes the recursion at
translation, so a body depends on the bodyless twin rather than on the function
it belongs to. Resources cannot recursively depend on each other through
resource inhales or exhales, and using the resource's snapshot ADT or the
location function leaves no dependency edge. Method bodies cannot be depended
upon by any other unit: a method's pre- and postconditions can serve as
dependencies for both the method body and its callers, but the method body
itself is always a terminal node in the graph.

Helium then takes one available unit from the graph at a time. A unit that fails
stops there, and every unit that depends on it is reported as skipped rather than
verified. The units that do not depend on it are still verified, so one failure
does not cost the report on the rest of the program.
