#import "../../macros.typ": *

== Verification Pipeline <sec:impl-pipeline>

A VMIR program comprises a flat sequence of declarations falling into six
distinct categories. Importantly, these declarations never nest: predicate
bodies, method contracts, and domain axioms all exist exclusively at the top
level. Helium processes this flat list in two consecutive phases. First, it
computes a dependency-based execution order over the declarations; subsequently,
it verifies each unit in that established sequence.

@tbl:decl-summary summarizes these six declaration types. They strictly partition into two groups: three constitute active verification units that encapsulate a body requiring traversal, while the other three merely establish the vocabulary utilized during those traverses.

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
    [the equation #vm[`f(args) == body`], installed as a rewrite rule the first
      time a later unit meets an application of #vm[`f`]],

    [#vm[`function`] with no body],
    [no],
    [an uninterpreted symbol, and, where the declaration links to an
      #vi[`ensures`], a guarded axiom over the result],

    vm[`resource`],
    [yes],
    [a record of recipes: two per footprint slot and one for the boolean],

    vm[`method`],
    [yes],
    [one result],
  ),
) <tbl:decl-summary>

Importantly, our unified design maps multiple source-level Viper constructs onto single VMIR declarations. For instance, a field and a domain function are both treated as bodyless #vm[`function`]s, leaving an uninterpreted symbol without requiring a separate verification walk. Similarly, a predicate body and a method contract are both encoded as #vm[`resource`]s; each is verified once at declaration, yielding a reusable record of recipes.

Because a method's contract is an independent #vm[`resource`] declaration, its pre- and postconditions are verified entirely separately from the method body itself (@sec:impl-methods). The same isolation applies to a function's clauses (@sec:impl-functions), ensuring that their well-definedness is confirmed independently of their usage.

To establish the execution schedule, Helium constructs a dependency graph among the verifiable units by drawing directed edges from dependencies to their dependents.

Crucially, we allow functions to form dependency cycles (enabling mutual recursion), and these are the only units allowed to do so. All other constructs strictly prohibit recursive dependencies. For example, resources cannot recursively depend on each other through resource inhales or exhales (using the resource's snapshot ADT or the location function leaves no dependency edge). Furthermore, method bodies cannot be depended upon by any other unit. While a method's pre- and postconditions can serve as dependencies for both the method body and its callers, the method body itself is always a terminal node in the graph.

Verification proceeds by taking one available unit from the graph at a time. When a unit fails verification, Helium halts its execution. Consequently, any downstream dependents are immediately aborted and reported as having failed due to an unresolved verification dependency.
