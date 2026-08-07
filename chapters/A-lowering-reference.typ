#import "../macros.typ": *

== Lowering Reference <sec:appendix-lowering>

@sec:implementation introduces VMIR one construct at a time and in the order that
explains it best. This appendix is the other view: every construct of the input
language in one place, with what it lowers to and where in the chapter it is
discussed. It is meant to be consulted rather than read.

The rows are not a selection. There is one for each variant of the typed Viper
syntax the frontend produces — declarations, statements, assertion forms and the
heap-dependent expression nodes — so that a construct absent from the table is
absent from the language, not merely from the exposition. The pure operators are
the one deliberate exception: there are two dozen of them, they carry no heap and
each becomes the same operator over e-classes, so they share a single row.

The _support_ column is what @sec:beyond-fragment and the fragment claim of
@sec:approach both rest on:

#table(
  columns: (auto, 1fr),
  stroke: none,
  inset: (x: 0.4em, y: 0.3em),
  [#emph[full]], [Lowered and verified for the whole construct.],
  [#emph[partial]], [Lowered, with a stated restriction — the restriction is named in the row.],
  [#emph[none]], [Rejected by the translator with an #vm[`Unsupported`] error.],
)

#todo[
  *Status of this appendix.* Rows marked #emph[check] in the support column have
  not been read off the translator yet — they are what the chapter says, not what
  `src/translate/` does. Resolve each against the match arm named in the row
  before the draft goes out.

  Completeness is checkable rather than asserted: walk `typed::Declaration`,
  `typed::Statement`, `typed::SpatialExpKind`, `typed::ResourceExpKind` and
  `typed::HeapNode` in `src/viper/typed/ast.rs` and confirm one row each. Do that
  again at write-up freeze, since a new variant will not announce itself here.

  Two rows have no VMIR fragment to show and say so instead: control flow becomes
  block structure rather than instructions, and a `label` becomes a named heap.
  That is correct, not a gap — but it means the table cannot be read as
  "instruction in, instructions out" throughout.
]

// A reference table is scanned column by column, not read, so its prose column is
// set ragged-right: justifying a column this narrow opens rivers in every second
// row and buys nothing.
// A bare section number ("4.5") for the last column. `@sec:..` would print
// "Section 4.5" in every row, and four extra words per row is a column's worth of
// width the VMIR side needs more.
#let sec(label) = context link(label, numbering("1.1", ..counter(heading).at(label)))

#let lower-table(..rows) = {
  set par(justify: false)
  set text(size: 0.95em)
  table(
    columns: (auto, 1fr, auto, auto),
    align: (left + top, left + top, left + top, left + top),
    inset: (x: 0.5em, y: 0.45em),
    stroke: (x, y) => (top: if y == 1 { 1pt + luma(40%) } else if y > 1 { 0.5pt + luma(80%) } else { none }),
    table.header(
      text(size: 0.78em, weight: "bold")[Viper],
      text(size: 0.78em, weight: "bold")[VMIR],
      text(size: 0.78em, weight: "bold")[Support],
      text(size: 0.78em, weight: "bold")[§],
    ),
    ..rows
  )
}

#para[Declarations]

#lower-table(
  vi[`field f: T`],
  [#vm[`function f(e0: Ref): &[f] T @ 1/1`]],
  [full], [#sec(<sec:impl-fields>)],

  vi[`predicate P(x: T) { A }`],
  [#vm[`resource P(..)`] with a body yielding #vm[`(h, b)`], plus the derived
   #vm[`P@snap`] and location function #vm[`P`]],
  [full], [#sec(<sec:impl-predicates>)],

  vi[`predicate P(x: T)`],
  [#vm[`resource P(..)`] with no body; the snapshot type is an opaque domain],
  [full], [#sec(<sec:impl-predicates>)],

  vi[`function f(..): T`],
  [#vm[`function`], plus a self-framed #vm[`f#requires`] resource and an
   #vm[`f#ensures`] boolean function; a heap-dependent one takes its
   precondition snapshot as a trailing parameter],
  [check], [#sec(<sec:impl-functions>)],

  vi[`method m(..) returns (..)`],
  [Contracts become resources; the body becomes a CFG of blocks],
  [check], [#sec(<sec:impl-cfg>)],

  vi[`domain D { .. }`],
  [Uninterpreted functions and axioms],
  [check], [#sec(<sec:impl-adts>)],

  vi[`adt A { .. }`],
  [An #vm[`adt`] plus derived constructor, projection and #vm[`@tag`] functions],
  [check], [#sec(<sec:impl-adts>)],
)

#para[Statements]

#lower-table(
  vi[`var x: T`],
  [One #vm[`fresh`] value per identifier; no heap instruction],
  [full], [#sec(<sec:impl-execution>)],

  vi[`var x: T := e`],
  [The lowering of #vi[`e`], bound to the name. One target per statement:
   a multi-target #vi[`var`] is rejected],
  [partial], [#sec(<sec:impl-execution>)],

  vi[`x := e`],
  [As above, and with the same single-target restriction. A field target is the
   #vi[`x.f := e`] row],
  [partial], [#sec(<sec:impl-heap-interaction>)],

  vi[`x.f := e`],
  [#vm[`h' := h assign(f(x), e)`]],
  [full], [#sec(<sec:impl-heap-interaction>)],

  vi[`x := new(f, g)`],
  [#vm[`fresh`] receiver, then one heap add at #vm[`1/1`] per named field. One
   target, and it must be a local rather than a field],
  [partial], [#sec(<sec:impl-heap-interaction>)],

  vi[`x := new(*)`],
  [—],
  [none], [#sec(<sec:beyond-fragment>)],

  vi[`x := m(args)`],
  [Exhale of the precondition resource, #vm[`fresh`] values for the results, then
   inhale of the postcondition resource against the consumed pre-state snapshot],
  [check], [#sec(<sec:impl-calls>)],

  vi[`inhale A`],
  [#vi[`A`]'s heap delta added left to right, its boolean assumed],
  [full], [#sec(<sec:impl-heap-interaction>)],

  vi[`exhale A`],
  [#vi[`A`]'s heap delta subtracted left to right, its boolean asserted. Value
   reads use the pre-exhale heap; #vi[`perm`] reads track the shrinking one],
  [full], [#sec(<sec:impl-heap-interaction>)],

  vi[`assert A`],
  [Non-destructive: each #vi[`acc(l, p)`] becomes #vm[`perm[h] l >= p`] and the
   whole assertion is asserted as one boolean. The heap is unchanged],
  [full], [#sec(<sec:impl-heap-interaction>)],

  vi[`assume A`],
  [As #vi[`assert`], assumed rather than asserted],
  [full], [#sec(<sec:impl-heap-interaction>)],

  vi[`refute A`],
  [As #vi[`assert`], with the dual outcome],
  [check], [#sec(<sec:beyond-fragment>)],

  vi[`fold P(args)`],
  [#vm[`h' := h fold P(args) p`]],
  [check], [#sec(<sec:impl-predicates>)],

  vi[`unfold P(args)`],
  [#vm[`h' := h unfold P(args) p`]],
  [check], [#sec(<sec:impl-predicates>)],

  vi[`if (c) { .. } else { .. }`],
  [No instruction: resolved into block structure before lowering],
  [check], [#sec(<sec:impl-cfg>)],

  vi[`while (c) invariant I { .. }`],
  [Block structure; the invariant becomes a resource exchanged at the edges],
  [check], [#sec(<sec:impl-loops>)],

  vi[`goto L`],
  [No instruction: a block terminator],
  [check], [#sec(<sec:impl-cfg>)],

  vi[`label L`],
  [No instruction: names the block's entry heap, which is what #vi[`old[L]`]
   reads from],
  [check], [#sec(<sec:impl-cfg>)],
)

#para[Assertions]

#lower-table(
  vi[`acc(x.f, p)`],
  [One heap add or subtract at #vm[`f(x)`], according to the direction],
  [full], [#sec(<sec:impl-heap-interaction>)],

  vi[`acc(P(args), p)`],
  [One #vm[`inhale`] or #vm[`exhale`] instruction over the whole resource],
  [full], [#sec(<sec:impl-predicates>)],

  vi[`A && B`],
  [The two lowerings in order, threading one heap into the next; #vi[`A`]'s
   boolean joins #vi[`B`]'s path condition],
  [full], [#sec(<sec:impl-heap-interaction>)],

  vi[`b ==> A`],
  [#vi[`A`] lowered unconditionally with #vi[`b`] pushed into each permission
   amount as a ternary],
  [full], [#sec(<sec:impl-heap-interaction>)],

  vi[`e`],
  [A pure conjunct: contributes no chunk, only to the boolean half],
  [full], [#sec(<sec:impl-predicates>)],

  vi[`forall x :: A`],
  [—],
  [check], [#sec(<sec:impl-quantifiers>)],
)

#para[Expressions]

#lower-table(
  vi[`x.f`],
  [#vm[`*[h] f(x)`] in a value position; #vm[`f(x)`] alone in an #vi[`acc`] or as
   an assignment target],
  [full], [#sec(<sec:impl-heap-interaction>)],

  vi[`P(args)`],
  [#vm[`P(args)`] — the derived location function],
  [full], [#sec(<sec:impl-predicates>)],

  vi[`f(args)`],
  [A pure application; a heap-dependent callee additionally takes
   #vm[`snap[h] f#requires(..)`] as its trailing argument],
  [check], [#sec(<sec:impl-functions>)],

  vi[`perm(x.f)`],
  [#vm[`perm[h] f(x)`]],
  [check], [#sec(<sec:impl-heap-interaction>)],

  vi[`unfolding P(args) in e`],
  [—],
  [check], [#sec(<sec:impl-predicates>)],

  vi[`old(e)`, `old[L](e)`],
  [#vi[`e`] evaluated against the baseline heap, or against the heap named by
   #vi[`L`]],
  [check], [#sec(<sec:impl-cfg>)],

  vi[`wildcard`],
  [A permission amount only — never a first-class value],
  [check], [#sec(<sec:beyond-fragment>)],

  [Operators, literals],
  [Every unary and binary operator, #vi[`?:`], the literals and #vi[`null`]: the
   same operator over e-classes, constant-folded where its operands are literals],
  [full], [#sec(<sec:impl-execution>)],
)
