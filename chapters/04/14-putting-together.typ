#import "../../macros.typ": *

== Putting It Together <sec:impl-together>

@sec:impl-example set a contract: every construct in the encoding Prusti emitted
for @lst:example-rust would be accounted for by the end of this chapter. This
section discharges it. The work was done in the sections above; all that is left
is to check that a real encoding contains nothing they do not cover, and that the
whole of it verifies.

#para[Construct by construct] The unabridged file is 6347 lines of Viper
declaring 139 members. Every one of them is an instance of something already
described.

#table(
  columns: (auto, 1fr),
  stroke: (x, y) => (top: if y == 1 { 1pt + luma(40%) } else if y > 1 { 0.5pt + luma(80%) } else { none }),
  inset: (x: 0.5em, y: 0.45em),
  align: (left + top, left + top),
  table.header(
    text(size: 0.78em, weight: "bold")[In the encoding],
    text(size: 0.78em, weight: "bold")[What executes it],
  ),

  vi[`domain s_Int_i32`, `s_Bool`, `TypeOf`, …],
  [Uninterpreted functions and axioms, flattened at the declaration
   (@sec:impl-adts); the axioms' triggered #vi[`forall`]s become quantifier
   values instantiated by e-matching (@sec:impl-quantifiers).],

  vi[`adt` snapshots, `s_Account_cons`, projections],
  [Ordinary applications plus a side table, with the projection, discriminator
   and injectivity rules minted per datatype (@sec:impl-adts).],

  vi[`field p_Int_i32_val`],
  [A unary location function into a bounded partition of its own
   (@sec:impl-fields).],

  vi[`predicate p_Int_i32`, `p_Account`],
  [Resources: a heap delta and a boolean, with a derived snapshot type and
   location function (@sec:impl-predicates). #vi[`p_Account`] nests three
   instances of #vi[`p_Int_i32`], so its footprint walk resolves inner addresses
   through the values it has recovered.],

  vi[`predicate p_Param`],
  [The abstract case: an opaque snapshot domain, held and given back but never
   folded (@sec:impl-predicates).],

  vi[`function p_Account_snap`],
  [Heap-dependent: its precondition becomes a wildcard-weakened resource, it
   takes that resource's snapshot as a trailing parameter, and its
   #vi[`unfolding`] is a scoped unfold of the reconstructed heap
   (@sec:impl-functions).],

  vi[`function make_generic_s_Account`, `make_concrete_s_Account`],
  [Bodyless, contract-only: one guarded fact per occurrence, and the fact is an
   equality, which is what the core is built for (@sec:impl-functions).],

  vi[`method p_Account_assign`],
  [Contracts as resources; a call is an exhale then an inhale, with the
   precondition's snapshot carried across so that the two-state postcondition can
   read the pre-state (@sec:impl-calls).],

  [#vi[`method m_account_deposit`] and the other bodies],
  [A flat #vi[`goto`] graph walked block by block, with values joined by ternaries
   and heaps by a structural merge (@sec:impl-cfg).],

  [#vi[`label`] per statement, #vi[`old`]],
  [A name for a block's entry heap, read from by #vi[`old[L]`]
   (@sec:impl-calls).],
)

The two constructs the abridged listing dropped are in the same position. The
overflow-checking #vi[`mir_binop_*WithOverflow`] family is a dozen more bodyless
functions with #vi[`ensures`] clauses, and the trait and #vi[`TypeOf`] domains are
more uninterpreted functions and axioms. Neither adds a mechanism; both add
volume, which is what the next chapter measures.

#para[The whole file] It verifies: 139 members, no failures, in 0.81 seconds
end to end, of which 0.76 is verification and the rest parsing, type-checking and
lowering.

The shape of the proof effort is worth one paragraph, because it is the design's
central claim in one number. The file raised 1751 obligations. 1716 of them — 98%
— were answered by the cheapest tier: the goal was already #vm[`true`], either
trivially or because an identical obligation had been discharged earlier and
recorded. Twenty-seven more were closed by saturating the live state. Only eight
needed the path condition assumed, and the whole file built eight scratch graphs
to supply it. Nothing in it required a case split.

That distribution is what the preceding sections were arranged to produce.
Framing is a lookup because a read names its heap
(#pararef(<para:impl-threading>, [Threading the heap])); a fold and its unfold
cancel because a projection over a constructor reduces (@sec:impl-predicates); two
calls of one heap-dependent function are congruent because their snapshots are one
term (@sec:impl-functions); a join collapses because a guard is a cube beside the
amount rather than a ternary inside it (@sec:impl-cfg). Each of those turns an
obligation that would have been a query into one that is already true, and the
first tier is where they all land.
