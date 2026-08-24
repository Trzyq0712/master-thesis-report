#import "../../macros.typ": *

== Putting It Together <sec:impl-together>

@sec:example set a contract: every construct in the encoding Prusti emitted for
@lst:example-rust would be accounted for by the end of this chapter. This section
discharges it. The work was done in the sections above; all that is left is to
check that a real encoding contains nothing they do not cover, and that the whole
of it verifies.

The unabridged file is 3371 lines of Viper declaring
151 members. @lst:example-viper showed one instance of each shape; the table below
takes each of those back to the section that owns it, and then accounts for
everything the abridgement dropped.

#table(
  columns: (auto, 1fr),
  stroke: (x, y) => (top: if y == 1 { 1pt + luma(40%) } else if y > 1 { 0.5pt + luma(80%) } else { none }),
  inset: (x: 0.5em, y: 0.45em),
  align: (left + top, left + top),
  table.header(
    text(size: 0.78em, weight: "bold")[In the encoding],
    text(size: 0.78em, weight: "bold")[What executes it],
  ),

  vi[`domain bool`, `i32`, `isize`, `Param`, `TypeOf`,
     `trait_Pointee`],
  [Uninterpreted functions and axioms, flattened at the declaration
   (@sec:impl-domains); the axioms' triggered #vi[`forall`]s become quantifier
   values instantiated by e-matching (@sec:impl-quantifiers).],

  vi[`adt Account`, `Pair`, `Box`, `Type`, …],
  [Ordinary applications plus a side table, with the projection, discriminator
   and injectivity rules created per datatype (@sec:impl-adts).],

  vi[`adt Transaction`, `AccountList`],
  [The multi-constructor case: one discriminator function into the integers, so
   #vi[`.isC`] is an equality against a variant index and constructor
   distinctness falls out of constant folding (@sec:impl-adts).],

  vi[`field val_i32`, `val_bool`, `val_isize`,
     `val_RefMut`, …],
  [A unary location function into a bounded partition of its own
   (@sec:impl-heap-interaction).],

  vi[`predicate own_i32`, `own_Account`, `own_Box`, …],
  [Resources: a heap delta and a boolean, with a derived snapshot type and
   location function (@sec:impl-predicates). #vi[`own_Account`] nests two
   instances of #vi[`own_i32`], so its footprint walk resolves inner addresses
   through the values it has recovered.],

  vi[`predicate own_Transaction`, `own_AccountList`, and their `_owned` variants],
  [The conditional footprint: the discriminant is held outright and each
   variant's payload under an implication on it, so the walk gates a slot on a
   value it has just recovered (@sec:impl-predicates).],

  vi[`predicate own_Param`],
  [The abstract case: an opaque snapshot domain, held and given back but never
   folded (@sec:impl-predicates).],

  vi[`function snap_Account`, `snap_i32`, `snap_Transaction`, …],
  [Heap-dependent: the precondition becomes a wildcard-weakened resource, the
   function takes that resource's snapshot as a trailing parameter, and its
   #vi[`unfolding`] is a scoped unfold of the reconstructed heap
   (@sec:impl-functions).],

  vi[`function generic_Account`, `add_ovf_i32_i32`, `Account_field_1`,
     `Transaction_discr`, …],
  [Bodyless, contract-only: one guarded fact per occurrence, and the fact is an
   equality, which is what the core is built for (@sec:impl-functions).],

  vi[`method assign_Account`, `make_generic_Account`, …],
  [Contracts as resources; a call is an exhale then an inhale, with the
   precondition's snapshot carried across so that a two-state postcondition can
   read the pre-state (@sec:impl-calls).],

  [#vi[`method account_deposit`] and the six other bodies],
  [A prologue inhaling the precondition and an exit exhaling the postcondition
   (@sec:impl-methods), around a block graph — #vi[`goto`], #vi[`if`] over
   #vi[`goto`]s, and #vi[`if`] over reach flags, all resolved into blocks —
   walked block by block, with values joined by ternaries and heaps by a
   structural merge (@sec:impl-cfg).],

  [#vi[`invariant`] on the heads of #vi[`sum_up_to`] and #vi[`sum_balances`]],
  [Back edges found by dominance and cut, with the invariant exhaled at the head
   and re-inhaled into #vm[`empty`] for the body, and the frame summed back at
   the exits (@sec:impl-loops).],

  [#vi[`label`] before every statement, #vi[`old`]],
  [A name for a block's entry heap, read from by #vi[`old`] and #vi[`old[L]`]
   (@sec:impl-calls).],
)

Nothing in the file falls outside the table, and nothing the abridgement dropped
adds a mechanism. The #vi[`TypeOf`] and #vi[`trait_Pointee`] domains are more
uninterpreted functions; the arithmetic family — #vi[`lt_i32_i32`] and its three siblings — is four more bodyless
functions with #vi[`ensures`] clauses; the per-type repetition of predicates,
snapshot functions and assignment methods is the same three shapes at fourteen
types, two of which — the #vi[`body_invariant!`] closures — exist only because
Prusti insists on an invariant. What they add is volume, which is what @sec:results measures.

The whole file verifies: 151 members, no failures. What it costs against
Silicon is @sec:results's subject and is not quoted twice; what the shape of the
proof effort was belongs here, because it is what the preceding sections were
arranged to produce.

The file put 2498 obligations to the prover. 2472 of them — 99% — were answered by
the cheapest tier: the goal was already #vm[`true`] when it was raised, without
the implication with the path condition ever being built. Ten more were closed by
saturating the live state. The remaining sixteen needed the path condition
assumed, and the whole file built eight scratch graphs between them, one per block
that asked for one. Nothing in it reached the last tier, and nothing required a
case split.

That distribution follows from the mechanisms rather than from the program being
easy. Framing is a lookup because a read names its heap
(#pararef(<para:impl-threading>, [Taking permission])); a fold and its unfold
cancel because a projection over a constructor reduces (@sec:impl-predicates); two
calls of one heap-dependent function are congruent because their snapshots are one
term (@sec:impl-functions); a join collapses because a guard is a cube beside the
amount rather than a ternary inside it (@sec:impl-cfg). Each of those turns an
obligation that would otherwise have been a query into one that is already true,
and the first tier is where they all land.
