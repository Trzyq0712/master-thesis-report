#import "../../macros.typ": *
#import "../../figures/cfg-assume.typ": cfg-assume

== Control Flow <sec:impl-cfg>

So far, in @sec:impl-methods the system verified only control flow-free method
bodies. This section covers what changes when a body branches. Viper's surface
syntax offers several ways to do this: an #vi[`if`] statement, a #vi[`while`]
loop, and a #vi[`goto`] to a labelled block. Together they form a control-flow
graph (CFG), which may contain loops.

The lowering reduces that graph to a CFG that is a directed acyclic graph, an
ordered set of basic blocks the verifier walks without ever meeting a back edge.
Each back edge is cut and exchanged for an appropriately placed loop invariant,
described below, so the burden of control flow analysis falls on the lowering.

A DAG of blocks does not dictate how a verifier proves a branch. It could still
be explored one path at a time, treating each arm as a separate execution fork
(as Silicon does). Helium instead verifies each arm in place and reconciles
them at their merge block. The remainder of this section details how VMIR represents
control flow, and how Helium verifies them in various situations.

#para[Basic blocks] @lst:cfg-assume shows a program that branches and rejoins,
assigning #vi[`v`] a different value in each arm, so the join has to settle on
one value for it.

#viper(
  caption: [A branch and a join. Each arm assigns #vi[`v`] a value the other
    disagrees with.],
  label: "lst:cfg-assume",
)[```viper
method example(b: Bool)
    returns (v: Int)
{
  if (b) {
    v := 1
  } else {
    v := 2
  }
  assert v == (b ? 1 : 2)
}
```]

@fig:cfg-assume gives the VMIR it lowers to, drawn as the block graph it forms.

#figure(
  cfg-assume,
  caption: [The VMIR of @lst:cfg-assume. Each block carries its number, its
    path condition and its predecessors, then its phases; #vm[`bb3`] is reached from both
    arms, and its join phase picks #vi[`v`] with a ternary before its body
    runs.],
) <fig:cfg-assume>

Structurally, a block comprises a path condition, a record of its predecessors,
a join phase, and a body phase. The join phase contains the value and heap
resolution for the basic block, while the body phase is the translation of the
block itself. This separation ensures that an execution-forking verifier could
simply pick the correct values directly, rather than setting them up as a
ternary as Helium does. #vm[`bb1`]'s path condition is #vm[`<e0>`] and
#vm[`bb2`]'s is #vm[`<!e0>`], the split condition in its two polarities, and
#vm[`bb3`] pops it back to what the two arms share, here the empty
#vm[`<>`]. A fact assumed inside a block is collected under that block's path
condition, so it reaches a join only as an implication of it.

VMIR and Helium are built for well-nested branching, where the arms of a split
rejoin at a single point. The arms then carry complementary extensions of one
shared PC, and their disjunction at the join telescopes back to the PC they both
came from, which is why #vm[`bb3`] is reached under #vm[`<>`] rather than under a
disjunction. The lowering keeps each block's reaching condition as a disjunction
of PCs and minimises it by the adjacency law $P and x or P and not x ==> P$
alone, so what it holds is always exactly the block's reach. A #vi[`goto`] can
produce branching that does not nest this way, and the reduction still accepts
it: a block genuinely reached under a disjunction carries a materialised boolean
in place of a PC, since a conjunction cannot express one, and a merge of more
than two predecessors becomes a chain of binary joins. Such a block keeps its
facts guarded by the whole disjunction rather than by a shorter shared prefix.

Each arm assigns #vi[`v`] a value the other disagrees with, so the join cannot
carry the assignment forward as an implication and instead requires a genuine
choice between two e-classes. #vm[`e4 := e0 ? e2 : e3`] makes that choice, using
a ternary on the branch condition to resolve to the value produced by the taken
arm. The heap semantics below encounter an analogous situation when determining
the value a merged chunk carries.

#para[Verifying a block] For any given method, all information is stored in a
single e-graph, the ground e-graph. An obligation raised inside a block is first
attempted there, by the same tier ladder @sec:impl-execution describes for a
branchless body. The four cheaper tiers answer from the ground graph alone. Only
when #vm[`saturate`] leaves the obligation open does Helium build a scratch copy
of the e-graph and assume the block's path condition into it.

Once the scratch exists, the remainder of the block runs the ladder directly on
it, so the cost of assuming the path condition is paid once per block rather than once per
obligation. The ground graph takes on a passive role for the rest of the block,
only recording instructions as they come. It therefore holds nothing the scratch
derived under the path condition, and saturates again when a later block raises an
obligation that needs it. The scratch is discarded at the end of the block, since
an e-graph cannot retract the path condition.

#para[Heaps] A heap operation inside a basic block guards its heap chunk with the block's entire path
condition, not just the local permission amount. Analogous to a fact assumed inside a block, a
chunk's recorded state depends on the validity of its enclosing block's path condition.
@lst:cfg-mix illustrates this by accessing three distinct locations across a branch. The subsequent
join phase must resolve three corresponding cases: an unmodified chunk, a location with diverging
values from different branches, and a chunk that is only conditionally instantiated.

#lowering(
  caption: [Three locations, three fates at the join. #vm[`x.f`] is taken
    before the branch and neither arm touches it; #vm[`x.g`] is taken on both
    arms with a different value each time; #vm[`x.k`] is taken only under
    #vm[`e1`], so the other arm holds no permission to it. The location
    applications are inlined into the heap instructions rather than bound to
    temporaries of their own.],
  label: "lst:cfg-mix",
  placement: auto,
  stacked: true,
  target-lang: "lvmir",
)[```viper
field f: Int, g: Int, k: Int

method example(x: Ref, b: Bool) {
  inhale acc(x.f, write)
  if (b) {
    inhale acc(x.g, write)
    inhale acc(x.k, write)
  } else {
    inhale acc(x.g, write)
  }
}
```][```lvmir
method example {
  bb0 <>:
    join:
    e0: Ref := fresh     // x
    e1: Bool := fresh    // b
    body:
    h0 := empty + f(e0) @ 1/1 with fresh   // v0
  bb1 <e1> from bb0:
    body:
    h1 := h0 + g(e0) @ 1/1 with fresh      // v1
    h2 := h1 + k(e0) @ 1/1 with fresh      // v3
  bb2 <!e1> from bb0:
    body:
    h3 := h0 + g(e0) @ 1/1 with fresh      // v2
  bb3 <> join e1 [bb1, bb2]:
    join:
    h4 := merge e1 ? h2 : h3
}
```]

@fig:cfg-mix-table lays out what each arm leaves #vm[`x.f`], #vm[`x.g`] and
#vm[`x.k`] holding, and what #vm[`bb3`]'s merge does with the three.

#let cfg-mix-table = {
  set par(justify: false)
  set text(size: 0.95em)
  let head(it) = text(size: 0.78em, weight: "bold")[#it]
  table(
    columns: (auto, auto, 1fr, 1fr, 1fr),
    align: (left + horizon, left + horizon, left, left, left),
    inset: (x: 0.6em, y: 0.45em),
    stroke: (x, y) => (
      top: if y == 1 { 1pt + luma(40%) } else if y > 1 { 0.5pt + luma(80%) } else { none },
    ),
    table.header(
      head[],
      head[],
      head[#vm[`bb1`] exit (#vm[`h2`])],
      head[#vm[`bb2`] exit (#vm[`h3`])],
      head[#vm[`bb3`] merge (#vm[`h4`])],
    ),
    table.cell(rowspan: 2)[#vm[`x.f`]], [amount],
    [#vm[`1/1`]], [#vm[`1/1`]], [#vm[`1/1`]],
    [value],
    [#vm[`v0`]], [#vm[`v0`]], [#vm[`v0`]],
    table.cell(rowspan: 2)[#vm[`x.g`]], [amount],
    [#vm[`1/1`]], [#vm[`1/1`]], [#vm[`1/1`]],
    [value],
    [#vm[`v1`]], [#vm[`v2`]], [#vm[`e1 ? v1 : v2`]],
    table.cell(rowspan: 2)[#vm[`x.k`]], [amount],
    [#vm[`1/1`]], [--], [#vm[`e1 ? 1/1 : 0/1`]],
    [value],
    [#vm[`v3`]], [--], [#vm[`v3`]],
  )
}

#figure(
  caption: [The amount and value each location carries out of #vm[`bb1`] and
    #vm[`bb2`], and what #vm[`bb3`]'s merge produces from them. #vm[`x.f`]
    passes through unchanged; #vm[`x.k`]'s amount collapses to #vm[`0/1`] on
    the arm that never added it, and its value is left as #vm[`bb1`]'s
    regardless, since nothing can read it where the amount is zero.],
  cfg-mix-table,
) <fig:cfg-mix-table>

The merge operation in #vm[`bb3`] (#vm[`h4 := merge e1 ? h2 : h3`]) reconciles #vm[`x.f`],
#vm[`x.g`], and #vm[`x.k`] based on their modifications:
- *Unmodified Locations*: #vm[`x.f`] is defined before the branch and remains unmodified. Consequently, both arms yield identical chunks, and its value #vm[`v0`] propagates to #vm[`h4`] without requiring conditional selection.
- *Divergent Values*: #vm[`x.g`] receives full permissions in both arms but is assigned different values. The merge preserves the permission amount (#vm[`1/1`]) and introduces a ternary expression to select the appropriate value (#vm[`e1 ? v1 : v2`]).
- *Conditional Presence*: #vm[`x.k`] is only added in one arm (#vm[`bb1`]). The merge treats the missing chunk in #vm[`bb2`] as having a #vm[`0/1`] permission amount, resulting in a conditional permission #vm[`e1 ? 1/1 : 0/1`]. Its value remains unconditionally #vm[`v3`]: any read access requires a positive permission amount, rendering the value unobservable on the path where it was not defined.

In summary, a chunk's amount and value at a join are guarded by the path condition of its originating arm. Chunks unmodified by either arm pass through the join directly. For locations modified on both paths, the join constructs a conditional value selection, mirroring the ternary construction for plain local variables (as seen for #vi[`v`] in @lst:cfg-assume). For locations modified on only one path, the join conditionally resolves the permission amount, propagating the value unconditionally.

This dynamic resolution strategy naturally extends to unreachable paths. @lst:cfg-dead demonstrates a scenario where one branch is statically dead, yet the subsequent join still must produce a unified heap state to satisfy a trailing #vi[`exhale`].

#lowering(
  caption: [A dead arm. #vm[`bb0`] assumes #vm[`e1`] directly, so #vm[`bb2`]'s
    path condition #vm[`<!e1>`] is unsatisfiable, but the lowering has no way to
    see that, so #vm[`bb3`]'s join is an ordinary merge
    #vm[`h1 := merge e1 ? h0 : empty`], unconditionally framing the untouched
    heap from #vm[`bb2`].],
  label: "lst:cfg-dead",
  placement: auto,
  target-lang: "lvmir",
)[```viper
method dead(x: Ref, b: Bool)
{
  assume b
  if (b) {
    inhale acc(x.f)
  } else {
    assert false
  }
  exhale acc(x.f)
}
```][```lvmir
method dead {
  bb0 <>:
    join:
    e0: Ref := fresh          // x
    e1: Bool := fresh         // b
    body:
    assume e1
  bb1 <e1> from bb0:
    body:
    h0 := empty + f(e0) @ 1/1 with fresh   // x.f
  bb2 <!e1> from bb0:
    body:
    assert false
  bb3 <> join e1 [bb1, bb2]:
    join:
    h1 := merge e1 ? h0 : empty
    body:
    h2, _ := h1 - f(e0) @ 1/1
}
```]

In @lst:cfg-dead, the condition #vi[`b`] is assumed true before the branch. Consequently,
#vm[`bb2`]'s path condition (#vm[`<!e1>`]) contradicts the ground e-graph. During verification,
Helium can discover that a block is unreachable by proving its path condition false. In this example,
Helium identifies #vm[`bb2`] as dead code.

While the structural shape of #vm[`bb3`]'s join remains unchanged, its evaluation is simplified by
the contradiction. At the join point, Helium exclusively selects values and heaps from the reachable arm
(#vm[`bb1`]). Crucially, this allows Helium to successfully discharge the #vi[`exhale`] obligation in
#vm[`bb3`] because the merged heap #vm[`h1`] eagerly resolves to #vm[`h0`], without the `else` branch
ever needing to contribute the permission chunk.

This optimization is motivated in part by Prusti's encoding of #ru[`match`]
expressions, where the fallthrough arm is designed to be unreachable. Because a #ru[`match`] is an
expression, it must yield a value across all control-flow paths. This mechanism enables Helium to
verify that the unreachable fallthrough cannot affect the merged result, allowing it to be safely ignored.

#para[Loops] The lowering to VMIR treats all loops identically, whether they originate from unstructured #vi[`goto`] control flow (as encoded by Prusti) or from source-level #vi[`while`] loops. The control-flow analysis reduces both into a uniform block structure. @lst:cfg-loop demonstrates a loop whose invariant claims one of the two fields the method holds.

#lowering(
  caption: [The loop cut. #vm[`h1`] is the frame, holding the permission the
    invariant did not ask for, and #vm[`h5`] is the sum of the frame and what the
    body ended with.],
  label: "lst:cfg-loop",
  placement: auto,
)[```viper
field val: Int
field other: Int

method spin(c: Ref, b: Bool)
  requires acc(c.val, write)
        && acc(c.other, write)
  ensures acc(c.val, write)
       && acc(c.other, write)
{
  var g: Bool := b
  while (g)
    invariant acc(c.val, write)
  {
    c.val := 1
    g := false
  }
}
```][```vmir
method spin {
  bb0 <>:
    join:
    e0: Ref := fresh          // c
    e1: Bool := fresh         // b
    e2: spin#requires@snap
       := fresh
    h0 := empty inhale
          spin#requires(e0, e1)
          @ 1/1 with e2
    body:
  bb1 <> from bb0:
    join:
    e3: &[val] Int @ 1/1
       := val(e0)
    h1, _ := h0 - e3 @ 1/1
    e4: Bool := fresh         // g
    h2 := empty + e3 @ 1/1
          with fresh
    body:
  bb2 <e4> from bb1:
    body:
    h3 := h2 assign e3 with 1
    h4, _ := h3 - e3 @ 1/1
  bb3 <!e4> from bb1:
    join:
    h5 := union h2 h1
    body:
    _, _ := h5 exhale
            spin#ensures(e0, e1, e2)
            @ 1/1
}
```]

The verification of a loop proceeds by cutting its back edges. Before entering the loop header, the invariant is exhaled from the incoming heap. This leaves behind a frame (#vm[`h1`]) containing any state the invariant did not claim. At the loop head, the invariant is inhaled fresh, and any modified locals are havoced (replaced with fresh variables). At the loop's back edge, the invariant is exhaled again.

Currently, support for invariants is minimal: the invariant is simply inlined at these three sites. In the future, we intend to introduce a contextual VMIR resource for invariants, similar to how #vi[`forall`] quantifiers are handled. This would allow the well-formedness (WF) of the invariant to be checked only once, and the same contextual resource recipe could be cleanly reused at the pre-header, the loop body inhale, and any loop-back edges.

On any loop exit, the framed state is restored using the #vm[`union`] operation:

#align(center)[#vm[`h5 := union h2 h1`]]

This operation takes whatever heap was produced inside the loop (#vm[`h2`]) and unions it with whatever remained in the frame from before the loop head (#vm[`h1`]).

#para[Comparison with Silicon] A fundamental distinction between Helium and Silicon lies in their approach to control-flow verification. Silicon employs symbolic execution, exploring each execution path separately. Conditional branches fork the verification state: one path assumes the condition is true, while the other assumes it is false, and each proceeds independently. While this path-enumeration strategy inherently risks exponential explosion, aggressive pruning of dead execution paths often renders it tractable in practice.

In contrast, Helium avoids forking the verification state entirely, instead structurally merging divergent paths at join points. This approach avoids the exponential blowup associated with sequential branching. However, it requires Helium to maintain a larger, more complex unified state that encodes all possible path outcomes simultaneously. Consequently, the solver must often consider all states at once, making some obligations more difficult to discharge.

Furthermore, Helium's unified state is currently susceptible to *branch pollution*, where facts derived within one execution arm can unintentionally leak and influence the reasoning in parallel arms. While this leakage does not compromise soundness, it introduces verification unpredictability: benign code reorderings can sometimes alter verification outcomes. Silicon's isolated path exploration inherently prevents this phenomenon.

Importantly, branch pollution is an artifact of the current implementation rather than a fundamental limitation of join-based verification. @sec:future-work discusses potential mitigations, such as strictly isolating fact derivation within individual branches and explicitly reconciling them only at join points.
