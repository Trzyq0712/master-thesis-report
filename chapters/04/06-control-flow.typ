#import "../../macros.typ": *

== Control Flow <sec:impl-cfg>

So far, in @sec:impl-methods the system verified only control flow-free method
bodies. This section covers what changes when a body branches. Viper's surface
syntax offers several ways to do this: an #vi[`if`] statement, a #vi[`while`]
loop, and a #vi[`goto`] to a labelled block. In VMIR, all are reduces to a single
representation before verification begins, shifting the burden of control flow
analysis to the lowering phase.

This representation is an ordered set of basic blocks forming a directed acyclic
graph (DAG), ensuring the verifier never encounters back edges. Instead of
deleting back edges, the reduction exchanges them for a appropriately placed loop
invariant constructions, which @sec:impl-loops describes later. The result is a
simplified representation that a verifier can evaluate directly.

A DAG of blocks does not dictate how a verifier proves a branch. It could still
be explored one path at a time, treating each arm as a separate execution fork
(as Silicon does). Helium instead verifies each arm in place and reconciles
them at their merge block. The remainder of this section details how VMIR represents
control flow, and how Helium verifies them in various situations.

=== Basic blocks

@lst:cfg-assume shows the smallest program that branches and rejoins. Its two arms
diverge in two distinct ways: #vi[`v`] retains a single identity but each arm
assumes a different fact about it, whereas #vi[`w`] is assigned a genuinely
different value in each arm. The join must handle the two differently, keeping
#vi[`v`]'s facts separate while selecting a single value for #vi[`w`].

#lowering(
  caption: [A branch and a join. Each arm assumes a different fact about
    #vi[`v`], and assigns #vi[`w`] a genuinely different value; #vm[`bb3`]
    proves both facts about #vi[`v`], each guarded by the literal that
    produced it, and picks #vi[`w`]'s value with a ternary on that same
    literal.],
  label: "lst:cfg-assume",
  stacked: true,
)[```viper
method example(b: Bool)
    returns (v: Int, w: Int)
{
  if (b) {
    assume v == 42
    w := 1
  } else {
    assume v == 32
    w := 2
  }
  assert b ==> v == 42
  assert !b ==> v == 32
  assert w == (b ? 1 : 2)
}
```][```vmir
method example {
  bb0 <>:
    join:
    e0: Bool := fresh  // b
    e1: Int := fresh   // v
    body:
  bb1 <e0> from bb0:
    body:
    e2: Bool := e1 == 42
    assume e2
    e9: Int := 1        // w
  bb2 <!e0> from bb0:
    body:
    e3: Bool := e1 == 32
    assume e3
    e10: Int := 2       // w
  bb3 <> join e0 [bb1, bb2]:
    join:
    e11: Int := e0 ? e9 : e10 // w
    body:
    e4: Bool := e1 == 42
    e5: Bool := e0 ==> e4
    assert e5
    e6: Bool := e1 == 32
    e7: Bool := e0 ? false : true //!b
    e8: Bool := e7 ==> e6
    assert e8
    e12: Int := e0 ? 1 : 2
    e13: Bool := e11 == e12
    assert e13
}
```]

Structurally, a block comprises a path condition , a record of its
predecessors, a join phase, and a body phase. The join phase contains the value
and heap resolution for the basic block, while the body phase is the translation
of the block itself. This separation ensures that an execution-forking verifier
could simply pick the correct values directly, rather than setting them up as a
ternary as Helium does. Returning to the path conditions, #vm[`bb1`]'s cube is
#vm[`<e0>`] and #vm[`bb2`]'s is #vm[`<!e0>`], representing the split condition in
positive and negative polarities. The #vm[`assume`] in each arm's body phase
carries the branch's knowledge forward: instead of assigning to #vm[`e1`], it
records a fact into the block's state, making it visible to every subsequent
instruction in that block.

At #vm[`bb3`], the join pops the cube back to what the two arms share, which
here is the empty cube #vm[`<>`]. For this reason, neither assumed fact unconditionally survives
into the join: #vm[`e1 == 42`] only holds given #vm[`e0`], so the
join can only state it guarded by #vm[`e0`]. A fact assumed under a block's cube
is only available at a join as an implication of that cube. This allows
#vm[`bb3`] to prove both #vm[`e0 ==> e1 == 42`] and #vm[`!e0 ==> e1 == 32`] without
contradiction: the two facts disagree, but neither is asserted outright.

#vi[`w`] takes the other path: each arm assigns it a value the other arm
disagrees with, rather than merely assuming a fact about a shared one. Thus, the
join cannot use an implication and instead requires a genuine choice between
two e-classes. #vm[`e11 := e0 ? e9 : e10`] makes that choice, using a ternary on the
branch condition to resolve to the value produced by the taken arm. The heap
semantics below encounter an analogous situation when determining the value a merged chunk carries.

=== Verifying a block

For any given method, all information is stored in a single e-graph—the ground
e-graph. An obligation raised inside a block is first attempted in this ground
e-graph, exactly as @sec:impl-execution describes for a branchless body. If that
fails, Helium builds a scratch copy of the e-graph and assumes the block's cube
into it. Once this scratch copy exists, every subsequent obligation in the block
is attempted against it rather than the ground graph. Thus, the cost of assuming
the cube is paid once per block, rather than once per obligation. Additions and
merges triggered by the block's instructions are mirrored into the scratch graph
as they occur, keeping it synchronized with the ground state without repeatedly
re-deriving the cube's consequences.

Only what the scratch graph derives is recorded back into the ground e-graph.
Since an e-graph cannot be "unassumed," the scratch copy is discarded when the block ends.
The next block then starts from the ground graph, exactly as it stood
before the previous block's obligations were processed.

=== Heaps

A heap operation inside a basic block guards its heap chunk with the block's entire path
condition, not just the local permission amount. Analogous to the #vm[`assume`] statements in
@lst:cfg-assume, a chunk's recorded state depends on the validity of its enclosing block's cube.
@lst:cfg-mix illustrates this by accessing three distinct locations across a branch. The subsequent
join phase must resolve three corresponding cases: an unmodified chunk, a location with diverging
values from different branches, and a chunk that is only conditionally instantiated.

#lowering(
  caption: [Three locations, three fates at the join. #vm[`x.f`] is taken
    before the branch and neither arm touches it; #vm[`y.f`] is taken on both
    arms with a different value each time; #vm[`z.f`] is taken only under
    #vm[`e3`], so the other arm holds none of it at all.],
  label: "lst:cfg-mix",
  stacked: true,
)[```viper
field f: Int

method example(x: Ref, y: Ref, z: Ref, b: Bool) {
  inhale acc(x.f, write)
  if (b) {
    inhale acc(y.f, write)
    inhale acc(z.f, write)
  } else {
    inhale acc(y.f, write)
  }
}
```][```vmir
function f(e: Ref): &[f] Int @ 1/1

method example {
  bb0 <>:
    join:
    e0: Ref := fresh          // x
    e1: Ref := fresh          // y
    e2: Ref := fresh          // z
    e3: Bool := fresh         // b
    h0 := empty
    body:
    e4: &[f] Int := f(e0)     // x.f
    h1 := h0 + e4 @ 1/1 with fresh   // v0
    e5: &[f] Int := f(e1)     // y.f
  bb1 <e3> from bb0:
    body:
    h2 := h1 + e5 @ 1/1 with fresh   // v1
    e6: &[f] Int := f(e2)     // z.f
    h3 := h2 + e6 @ 1/1 with fresh   // v3
  bb2 <!e3> from bb0:
    body:
    h4 := h1 + e5 @ 1/1 with fresh   // v2
  bb3 <> join e3 [bb1, bb2]:
    join:
    h5 := merge e3 ? h3 : h4
}
```]

@fig:cfg-mix-table lays out what each arm leaves #vm[`x.f`], #vm[`y.f`] and
#vm[`z.f`] holding, and what #vm[`bb3`]'s merge does with the three.

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
      head[#vm[`bb1`] exit (#vm[`h3`])],
      head[#vm[`bb2`] exit (#vm[`h4`])],
      head[#vm[`bb3`] merge (#vm[`h5`])],
    ),
    table.cell(rowspan: 2)[#vm[`x.f`]], [amount],
    [#vm[`1/1`]], [#vm[`1/1`]], [#vm[`1/1`]],
    [value],
    [#vm[`v0`]], [#vm[`v0`]], [#vm[`v0`]],
    table.cell(rowspan: 2)[#vm[`y.f`]], [amount],
    [#vm[`1/1`]], [#vm[`1/1`]], [#vm[`1/1`]],
    [value],
    [#vm[`v1`]], [#vm[`v2`]], [#vm[`e3 ? v1 : v2`]],
    table.cell(rowspan: 2)[#vm[`z.f`]], [amount],
    [#vm[`1/1`]], [--], [#vm[`e3 ? 1/1 : 0/1`]],
    [value],
    [#vm[`v3`]], [--], [#vm[`v3`]],
  )
}

#figure(
  caption: [The amount and value each location carries out of #vm[`bb1`] and
    #vm[`bb2`], and what #vm[`bb3`]'s merge produces from them. #vm[`x.f`]
    passes through unchanged; #vm[`z.f`]'s amount collapses to #vm[`0/1`] on
    the arm that never added it, and its value is left as #vm[`bb1`]'s
    regardless, since nothing can read it where the amount is zero.],
  cfg-mix-table,
) <fig:cfg-mix-table>

The merge operation in #vm[`bb3`] (#vm[`h5 := merge e3 ? h3 : h4`]) reconciles #vm[`x.f`],
#vm[`y.f`], and #vm[`z.f`] based on their modifications:
- *Unmodified Locations*: #vm[`x.f`] is defined before the branch and remains unmodified. Consequently, both arms yield identical chunks, and its value #vm[`v0`] propagates to #vm[`h5`] without requiring conditional selection.
- *Divergent Values*: #vm[`y.f`] receives full permissions in both arms but is assigned different values. The merge preserves the permission amount (#vm[`1/1`]) and introduces a ternary expression to select the appropriate value (#vm[`e3 ? v1 : v2`]).
- *Conditional Presence*: #vm[`z.f`] is only added in one arm (#vm[`bb1`]). The merge treats the missing chunk in #vm[`bb2`] as having a #vm[`0/1`] permission amount, resulting in a conditional permission #vm[`e3 ? 1/1 : 0/1`]. Its value remains unconditionally #vm[`v3`]: any read access requires a positive permission amount, rendering the value unobservable on the path where it was not defined.

In summary, a chunk's amount and value at a join are guarded by the path condition of its originating arm. Chunks unmodified by either arm pass through the join directly. For locations modified on both paths, the join constructs a conditional value selection, mirroring the ternary construction for plain local variables (as seen for #vi[`w`] in @lst:cfg-assume). For locations modified on only one path, the join conditionally resolves the permission amount, propagating the value unconditionally.

This dynamic resolution strategy naturally extends to unreachable paths. @lst:cfg-dead demonstrates a scenario where one branch is statically dead, yet the subsequent join still must produce a unified heap state to satisfy a trailing #vi[`exhale`].

#lowering(
  caption: [A dead arm. #vm[`bb0`] assumes #vm[`e1`] directly, so #vm[`bb2`]'s
    cube #vm[`<!e1>`] is unsatisfiable, but the lowering has no way to see
    that, so #vm[`bb3`]'s join is an ordinary merge
    #vm[`h2 := merge e1 ? h1 : h0`], unconditionally framing the unmodified heap from #vm[`bb2`].],
  label: "lst:cfg-dead",
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
```][```vmir
method dead {
  bb0 <>:
    join:
    e0: Ref := fresh          // x
    e1: Bool := fresh         // b
    h0 := empty
    body:
    assume e1
  bb1 <e1> from bb0:
    body:
    e2: &[f] Int := f(e0)     // x.f
    h1 := h0 + e2 @ 1/1 with fresh
  bb2 <!e1> from bb0:
    body:
    assert false
  bb3 <> join e1 [bb1, bb2]:
    join:
    h2 := merge e1 ? h1 : h0
    body:
    e3: &[f] Int := f(e0)
    h3, _ := h2 - e3 @ 1/1
}
```]

In @lst:cfg-dead, the condition #vi[`b`] is assumed true before the branch. Consequently,
#vm[`bb2`]'s path condition (#vm[`<!e1>`]) contradicts the ground e-graph. During verification,
Helium can discover that a block is unreachable by proving its path condition false. In this example,
Helium identifies #vm[`bb2`] as dead code.

While the structural shape of #vm[`bb3`]'s join remains unchanged, its evaluation is simplified by
the contradiction. At the join point, Helium exclusively selects values and heaps from the reachable arm
(#vm[`bb1`]). Crucially, this allows Helium to successfully discharge the #vi[`exhale`] obligation in
#vm[`bb3`] because the merged heap #vm[`h2`] eagerly resolves to #vm[`h1`], without the `else` branch
ever needing to contribute the permission chunk.

This optimization is motivated in part by Prusti's encoding of #ru[`match`]
expressions, where the fallthrough arm is designed to be unreachable. Because a #ru[`match`] is an
expression, it must yield a value across all control-flow paths. This mechanism enables Helium to
verify that the unreachable fallthrough cannot affect the merged result, allowing it to be safely ignored.

=== Loops <sec:impl-loops>

The lowering to VMIR treats all loops identically, whether they originate from unstructured #vi[`goto`] control flow (as encoded by Prusti) or from source-level #vi[`while`] loops. The control-flow analysis reduces both into a uniform block structure. @lst:cfg-loop demonstrates a loop whose invariant claims one of the two fields the method holds.

#lowering(
  caption: [The loop cut. #vm[`h1`] is the frame, holding the permission the
    invariant did not ask for, and #vm[`h5`] is the sum of the frame and what the
    body ended with.],
  label: "lst:cfg-loop",
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

=== Comparison with Silicon

A fundamental distinction between Helium and Silicon lies in their approach to control-flow verification. Silicon employs symbolic execution, exploring each execution path separately. Conditional branches fork the verification state: one path assumes the condition is true, while the other assumes it is false, and each proceeds independently. While this path-enumeration strategy inherently risks exponential explosion, aggressive pruning of dead execution paths often renders it tractable in practice.

In contrast, Helium avoids forking the verification state entirely, instead structurally merging divergent paths at join points. This approach elegantly sidesteps the exponential blowup associated with sequential branching. However, it requires Helium to maintain a larger, more complex unified state that encodes all possible path outcomes simultaneously. Consequently, the solver must often consider all states at once, making some obligations more difficult to discharge.

Furthermore, Helium's unified state is currently susceptible to *branch pollution*, where facts derived within one execution arm can unintentionally leak and influence the reasoning in parallel arms. While this leakage does not compromise soundness, it introduces verification unpredictability: benign code reorderings can sometimes alter verification outcomes. Silicon's isolated path exploration inherently prevents this phenomenon.

Importantly, branch pollution is an artifact of the current implementation rather than a fundamental limitation of join-based verification. @sec:future-work discusses potential mitigations, such as strictly isolating fact derivation within individual branches and explicitly reconciling them only at join points.
