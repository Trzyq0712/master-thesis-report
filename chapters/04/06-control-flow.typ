#import "../../macros.typ": *
#import "../../figures/cfg-blocks.typ": cfg-blocks

== Control Flow <sec:impl-cfg>

While the method bodies discussed in @sec:impl-methods execute linearly, this
section details the representation and verification of branching control flow. Our
foundational aim is to enforce structured control flow: an #vi[`if`] statement
reaches the verifier explicitly as a single branch paired with a corresponding
join. This ensures that diverging execution paths remain isolated exactly where
they differ and cleanly reconcile where they intersect. Unfortunately, Viper
inherently lacks this explicit structure; a Prusti method is essentially a
#vi[`goto`] graph defined over labelled blocks. The condition under which a block
is reached is embedded within the program's data as a _reach flag_---an ordinary
boolean variable assigned by the encoder along the taken edge. Helium actively
reconstructs this structured control flow via a dedicated analysis over the typed
body prior to lowering. This section outlines the decomposition into basic
blocks, the role of a block's path condition (cube) during proving, the
propagation and reconciliation of heaps across joins, the handling of nested
branches, and the underlying support for loops within VMIR.

=== Basic blocks

@lst:cfg-branch writes a field on one path and leaves it alone on the other,
which is the smallest program with a join in it, and @fig:cfg-blocks draws the
block graph it lowers to. Everything the rest of the section adds is a
consequence of that one join: the two arms reach it holding different
permission, and the exit demands a single answer.

#lowering(
  caption: [A branch and a join. Both arms read #vm[`h0`], each leaves its own
    heap behind, and #vm[`bb3`] reconciles the two before the exit exhale demands
    the full permission back.],
  label: "lst:cfg-branch",
)[```viper
field val: Int

method step(c: Ref, b: Bool)
    returns (d: Int)
  requires acc(c.val, write)
  ensures acc(c.val, write)
{
  var v: Int := c.val
  if (b) {
    d := 1
    c.val := v + 1
  } else {
    d := 0
  }
}
```][```vmir
method step {
  bb0 <>:
    join:
    e0: Ref := fresh          // c
    e1: Bool := fresh         // b
    e2: step#requires@snap
       := fresh
    h0 := empty inhale
          step#requires(e0, e1)
          @ 1/1 with e2
    body:
    e3: &[val] Int @ 1/1
       := val(e0)
    e4: Int := *[h0] e3       // v
  bb1 <e1> from bb0:
    body:
    e5: Int := e4 + 1
    h1 := h0 assign e3 with e5
  bb2 <!e1> from bb0:
    body:
  bb3 <> join e1 [bb1, bb2]:
    join:
    e6: Int := e1 ? 1 : 0     // d
    h2 := merge e1 ? h1 : h0
    body:
    _, _ := h2 exhale
            step#ensures(
              e0, e1, e6, e2)
            @ 1/1
}
```]

#figure(
  cfg-blocks,
  caption: [The block graph of @lst:cfg-branch. Each block carries its number,
    its cube, and the heap it leaves behind. Two heaps reach #vm[`bb3`] and one
    leaves it.],
) <fig:cfg-blocks>

Structurally, a basic block comprises a path condition (its cube), a record of
its incoming edges, a join phase, a body phase, and an exit heap. The cube
formally defines the logical condition under which the block executes, as denoted
in its header: #vm[`bb1`] executes under #vm[`e1`] and #vm[`bb2`] under
#vm[`!e1`], whereas both the entry block and the join block execute
unconditionally under the empty cube #vm[`<>`]. The join phase explicitly
reconciles incoming states from predecessors, while the body phase contains
straight-line VMIR instructions akin to those described in previous sections.
Finally, the exit heap denotes the state the block propagates forward: #vm[`h1`]
for #vm[`bb1`], and the unmodified #vm[`h0`] for #vm[`bb2`].

Notably, VMIR blocks omit explicit terminators. Instead of declaring successors,
a block explicitly names its predecessors using one of three forms. The entry
block naturally declares no predecessors. A block on a linear path identifies its
single predecessor, as seen where #vm[`bb1`] references #vm[`bb0`]. A join block
specifies a branch condition alongside the two predecessor blocks it merges,
illustrated by #vm[`bb3`] merging #vm[`bb1`] and #vm[`bb2`] under #vm[`e1`].
Orienting edges backwards in this manner ensures that a block's entry state
remains entirely derivable from the block itself. Furthermore, it shifts the
responsibility of state reconciliation into the join phase, rather than forcing
predecessors to preemptively reconcile state upon exit.

Blocks are stored in topological order, so every predecessor precedes its
successor. One forward walk over that order is therefore enough to execute a
method: every heap a block reads has already been built, and no block is visited
twice.

That order exists because a VMIR block graph is acyclic, which Viper's is not. An
edge whose target dominates its source is a back edge, and a method with a loop
has one. We detect those edges, and ask every ordering question of the
graph with them removed, which is a DAG. A cut is an exchange rather than a
deletion, and @sec:impl-loops describes what is exchanged. We consider a cycle entered at more
than one point to be irreducible, and we reject it with a diagnostic.

The reach flags Prusti writes into the program's data cost the verifier nothing,
because they are ordinary boolean variables. A flag is assigned #vi[`false`] in
the prologue and #vi[`true`] on the edge that sets it, so at a block that only
one path reaches, the operands of the guard are literals and the conditional
constant-folds before any statement of the block executes. The branch structure
carried in the data therefore collapses into the block structure the analysis has
already recovered. A structured #vi[`if`] and a pair of #vi[`goto`]s guarded by
flags produce the same block graph, and nothing downstream distinguishes them.

=== Verifying a block

The block's cube, stated unequivocally in its header, holds true for every
instruction within that block. Helium assumes this cube upon entry, ensuring that
any subsequent obligation raised within the block is discharged under this path
condition. Furthermore, the cube inherently contextualizes the permission demands
of its constituent instructions. For instance, the write operation in #vm[`bb1`]
demands the location's full permission bound rather than a fraction scaled by the
branch condition #vm[`e1`]. This is because the branching logic is inherently
managed by the block graph architecture itself rather than by the individual
instructions.

Fixing one cube for the length of a block lets the costly end of the prove ladder
be shared over it. The #vm[`implication_decompose`] tier of @sec:impl-execution
works by cloning the e-graph and assuming in the clone, and inside a block we
clone once: a copy of the state with the block's cube assumed, which every
obligation the block raises then reasons in. We build that copy on the first
obligation to reach the tier, because most blocks never reach it, and mirror
additions and merges into it as the block runs, so it stays in step with the
state. An obligation whose path condition the cube already implies is decided in
the copy outright. One carrying a further literal clones the copy rather than the
ground state, so it starts from a graph in which the cube's consequences have
already been drawn.

Two further properties follow from holding that copy for a whole block. A block
whose cube is contradictory is recognised the first time the copy is built, and
every obligation of the block after that is discharged without further work.
The aliasing question a consume raises under the path condition, whether two
addresses that differ in the state coincide under the cube, is answered by a
lookup in the copy instead of by a saturation of its own. The copy is discarded
when the block ends, since the cube the next block runs under excludes it, and
function and resource bodies have no blocks to hold one over, so they clone per
obligation as @sec:impl-execution describes.

=== Heaps across blocks

A heap is a value (@sec:impl-heap), so a block's entry heap is named rather than
implied. Both arms of @lst:cfg-branch read #vm[`h0`], the heap the prologue built,
and neither disturbs what the other sees. #vm[`bb1`] leaves #vm[`h1`], #vm[`bb2`]
leaves #vm[`h0`] untouched, and those two names are what #vm[`bb3`] has to
reconcile. Nothing about the arrangement is implicit, which is what lets a join
treat its two inputs as data. A variable the two arms disagree about is reconciled in the join phase by a
ternary on the branch condition. #vm[`e6`] is one, and it gives #vi[`d`] the value
#vm[`1`] where the then arm ran and #vm[`0`] where the else arm did. A variable
both arms agree on passes through untouched, and one assigned on a single arm
inherits from that arm. The value ternary and the heap merge beside it select on
the same condition.

=== Merging heaps

The join phase of #vm[`bb3`] holds the instruction that reconciles the two
heaps,

#align(center)[#vm[`h' := merge c ? h1 : h2`]]

which takes the exit heaps of the two predecessors and produces the heap the block
runs on. It resolves them structurally: the two heaps are walked partition by
partition and, within a partition, by canonical location, and each pair of chunks
is settled on its own. Four cases arise, ordered here by how much each
introduces. First, a location held on both arms at the same amount is carried
across unchanged and the branch literal drops, which is the common case, since a
call that takes permission and gives it back leaves both arms holding what they
started with. Second, a location held on both arms at genuinely different amounts
becomes one select on the branch condition, one level deep. Third, a location held
on one arm only is carried across with the branch literal appended to a per-chunk
_reachability guard_, a flat cube kept beside the amount rather than inside it.
Finally, where two chunks' guards differ, so that presence is a disjunction rather
than a cube, the guard moves into the amount, and we count how often that
happens.

@lst:cfg-branch takes the first case. Both arms hold #vi[`c.val`] at #vm[`1/1`],
because a write changes a value and leaves an amount alone, so #vm[`h2`] holds it
at #vm[`1/1`] with no trace of #vm[`e1`] on it, and the exit exhale of the
postcondition finds the full share it demands. @lst:cfg-give takes the second: the
write on the then arm becomes an exhale of half the permission, which is the
smallest change that makes the two arms hold different amounts at one location.

#lowering(
  caption: [A conditional exhale. The merged chunk holds
    #vm[`e1 ? 1/2 : 1/1`], and the postcondition's demand for #vm[`1/2`] is proven
    against each arm of that select in turn.],
  label: "lst:cfg-give",
)[```viper
field val: Int

method give(c: Ref, b: Bool)
  requires acc(c.val, write)
  ensures acc(c.val, 1/2)
{
  if (b) {
    exhale acc(c.val, 1/2)
  }
}
```][```vmir
method give {
  bb0 <>:
    join:
    e0: Ref := fresh          // c
    e1: Bool := fresh         // b
    e2: give#requires@snap
       := fresh
    h0 := empty inhale
          give#requires(e0, e1)
          @ 1/1 with e2
    body:
  bb1 <e1> from bb0:
    body:
    e3: &[val] Int @ 1/1
       := val(e0)
    h1, _ := h0 - e3 @ 1/2
  bb2 <!e1> from bb0:
    body:
  bb3 <> join e1 [bb1, bb2]:
    join:
    h2 := merge e1 ? h1 : h0
    body:
    _, _ := h2 exhale
            give#ensures(e0, e1, e2)
            @ 1/1
}
```]

When merging chunks with different conditional existence, we explicitly track the
guard indicating reachability alongside the permission amount, rather than
baking the guard multiplicatively into the permission itself. A location held
unconditionally on both arms records no guard, smoothly yielding an unconditional
amount upon exit. However, when merging differing conditional amounts, the
resulting permission requires case analysis to evaluate against subsequent demands.
For @lst:cfg-give, to prove that the resulting chunk satisfies a demand for
#vm[`1/2`], we push #vm[`e1`] onto the path condition and prove $1\/2 >= 1\/2$,
then push #vm[`!e1`] and prove $1 >= 1\/2$. The case analysis is therefore handled
structurally during obligation checking rather than being embedded permanently as
a permission term within the state graph.

An arm that is provably unreachable is dropped rather than merged. Prusti's dead
#ru[`match`] arms lower to blocks whose cube is refuted, and selecting the
surviving arm against one of those would build exactly the structure the previous
paragraphs avoid, for a state that cannot arise. Such an arm therefore costs
nothing at either end: its obligations are discharged the moment its cube is
assumed, and its heap never reaches a join.

=== Nested and repeated branches

@lst:cfg-nested nests one branch inside another, which is the shape that tells
whether the machinery above composes: the inner join runs inside an arm that
already carries a cube. Its VMIR side elides the prologue and the arguments of
the exit exhale, both of which @lst:cfg-branch already gives in full.

#lowering(
  caption: [Nested branches. The inner join keeps the cube #vm[`<e1>`] of the arm
    it sits in, and the outer join telescopes back to #vm[`<>`].],
  label: "lst:cfg-nested",
)[```viper
method nest(c: Ref,
    a: Bool, b: Bool)
  requires acc(c.val, write)
  ensures acc(c.val, write)
{
  var v: Int := c.val
  if (a) {
    if (b) { c.val := 1 }
    else   { c.val := 2 }
  } else {
    c.val := 3
  }
}
```][```vmir
method nest {
  bb0 <>: ...
  bb1 <e1> from bb0:
  bb2 <e1, e2> from bb1:
    join:
    e6: Bool := e1 ? e2 : false
    body:
    h1 := h0 assign e4 with 1
  bb3 <e1, !e2> from bb1:
    body:
    h2 := h0 assign e4 with 2
  bb4 <e1> join e6 [bb2, bb3]:
    join:
    h3 := merge e6 ? h1 : h2
  bb5 <!e1> from bb0:
    join:
    e7: Bool := e1 ? false : true
    body:
    h4 := h0 assign e4 with 3
  bb6 <> join e7 [bb5, bb4]:
    join:
    h5 := merge e7 ? h4 : h3
    body:
    _, _ := h5 exhale ...
}
```]

A block's cube is computed once, at lowering time, from its predecessors. Each
incoming edge contributes its source's cube extended by the literal that edge is
taken under, which is how #vm[`bb2`] arrives at #vm[`<e1, e2>`], and the block's
reaching condition is the disjunction of those. A disjunction is not a cube, so
the interesting part is when it collapses back into one. We keep the
reaching condition as a _set_ of cubes and minimise it by the one law that is
value-preserving, $P and x or P and not x = P$: two cubes differing in exactly one
literal's polarity merge into their shared prefix. At #vm[`bb4`] the two arms of
the inner branch differ only in #vm[`e2`], so the law fires and the join is
reached under #vm[`<e1>`]. At #vm[`bb6`] the remaining cubes are #vm[`<e1>`] and
#vm[`<!e1>`], which telescope to #vm[`<>`].

Threading the set rather than materialising it is what makes the telescoping
possible. Where a join's predecessors do not complete a partition, the set is
carried on so that a later join pooling the remaining cubes can finish it. An
#vi[`n`]-way #ru[`match`] decoded into a chain of two-way branches needs exactly
that, because no single join in the chain can see that the cases are exhaustive
and only the last one can. Only a set that genuinely cannot be reduced to a single
cube is materialised into one boolean, and the block is then guarded by that
value. The distinction matters, because a cube is what the prover assumes literal
by literal, while a materialised disjunction is one opaque boolean.

Joins are binary, and a label reached by several #vi[`goto`]s is Prusti's normal
shape. We normalise such a block into a chain of binary joins, each a
synthetic block with an empty body phase, and chain them so that the last arm is
the unguarded fall-through. @lst:cfg-chain is the tail of a three-way merge, where
#vm[`bb7`] is the synthetic block and #vm[`bb8`] the label the program named.

#vmir(
  caption: [A three-way merge as a chain of two binary joins. #vm[`bb7`] is
    synthetic and holds nothing but its own merge.],
  label: "lst:cfg-chain",
)[```vmir
bb7 <> join e7 [bb4, bb6]:
  join:
  h4 := merge e7 ? h2 : h3
  body:
bb8 <> join e1 [bb1, bb7]:
  join:
  h5 := merge e1 ? h1 : h4
  body:
  _, _ := h5 exhale ...
```]

Chaining with an unguarded last arm keeps the select exhaustive by construction.
No leaf stands for "none of the arms", so there is nothing to prove about the arms
covering every case. Manufacturing such a leaf instead would produce a term whose
collapse depends on a proof of exhaustiveness, which is the proof the structural
merge was designed to avoid.

=== Loops <sec:impl-loops>

A loop is any back edge, and source-level #vi[`while`] is a special case of one.
We desugar a #vi[`while`] in the control-flow analysis into the block shape a
hand-written #vi[`goto`] loop already produces, so everything downstream sees a
single loop shape. Prusti relies on that, because it emits no #vi[`while`] at all
and carries its invariants on the loop head's #vi[`label`]. Each head is given a
single forward predecessor by a pre-header, so there is one place to establish the
invariant and one frame to restore afterwards. @lst:cfg-loop is a loop whose
invariant claims one of the two fields the method holds.

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

The cut happens in the join phase of the head, #vm[`bb1`], in three steps. The
invariant is exhaled from the heap the forward predecessor arrived with, which is
the entry obligation and a claim about the state control actually reaches the head
in. What that exhale leaves behind is the _frame_, #vm[`h1`], holding
#vi[`c.other`] and everything else the invariant did not ask for. Every variable
the body assigns is then replaced by a fresh value, which is why the loop guard
tests #vm[`e4`] rather than the value #vi[`g`] had before the loop. Finally the
invariant is inhaled into #vm[`empty`], so the body starts from the invariant and
from the havoc'd values. The frame is an ordinary heap value with a name, so an
edge leaving the loop simply refers to it, however deeply nested that edge is.

The body block #vm[`bb2`] exhales the invariant again at its end and has no
successor. That is the back edge, cut: nothing reads #vm[`h4`], the block graph
stays acyclic, and the topological order the walk relies on survives.
Permission left over at the back edge is not required to be empty, and we
lose it, which is what Silicon does as well.

The exit block restores the frame with the second instruction this section
introduces,

#align(center)[#vm[`h' := union h1 h2`]]

which is the sum of two heaps held at the same time, rather than the
#vm[`merge`], which selects between two alternatives. Permissions at a shared
location add, and values at a shared location are equated only where both sides
hold provably positive permission. That second clause carries the framing story. An invariant
demanding a #vm[`wildcard`] share leaves the frame a positive residual, so the
frame still holds the location and its value survives the loop. An invariant
demanding #vi[`write`] takes everything, the frame's residual holds nothing, and
the value does not survive. Equating the two values outright would fuse a stale
pre-loop value with the loop's havoc'd symbol and erase the havoc on the path
where the loop ran.

The support this buys is deliberately narrow. We deferred contextual resource
resolution, so a body cannot read a frame location it holds no permission to, and
every location the body touches has to be named in the invariant. The invariant is consequently re-lowered at each of the
three sites the cut needs it at, clause by clause, rather than compiled once into
a resource of its own. Two further restrictions come from elsewhere: quantified
permissions are unsupported, which puts an index-based loop over an array out of
reach, and #vi[`decreases`] is ignored, so the guarantee is partial correctness.
The loops Silicon verifies and Helium does not fail on the integer arithmetic gap
of @sec:impl-execution rather than on the cut, and each of them fails on the same
obligation with no loop anywhere in the program.

=== Comparison with Silicon

Silicon threads its heap implicitly through the symbolic state @silicon, so
leaving a loop requires a stack of invariant contexts to recover what the head set
aside. Helium names the frame, and an edge leaving a
loop three blocks deep refers to that name like any other operand. Nesting needs
no stack either, since an edge leaving two loops at once restores their frames
innermost first.

At a join the two differ in what carries the branch. Silicon explores the paths
separately and reasons about the resulting permission terms, so a method exit
gathering several arms reaches a goal that only case analysis closes. The
structural merge settles the same question in the heap representation, so no
method body raises such a goal, and the prove ladder of @sec:impl-execution needs
no case analysis it does not have.

Both cut the back edge, and neither requires the residual there to be empty. The
loop encodings agree on the observable question as well: a program whose invariant
demands a #vm[`wildcard`] share keeps the framed value across the loop in both
verifiers, and the same program demanding #vi[`write`] loses it in both.
