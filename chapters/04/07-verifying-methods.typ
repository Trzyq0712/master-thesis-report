#import "../../macros.typ": *

== Verifying Methods <sec:impl-cfg>

Everything so far has been straight-line, and that assumption is discharged here.
A method is the first construct with control flow, and walking one is where the
heap of @sec:impl-heap acquires the machinery it was deliberately introduced
without — a chunk that is held on one path and not on another, and a demand that
has to be met by a sum rather than by a chunk.

Calling a method is a separate concern and needs none of this; it is
@sec:impl-calls.

#para[Blocks and block order] A Viper method body is a basic-block graph, and the
verifier keeps it as one. Prusti emits a flat #vi[`goto`] graph and never a
structured #vi[`if`] or #vi[`while`], so there is no syntax tree to walk in the
first place; a source-level #vi[`if`] is resolved into block structure before
lowering, and after that the two are indistinguishable.

Blocks are lowered and executed in topological order, with back edges cut
(@sec:impl-loops). That order is what makes a single forward walk possible: every
predecessor of a block is executed before it, so the state a block starts from is
always available, and no block is ever revisited. Each block is a triple — the
cube it is reached under, a _join phase_ that reconciles its predecessors, and a
_body phase_ that is straight-line VMIR of the kind the preceding sections have
been describing.

#lowering(caption: [A conditional exhale, lowered to blocks.], label: "lst:blocks")[```viper
method m(b: Bool, x: Ref)
  requires acc(x.f)
{
  var v: Int := x.f
  if (b) {
    exhale acc(x.f)
  } else {
    v := 0
  }
  assert !b ==> v == 0
}
```][```vmir
method m {
  bb0 <>:
    join:
    e0: Bool := fresh
    e1: Ref := fresh
    e2: m#requires@snap := fresh
    h0 := empty inhale
          m#requires(e0, e1) @ 1/1
          with e2
    body:
    e3: &[f] Int @ 1/1 := f(e1)
    e4: Int := *[h0] e3
  bb1 <e0> from bb0:
    body:
    h1, _ := <e0> h0 - e3 @ 1/1
  bb2 <!e0> from bb0:
    join:
    e5: Bool := e0 ? false : true
    body:
  bb3 <> join e0 [bb1, bb2]:
    join:
    e6: Int := e0 ? e4 : 0
    h2 := merge e0 ? h1 : h0
    body:
    e7: Bool := e6 == 0
    e8: Bool := e5 ? e7 : true
    assert e8 [h2]
}
```]

The entry block opens with the method's own prologue: a fresh value per parameter
and return variable, a fresh snapshot handle, and an inhale of the method's
precondition bound to that handle, which is a
resource like any other (@sec:impl-calls). The heap the body works in is therefore
built rather than assumed, and it starts at #vm[`empty`] — a method may assume
only what its contract grants it. The handle is what the entry state is _called_:
nothing constrains it, so the footprint it widens into is as arbitrary as
#vm[`with fresh`] would have made it, but it has a name, and an exit block needs
that name to state the postcondition against the state the method was entered in.
At the other end, each exit block exhales the
postcondition against the final values of the return variables. There is nothing
method-specific in either: they are the resource operations of
@sec:impl-predicates, applied at the two ends of the walk.

#para[Path conditions] A block's cube is written in its header, and every
instruction of the block carries it. It is computed once, at lowering time, from
the predecessors' cubes: each incoming edge contributes its source's condition
extended by the literal that edge is taken under, and the block's condition is the
disjunction of those.

A disjunction is not a cube, so the interesting part is when it collapses back
into one. The reaching condition is kept as a _set_ of cubes and minimised by the
one law that is value-preserving, $P and x or P and not x = P$: two cubes that
differ in exactly one literal's polarity merge into their shared prefix. Where the
predecessors of a block are the two arms of one branch, that law fires
immediately and the join's condition is the branch's own — which is why #vm[`bb3`]
above is reached under #vm[`<>`] rather than under a disjunction. Where they are
not, the set is threaded on rather than materialised, so that a later join pooling
the remaining cubes can complete the partition and telescope the whole chain to
#vm[`<>`]. This is what an #vi[`n`]-way #ru[`match`] decoded into a chain of
two-way branches needs: no single join in the chain can see that the cases are
exhaustive, and only the last one can.

Only when the set genuinely cannot be reduced to a single cube is it materialised
into one boolean value, and the block is then guarded by that. The distinction
matters because a cube is what the tiered prover can assume literal by literal
(#pararef(<para:impl-tiers>, [Discharging an obligation])), while a materialised
disjunction is one opaque boolean.

Because every instruction in a block shares the block's cube, the expensive tier
can be shared too. A block builds at most one scratch graph — a copy of the state
with the cube assumed, saturated once — and every obligation of that block that
needs the path condition is discharged against it. Since the cube is a static
property of the block, the scratch is warm for the second obligation onward, which
is what keeps the tier that clones from being paid per instruction. Function and
resource bodies have no block structure and so keep the per-obligation clone;
there is nothing for them to share.

#para[Joining values] A variable that the two arms disagree about is reconciled by
a ternary on the branch condition, and #vm[`e6`] above is one: #vi[`v`] is #vi[`0`]
where the else arm ran and the field's value where the then arm did. A variable
both arms agree on passes through untouched, and one only defined on a single arm
inherits from that arm.

Joins are binary. An #vi[`n`]-ary merge — a label reached by several #vi[`goto`]s,
which is Prusti's normal shape — is normalised into a chain of binary joins, each
its own synthetic block, folded so that the last arm is the _unguarded_
fall-through. That detail is load-bearing rather than cosmetic. Folding the arms
with a fall-through means the select is exhaustive by construction: there is no
leaf standing for "none of the arms", and so nothing to prove about the arms
covering every case. Manufacturing such a leaf instead would produce a term whose
collapse depends on a proof of exhaustiveness, and that proof is exactly the one
the case-splitting tier would have to do.

#para[Joining heaps] The heaps of the two arms are reconciled by a #vm[`merge`]
instruction in the join phase, before any instruction of the block reads a heap.
It is a structural operation: the two heaps are walked partition by partition and,
within a partition, by canonical location, and each pair of chunks is resolved on
its own.

The resolution has four cases, and they are ordered by how much structure they
have to introduce. A chunk present on _both_ arms with the same amount is carried
across unchanged — the give-back case, and the common one, since a call that
takes permission and returns it leaves both arms holding what they started with.
A chunk present on both arms with genuinely different amounts becomes one
conditional amount, a select on the branch condition. A chunk present on _one_ arm
only is carried across with the branch literal appended to a per-chunk
_reachability guard_: a flat cube, held beside the amount rather than inside it.
Only where two chunks' guards genuinely differ — so that presence is a disjunction
rather than a cube — does the guard get pushed into the amount, and that case is
rare enough to be worth counting.

Values are merged the same way and by the same rule as everywhere else: two
chunks at one location agree only where both are actually held, so the merged
value is the asymmetric pick of @sec:impl-heap with its conditional agreement
assumed, never an outright union.

An arm that is _provably_ unreachable — a block whose cube is refuted, which is
what Prusti's dead #ru[`match`] arms lower to — is not merged at all. Its heap is
dropped and the surviving arm is carried across as it stands. Selecting against a
dead arm would build precisely the structure the previous paragraph avoids, and
for a state that cannot arise.

#para[Guards, and why not ternaries] It is worth being explicit that this is the
_opposite_ of what @lst:guarded-add does. A guarded access inside an assertion
pushes its condition into the permission amount and keeps the chunk unconditional;
a join keeps the amount guard-free and carries the condition beside it as a cube.
The problem has the same shape in both places and gets the opposite answer, so a
reader who is not told will assume the first mechanism was simply scaled up.

The reason is cost, and it is specific. Pushing a join's condition into the amount
would build an amount of the form $ternary(c, p, 0)$ at every join a chunk
survives, and a method exit gathering #vi[`n`] arms would carry a tower of them,
each with a #vm[`0`] leaf. Collapsing such a tower back to #vm[`1/1`] — which is
what the exit exhale of the postcondition demands — is not a reduction; it needs a
proof that the branch conditions partition the state, which is the case split of
#pararef(<para:impl-tiers>, [Discharging an obligation]). Measured on the enum
family of the corpus, that was the sole obligation reaching the splitting tier,
and it fired exactly once per method exit regardless of how many arms the
#ru[`match`] had.

Keeping the guard flat and beside the amount removes the tower rather than
collapsing it. A chunk held on one arm records that fact as a cube; a chunk held
on all of them records nothing, because the branch literal drops as soon as both
sides agree. No #vm[`0`] leaf is ever built, so there is no tower to collapse and
no exhaustiveness to prove. The exit permission comes out as #vm[`1/1`]
structurally.

#para[Sufficiency under a path condition] <para:impl-pc-sufficiency> The guard is
not free: it has to be put
back where an obligation is raised. When a consume reaches a guarded chunk, the
exact obligation of @lst:guarded-add is reconstructed for that one operation —
the amount gated by the guard, $ternary(g, p, 0)$ — proven, and thrown away. The
gated form exists only for the duration of the check, so the heap keeps its flat
representation while sufficiency keeps the semantics it would have had.

The demand itself also stops being a question about one chunk. Two chunks that are
distinct on the face of it may be at one location _under the path condition_ — the
branch may have assumed an equality of the two receivers — and then neither alone
carries the permission the program holds. Where the direct proof fails, the
verifier collects the chunks of the partition whose locations coincide under the
cube, proves sufficiency against their _sum_, and takes the debit _distributed_
across them: each gives up as much as it holds, gated by the same condition, until
the demand is retired. Nothing is merged, because off the path the locations are
genuinely distinct and nothing there was given up; and each member is driven to
its true remainder, so a later operation on any one of them sees the right
amount. Charging the whole debit to the first matching chunk instead is the
unsound version of this: it leaves a partner reporting permission that the
location no longer has.

A branch-structured amount is proven the same way it is stored — per leaf.
Rather than materialising the select into the state and asking about the
resulting term, the verifier pushes the select's condition into the path
condition and requires the property of both arms. The case analysis happens in
the prover's path condition, where it is a cube literal, and never in the state,
where it would be a node that outlives the obligation.

The shape to keep in mind for @sec:impl-calls is a chunk part-way through this
process: a location drained under one condition and untouched otherwise reads
#vm[`e0 ? 0/1 : 1/1`], and every finding in the next section is about a probe
meeting one of those.

#para[What we record] A join never approximates. Where two arms cannot be
reconciled structurally the verifier falls back to a representation that is
larger, not to one that is weaker, and a failed obligation under a cube leaves
the cube, the chunk and its guard exactly as they were. The state after a join is
a faithful description of both arms, which is what lets @sec:beyond-fragment claim
that the incompleteness is in the decision procedure rather than in the record.
