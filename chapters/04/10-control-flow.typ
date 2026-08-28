#import "../../macros.typ": *

== Control Flow <sec:impl-cfg>

Everything so far has been straight-line, and that assumption is discharged here.
A second block is what costs the verifier something: it is where the heap of
@sec:impl-heap acquires the machinery it was deliberately introduced without — a
chunk that is held on one path and not on another, and a demand that has to be
met by a sum rather than by a chunk. The two ends @sec:impl-methods describes are
untouched by any of it; what changes is everything between them.

A Viper method body is a basic-block graph, and the
verifier builds one before it lowers anything. Viper offers two ways to branch and
Prusti uses both: #vi[`goto`] between labelled blocks, and a structured
#vi[`if`] — either wrapping a pair of #vi[`goto`]s, or guarding a run of
statements by a _reach flag_, or by a conjunction of them where the block is
reached through more than one branch, as in @lst:example-body. A control-flow
analysis over the typed body resolves the two into one block graph, and after it
they are indistinguishable; nothing downstream walks a syntax tree.

That the reach flags are ordinary boolean variables rather than syntax is worth
one sentence, because it is what makes the arrangement cheap. #vi[`_from_bb0_to_bb1`]
is assigned #vi[`false`] in the prologue and #vi[`true`] on the edge that sets it,
so at a block that only one path reaches, the guard's operands are literals and
the whole conditional const-folds before the block's statements are executed. The
branch structure Prusti writes into the data therefore collapses into the branch
structure the verifier already has.

Blocks are lowered and executed in topological order, with back edges cut. What
a cut does is an exchange rather than a deletion: the loop's invariant is
exhaled where the edge would have arrived and re-inhaled for the body. That
order is what makes a single forward walk possible: every
predecessor of a block is executed before it, so the state a block starts from is
always available, and no block is ever revisited. Each block is a triple — the
cube it is reached under, a _join phase_ that reconciles its predecessors, and a
_body phase_ that is straight-line VMIR of the kind the preceding sections have
been describing.

#lowering(caption: [A conditional exhale, lowered to blocks.], label: "lst:blocks")[```viper
method m(b: Bool, x: Ref)
  requires acc(x.val_i32)
{
  var v: i32 := x.val_i32
  if (b) {
    exhale acc(x.val_i32)
  } else {
    v := i32_cons(0)
  }
  assert !b ==> v == i32_cons(0)
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
    e3: &[val_i32] i32 @ 1/1
         := val_i32(e1)
    e4: i32 := *[h0] e3
    e5: i32 := i32_cons(0)
  bb1 <e0> from bb0:
    body:
    h1, _ := <e0> h0 - e3 @ 1/1
  bb2 <!e0> from bb0:
    join:
    e6: Bool := e0 ? false : true
    body:
  bb3 <> join e0 [bb1, bb2]:
    join:
    e7: i32 := e0 ? e4 : e5
    h2 := merge e0 ? h1 : h0
    body:
    e8: Bool := e7 == e5
    e9: Bool := e6 ? e8 : true
    assert e9 [h2]
}
```]

The method is invented rather than quoted: a single #vi[`exhale`] under a
condition is the smallest program that forces two heaps to be reconciled, and
#vi[`account_deposit`] does the same thing across six blocks. Everything in it
that is not the branch — the field, its predicate's stored type, the constructor
#vi[`i32_cons`] — is the guiding example's.

The entry block opens with the prologue of @sec:impl-methods, unchanged — the
fresh values, the snapshot handle, the inhale of the precondition into
#vm[`empty`]. The method declares no postcondition, so no exit exhale appears in
the listing; had it declared one, neither end would know that the body branched.
Everything this section is about happens between them, and #vm[`bb3`]'s join
phase is where it becomes visible: two heaps arrive there and one leaves.

A block's cube is written in its header, and every
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
matters because a cube is what the tiered prover can assume literal by
literal, while a materialised disjunction is one opaque boolean.

Because every instruction in a block shares the block's cube, the expensive tier
can be shared too. A block builds at most one scratch graph — a copy of the state
with the cube assumed, saturated once — and every obligation of that block that
needs the path condition is discharged against it. Since the cube is a static
property of the block, the scratch is warm for the second obligation onward, which
is what keeps the tier that clones from being paid per instruction. Function and
resource bodies have no block structure and so keep the per-obligation clone;
there is nothing for them to share.

A variable that the two arms disagree about is reconciled by
a ternary on the branch condition, and #vm[`e7`] above is one: #vi[`v`] is the
constant where the else arm ran and the field's value where the then arm did. A variable
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

The heaps of the two arms are reconciled by a #vm[`merge`]
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

The treatment of guards at a join is the _opposite_ of what @lst:guarded-add
does. A guarded access inside an assertion
pushes its condition into the permission amount and keeps the chunk unconditional;
a join keeps the amount guard-free and carries the condition beside it as a cube.
The problem has the same shape in both places and gets the opposite answer, so a
reader who is not told will assume the first mechanism was simply scaled up.

The reason is cost, and it is specific. Pushing a join's condition into the amount
would build an amount of the form $ternary(c, p, 0)$ at every join a chunk
survives, and a method exit gathering #vi[`n`] arms would carry a tower of them,
each with a #vm[`0`] leaf. Collapsing such a tower back to #vm[`1/1`] — which is
what the exit exhale of the postcondition demands — is not a reduction; it needs a
proof that the branch conditions partition the state — reasoning by cases, which
the prove ladder deliberately does not do, and which the
permission arithmetic does only in the narrow gated form of
#pararef(<para:impl-gate-split>, [Conditional footprints]). Measured on the enum
family of the corpus, that was the sole obligation reaching a split at all, and it
arose exactly once per method exit regardless of how many arms the #ru[`match`]
had.

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

The shape to keep in mind for what follows is a chunk part-way through this
process: a location drained under one condition and untouched otherwise reads
#vm[`e0 ? 0/1 : 1/1`]. Every finding below is about a probe meeting one of those.

The corpus is where this stopped being
straightforward. A #ru[`&mut`] passed into a call is, in Prusti's encoding, a
reborrow: the caller computes a new reference whose address is provably equal to
one it already holds permission for, and the call site then demands permission at
_that_ address. Every failure below is a variant of the same situation — the
demanded location and the held chunk are one location, but not visibly so at the
moment of the lookup — and each turns on the guarded chunks above. They are
reported here as findings, because the fixes are not obvious and three of the
four were arrived at by first getting them wrong.

The first failure concerns where a retry belongs. A reborrow's address meets the
held chunk's address only after the full rule set has run: it reaches through the
snapshot machinery, and the terminating reductions the verifier runs after a heap
operation are not enough to close the gap. So a lookup that misses has to be able
to saturate and try again.

Where that retry sits is the whole of the finding. Placing it in the lookup, so
that every miss saturates, is the obvious implementation and costs a factor of
36 on one benchmark of the corpus — 1.48 seconds to 53.5 — because a lookup that
misses is _normal_: an assertion may legitimately demand permission at a location
nothing is held at, and the ordinary answer is that the demanded amount is
provably zero. Putting the retry after that check inverts who pays. A miss that
the zero test closes never saturates; only an obligation that would otherwise be
reported as a failure does.

The second failure is invisible
to the first fix. A reborrow computed _inside_ an arm has an address whose
equality to the held chunk's is a fact of that arm, so it is in the state as a
guarded implication rather than as a merge of two classes. Matching chunks by
canonical e-class cannot see it, and no amount of saturation on the unguarded
state will make it visible, because the equality is not unconditionally true.

The fix is to route the miss through the under-path-condition lookup instead: the
same collect-the-alias-set path
#pararef(<para:impl-pc-sufficiency>, [Sufficiency under a path condition])
describes, which resolves the address gate under the cube rather than in the
ground state. The consume then proceeds with its debit gated by that cube, so
nothing is taken on the path where the addresses are unrelated.

The third is a soundness bug rather than a
completeness one, and it is what the alias _set_ exists for. Where several held
chunks coincide with the demand under the path condition, the permission at that
location is their sum and nothing less; proving sufficiency against the first
chunk that matches is order-dependent and wrong. The failing case is two
consecutive consumes through a chain of reborrows: the first drains one chunk,
the second matches that same drained chunk, and — if the check looks no further
— sees the permission still sitting in a sibling and succeeds. The location is
then spent twice.

Proving against the sum and distributing the debit across the set closes it. The
case is pinned by a soundness regression test in the suite: two full consumes at one
location, reached through nested equalities, which must not both succeed.

The last is a completeness failure
with a cause in a different section entirely. Re-reading a field after a call
should relate the value read to the one the postcondition established, and it did
not: the occurrence of the function relating them stayed opaque, so two reads of
an unchanged field were provably unrelated.

The cause is that a function's body is captured as a recipe and instantiated at
each occurrence, and the instantiation is gated by a token marking that
the occurrence is a genuine call. Building a recipe prunes whatever the result
does not depend on — and the token's value is read by nothing, so it was pruned.
An occurrence introduced by a method contract therefore arrived without its
token and was never unfolded. The fix belongs where the pruning is, and is stated
there.

A join never approximates. Where two arms cannot be
reconciled structurally the verifier falls back to a representation that is
larger, not to one that is weaker, and a failed obligation under a cube leaves
the cube, the chunk and its guard exactly as they were. A call that cannot be
discharged leaves its transaction half-executed by design: the exhale reports
which location it could not take enough permission from, with the demanded and
held amounts as terms, and the caller's heap up to that point is intact. Either
state is a faithful description of the program point, so the incompleteness sits
in the decision procedure rather than in the record.
