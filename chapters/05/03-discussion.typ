#import "../../macros.typ": *
#import "../../generated/attribution-scalars.typ": *
#import "../../generated/attribution-permtree-scalars.typ": *
#import "../../generated/perf-rust-scalars.typ": *

== Discussion <sec:results-discussion>
The per-file ratios of @sec:results-quantitative spread over more than an order
of magnitude, and this section accounts for that spread. Every measurement below
comes from a counter Helium records for itself, and those counters are
deterministic, which makes a claim in their terms stronger than a claim in
milliseconds.

#para[Discharging an obligation] Helium attempts the tiers of
@sec:impl-execution in order and stops at the first that succeeds, a design that
rests on the expensive tier being rare.
@tbl:results-tiers-rust measures how rare it is. The verifier credits exactly one
tier per query, so a share of the ladder is a share of the queries the corpus
raised, and every tier reads the ground e-graph except
#vm[`implication_decompose`], which reads the copy described below.

A query is not the same thing as an obligation, in two directions. The heap
machinery consults the ladder to decide questions it is prepared to hear a no
to, such as whether a demand is provably zero or whether two addresses coincide,
and it reads that no as a fact about the heap rather than as a failure. One
obligation may also raise several queries. Proving that the permission held at a
location covers what an exhale demands descends the tree of guards the amount is
built from and asks a query per leaf, and a leaf whose amount is a conditional
minted by a footprint is retried under the condition and under its negation,
raising a further query for each arm whose amount is not already a literal that
suffices. The arm under the negation is discharged exactly when assuming that
negation refutes itself. The row this table calls #emph[declined] therefore
counts the queries no tier settled, which includes the first attempt at every
leaf that the case split then closes. A member fails to verify only when the
caller has no route left, not when this row is non-empty.

#include "../../generated/attribution-tiers-rust.typ"

The cheapest tiers carry the corpus. #vm[`goal_true`] alone closes
#attr-rust-goal-share of the queries, rebuilding the e-graph and finding the goal
already merged with #vm[`true`] without a single rewrite firing.
#vm[`inconsistent`] fires #attr-rust-dead-block times, every one of them a block
whose own path condition is unsatisfiable rather than an e-graph that has turned
contradictory. Those are the dead arms of @sec:impl-cfg, which a #ru[`match`]
produces in quantity, and the non-vacuity check of @sec:results-quantitative
confirms that the unreachability originates in the encoding rather than in a
state Helium has corrupted. #vm[`implication_true`] fires
#attr-rust-implication-true times, so the weakening it applies earns almost
nothing the tier above had not already closed, and #vm[`saturate`], the first
tier to run a rewrite search, accounts for under half a per cent.

That leaves #vm[`implication_decompose`] at #attr-rust-decompose-share. It is the
only tier that reads a graph with the path condition assumed, and therefore the
only one that pays for a copy. Inside a method body that copy is the block
scratch: the assumption is made once per basic block and every later obligation
of the block reads the scratch that already exists, so the cost is amortised over
the block rather than paid per obligation. The corpus builds
#attr-rust-block-scratch-clones scratches in all, against
#attr-rust-probe-clone obligations that clone the ground graph for themselves,
which are those raised in a function or a resource, where there are no blocks to
amortise the assumption over.

The ladder consequently answers cheaply for almost everything the corpus asks,
and an expensive file does not differ from a cheap one in how often it reaches
the expensive tier. An expensive file pays instead for the declines counted in
the last row, which return the heap machinery to a fallback rather than
discharging an obligation.

#para[The give-back at a join] The per-file ratios run from
#rust-best-ratio down to #rust-worst-ratio, and the files at the bottom share one
shape: a Rust method that mutates through a #ru[`&mut`] inside a #ru[`match`].
Each arm lends a location out and takes it back before the arm ends, and Prusti
encodes the lending and the taking back as ordinary permission transfers guarded
by the arm's condition. The shape is expensive because the give-back does not
name the location the method started with. A reborrow is a fresh reference whose
pointee is equated to the original's by a postcondition, and that postcondition is
released under the arm's guard like every other fact the arm establishes.
@lst:giveback states the shape directly in Viper.

#viper(
  caption: [A location lent out inside an arm and taken back at a second name for
    it. #vi[`q`] is the same reference as #vi[`r`], but only where #vi[`b`] holds,
    so the permission returns at an address the ground e-graph cannot identify
    with the one the release names.],
  label: "lst:giveback",
  placement: auto,
)[```viper
method reborrow(r: Ref) returns (q: Ref)
  requires acc(r.val)
  ensures  acc(q.val) && q == r

method one_arm(r: Ref, b: Bool)
{
  inhale acc(r.val)
  if (b) {
    var q: Ref
    q := reborrow(r)
  }
  exhale acc(r.val)
}
```]

The rule @sec:impl-cfg states for facts, and states again for chunks, denies the
release its lookup. A fact established under a block's path condition reaches the
join as an implication of that condition, and Helium merges the guarded
implication rather than the fact, because a bare merge would assert the fact on
every path and let the verifier assume what it has to prove. Consequently
#vi[`q == r`] holds under #vi[`b`] and nowhere else, #vm[`val(q)`] and
#vm[`val(r)`] resolve to two e-classes, and the partition holds two chunks where
the program holds one location.

The join leaves them apart. It groups the arms' chunks by their canonical
addresses, and two addresses whose equality it cannot establish remain two
entries, each carrying the guard of the arm that produced it. Merging them there
would be unsound, since the location axioms of @sec:impl-heap bound what the
chunks of one partition sum to. Recovering the permission is left to the release,
which has to establish an identity holding only under a guard the ground e-graph
cannot assume, and the file's time goes into that recovery.

Helium reports, per member, the time it spends inside that recovery. Over the
Prusti-generated corpus #attr-giveback-files files of #attr-giveback-files-total
reach it at all, and four spend measurable time there: #attr-giveback-0-case,
#attr-giveback-1-case, #attr-giveback-2-case and #attr-giveback-3-case. The fifth
is #attr-giveback-4-case, which reaches it #attr-giveback-4-consumes times for
#attr-giveback-4-secs and is among the corpus's fastest files against Silicon, so
a file's ratio suffers from reaching the recovery often rather than from
reaching it at all. In #attr-giveback-0-case #attr-giveback-0-members members reach it over
#attr-giveback-0-consumes consumes, and #raw("m_shape_grow") spends
#attr-giveback-m-shape-grow-secs there, #attr-giveback-m-shape-grow-share of its
own verification time.

That figure bounds the recovery's own share of the cost at a tenth. The other
nine tenths are spent on permission proofs that succeed without it. A conditional
footprint gives a location an amount that is a tree of guards with a permission
amount at each leaf, #vm[`1/1`] where the guard grants the permission and
#vm[`0`] where it withholds it, and proving a permission goal means descending
that tree and discharging each leaf under the guards reaching it. Assuming every
such descent away, which is unsound and done here only to price it, splits the
corpus in two. Both columns of @tbl:results-permtree are measured outside a
sweep, so they sit a little under the times @sec:results-quantitative reports,
and the number to read is the difference between them.

#include "../../generated/attribution-permtree.typ"

The descent costs #attr-permtree-branchy-lo to #attr-permtree-branchy-hi on the
#attr-permtree-branchy-files files whose permissions are branch-structured, and
at most #attr-permtree-other-hi on the #attr-permtree-other-files that are not,
with nothing in between. The files that pay for the descent are the files that
reach the give-back recovery, which follows, since a permission lent away under
a guard builds the tree.

The measurement also bounds the explanation, well short of the whole. With every
permission proof free #attr-giveback-0-case still takes
#attr-permtree-worst-assumed against #attr-permtree-worst-walked, a reduction of
#attr-permtree-worst-cut. Most of the file's cost survives that assumption, so
discharging permissions accounts for a quarter of what this file pays and the
remainder lies elsewhere.

The remainder is the size of the state. Helium verifies each member in its own
e-graph, and @fig:results-member-size sets what a member costs against how large
that graph grows. Over the #attr-size-members members of the corpus the
relationship is a power law: time goes as the e-graph to the power
#attr-size-exponent, accounting for #attr-size-fit of the variance across three
orders of magnitude of both quantities. The exponent rises with the graph, to
#attr-size-large-exponent over the #attr-size-large-members members above
#attr-size-large-cut e-nodes. The two populations matter more than either
exponent: the four files reaching the give-back recovery lie on the same line as
the seven that do not, and #rust-worst's members sit at
#attr-size-worst-residual their predicted time, so they are as fast as their
graph size predicts.

#include "../../generated/attribution-member-scatter.typ"

The slow files are therefore slow because they carry more state, at the same
price per e-node the rest of the corpus pays, and that state is branch-implied
information. Helium keeps a single e-graph for every arm, so a fact an arm
establishes enters the graph as an implication of that arm's path condition
rather than as the fact itself. Where both arms of a conditional establish
#vm[`x == 3`], the graph consequently holds #vm[`b ==> x == 3`] and
#vm[`!b ==> x == 3`] as two terms, and neither reduces to #vm[`x == 3`] until
something decides #vm[`b`]. #attr-size-worst-member builds
#attr-size-worst-nodes e-nodes and takes #attr-size-worst-secs, against the
#attr-size-smallest-nodes e-nodes of the smallest member in the corpus. The
families below separate whether that growth is a property of branching or of
the permissions crossing it.

#para[Scaling with branching] The Prusti-generated corpus varies many things at
once. To vary a single parameter we generate two families of Viper programs over
the number of chained conditionals a method contains, chained rather than nested
so that the body has #attr-branch-paths paths at the widest setting while the
source grows linearly. Both close with the same obligation: two locals are updated
identically on every arm, so their equality holds on all paths and proving it is
the join's work rather than any arm's. The first does nothing else. The second
lends a location out inside every arm and takes it back through a reborrow whose
identity with the original holds under that arm's guard alone. Holding the
obligation fixed makes the difference between the curves the cost of the
permission traffic. Helium is measured on the give-back family only to
#attr-branch-perm-helium-depth conditionals, where it already takes
#attr-branch-perm-hi and its e-graph grows by #attr-branch-perm-nodes-growth per
conditional, so its curve stops there while the other three run the full range.

#include "../../generated/attribution-branching.typ"

@fig:results-branching plots both families. Without permission traffic Helium is
flat: it takes #attr-branch-pure-lo at one conditional and #attr-branch-pure-hi
at #attr-branch-depths, while Silicon in its default configuration goes from
#attr-branch-pure-silicon-lo to #attr-branch-pure-silicon-hi as the paths it
explores double. Helium's lead over
that configuration therefore widens with the branching, from
#attr-branch-pure-ratio-lo to #attr-branch-pure-ratio-hi. The e-graph grows by
#attr-branch-pure-nodes-step e-nodes per conditional in @tbl:results-branching-size,
from #attr-branch-pure-nodes-lo to #attr-branch-pure-nodes-hi, and the largest
e-class holds two nodes at every depth: a conditional whose arms agree contributes one
#vm[`ite`] and the arms share everything beneath it. This is the shape
@sec:results-quantitative credits for the top of the ratio range, with everything
else held fixed.

Silicon's growth on the branch-only family is a property of that configuration
rather than of symbolic execution. Bösiger's join points @perf-impr are available
as #raw("--moreJoins 2"), at which Silicon merges the arms of a conditional
wherever it can rather than exploring each path to the end, and this family is
the best case that mechanism can be given: the two arms agree on every variable,
so a merge has one conditional expression to build and no permission to scale.
Under the flag Silicon's curve flattens accordingly, from
#attr-branch-morejoins-lo at one conditional to #attr-branch-morejoins-hi at
#attr-branch-depths, #attr-branch-morejoins-gain faster than its default at the
widest setting. Over the whole range the three configurations grow by
#attr-branch-pure-helium-growth for Helium, #attr-branch-morejoins-growth for
Silicon under the flag and #attr-branch-pure-silicon-growth for Silicon's
default, so joining removes most of what branching costs Silicon without removing
all of it, and Helium is the configuration that degrades least. A constant
separates the two verifiers otherwise: Helium leads Silicon's better
configuration by
#attr-branch-morejoins-ratio-hi at #attr-branch-depths conditionals, and that
factor is the per-obligation cost of translating a goal into an SMT query and
reading the answer back, which the e-graph does not pay.

The give-back reverses that result. Helium goes from #attr-branch-perm-lo at one
conditional to #attr-branch-perm-hi at #attr-branch-perm-helium-depth, where
Silicon takes #attr-branch-perm-silicon-at-helium-hi, and Silicon reaches only
#attr-branch-perm-silicon-hi at #attr-branch-depths. A lead of
#attr-branch-perm-ratio-lo at one conditional becomes a deficit of
#attr-branch-perm-ratio-hi at #attr-branch-perm-helium-depth, and the two
verifiers cross at #attr-branch-crossover conditionals. The time is spent on the
e-graph, which grows from #attr-branch-perm-nodes-lo to
#attr-branch-perm-nodes-hi e-nodes, a factor of #attr-branch-perm-nodes-growth
per conditional against the branch-only family's fixed increment of
#attr-branch-pure-nodes-step. Each conditional
contributes a chunk whose address equals the previous one under that
conditional's guard alone, so the partition the release traverses grows with the
family and every term reasoning about it carries one more guard. The guards
differ from one conditional to the next, so the terms mentioning them differ too,
and the family shares none of them.

Silicon barely distinguishes the two families, which is the other half of the
result. Permission moving across a branch is ordinary work for a symbolic
execution engine, because each path is explored with its own guard assumed and the
reborrow's identity with its original is an ordinary fact there. The two
families consequently separate branching from the permissions crossing it, and they
confirm over a generated family what the attribution above reaches over a corpus:
a branch Helium can merge costs it a constant, and a branch across which
permission moves costs it a state that grows with the branching. Read together
with the #raw("--moreJoins") curve, the two families bound the contribution of the
representation more tightly than the corpus does. Helium's advantage on
branch-heavy code is a constant factor per obligation rather than a better
asymptote, and it is confined to the branches across which no permission travels.
@sec:future-work develops the design that would lift the second restriction, a
fork of the verification state at a branch, in which an arm's guard is assumed
outright and the reborrow's identity with its original becomes the same ordinary
fact it is for Silicon.


// ── Superseded draft, kept for reference ──────────────────────────────
// #import "../../macros.typ": *
// #import "../../generated/attribution-scalars.typ": *
// #import "../../generated/attribution-permtree-scalars.typ": *
// #import "../../generated/perf-rust-scalars.typ": *
//
// == Discussion <sec:results-attribution>
// The tables of @sec:results-perf give a ratio per file. This section explains
// them. A ranking of ratios on its own says little, because a file Silicon happens
// to find hard flatters Helium and a file it finds easy does not, so we read each
// ratio against what the file's shape predicts and treat the residuals as the
// interesting cases.
//
// Three measurements support the explanation, and all three come from counters
// Helium records for itself. Those counters are deterministic, which is what makes
// a claim in their terms stronger than a claim in milliseconds.
//
// === How the prover ladder divides the work <sec:results-tiers>
// Helium discharges an obligation by trying the tiers of @sec:impl-execution in
// order and stopping at the first that succeeds. The design rests on the expensive
// tier being rare, and this is the measurement of how rare it is.
//
// The verifier credits exactly one tier per proof query, so the counts below sum
// to the queries the run raised and a share of the ladder is a share of those
// queries. Not every query is a proof obligation. The heap machinery asks the same
// ladder whether a demand is provably zero, or whether two addresses coincide, and
// reads a declined answer as a fact about the heap that sends the operation to its
// next fallback. Those declines are what the last row of each table counts.
//
// #include "../../generated/attribution-tiers-rust.typ"
//
// Over the Prusti corpus of @sec:results-perf-rust a lookup carries the corpus:
// #vm[`goal_true`] alone closes #attr-rust-goal-share of the queries, rebuilding
// the e-graph and finding the goal already merged with #vm[`true`] without a
// single rewrite firing. #vm[`inconsistent`] fires #attr-rust-dead-block times, and every one of them is
// a block whose own path condition is unsatisfiable rather than an e-graph that
// has turned contradictory. That is the dead arm of @sec:impl-cfg, which a
// #ru[`match`] produces in quantity, and its absence in the other direction is the
// non-vacuity gate of @sec:results-perf holding. #vm[`implication_true`] builds the weakened goal and finds its class already
// merged with #vm[`true`], either because an earlier identical obligation recorded
// it there or because a rewrite settled the shape before anything asked. It fires
// #attr-rust-implication-true times, so on this corpus the weakening earns almost
// nothing that the tier above it had not already closed. #vm[`saturate`],
// the first tier that runs a rewrite search, accounts for under half a percent.
//
// That leaves #vm[`implication_decompose`] at #attr-rust-decompose-share. It is
// the only tier that reads a graph with the path condition assumed, and therefore
// the only one that pays for a copy. What it copies is usually not the ground
// graph: inside a method body the assumption is made once per basic block, into
// the scratch graph of @sec:impl-cfg, and every later obligation of that block
// reads the copy that already exists. The corpus builds
// #attr-rust-block-scratch-clones scratches in all, against
// #attr-rust-probe-clone obligations that clone the ground graph for themselves,
// which are the ones raised in a function or a resource, where there are no blocks
// to amortise the assumption over. Of the obligations this tier closes,
// #attr-rust-ite-decompose reach its last rung, the goal decomposition that
// telescopes one guard at a time.
//
// The hand-written corpus of @sec:results-perf-viper divides the same way at a
// smaller scale, with #vm[`goal_true`] at #attr-viper-goal-share and
// #vm[`implication_decompose`] at #attr-viper-decompose-share.
//
// #include "../../generated/attribution-tiers-viper-perf.typ"
//
// A file of that corpus finishes in tens of milliseconds, so its shares confirm
// the shape rather than measure it, and the process-overhead caveat of
// @sec:results-perf-viper applies to any time read off it.
//
// === What the rewrite rules cost <sec:results-rules>
// A rewrite rule's cost on its own says little: an expensive rule that nothing
// would notice missing is a deletion candidate, and a cheap rule holding up half
// the corpus is not. Both numbers come from the same experiment, an ablation that
// drops one rule and measures what changes.
//
// Over the rust corpus, two rules dominate the time spent inside `saturate`:
// `distinguishing-observation` (#attr-rule-distinguishing_observation-ms) and
// `ite-reduce` (#attr-rule-ite_reduce-ms), an order of magnitude ahead of every
// other rule Helium applies. `distinguishing-observation` is the contrapositive of
// congruence: if a function's results in two e-classes carry distinguishable
// fingerprints, the arguments cannot be equal, which is how Helium tells apart
// the retraction of an enum snapshot without needing a free-constructor axiom for
// it. `ite-reduce` folds a conditional whose guard the e-graph has already
// decided down to its live branch, which is what lets a branch merged back
// together stop carrying the branch that can no longer be taken.
//
// Dropping either confirms it is load-bearing, and the two failures look
// nothing alike. Ablating `distinguishing-observation` drops the corpus's wall
// time by #attr-ablate-distinguishing_observation-change
// (#attr-ablate-distinguishing_observation-with to
// #attr-ablate-distinguishing_observation-without) but costs exactly
// #raw("shape_area")'s two #ru[`&mut`]-through-#ru[`match`] methods,
// #raw("m_shape_grow") and #raw("m_shape_translate"), the two methods whose join
// reconciles a given-out and a given-back permission chunk by telling their
// snapshots apart. @sec:results-giveback derives that pattern and measures it.
// Every other member in the corpus verifies without it — the rule earns its cost
// entirely on one file's pattern. Ablating `ite-reduce` is not a matter of cost at
// all: wall time rises by #attr-ablate-ite_reduce-change
// (#attr-ablate-ite_reduce-with to #attr-ablate-ite_reduce-without), and ten of
// the eleven files time out outright rather than finish slower; the eleventh,
// #raw("borrow_fields"), instead loses seven members to insufficient permission.
// Without a live conditional collapsing once its guard is settled, the branches
// Helium clones at every join keep growing rather than folding back down, and the
// corpus stops being tractable rather than merely slower.
//
// A third rule, the built-in projection for `Option`'s payload accessor
// (`proj-18446744073709551612`, #attr-rule-proj_18446744073709551612-ms of search
// and apply time, close behind the two above), is the deletion candidate the
// other two are not: ablating it changes wall time by
// #attr-ablate-proj_18446744073709551612-change, inside the noise band of
// @sec:results-setup, and costs nothing — every member that verified with the
// rule still verifies without it. Every `&mut` reborrow Prusti's encoder emits
// goes through this accessor, which is why it ranks third by raw cost despite
// being redundant: whatever it proves, some other rule proves as well.
//
// === The #ru[`&mut`] give-back at a join <sec:results-giveback>
// @sec:results-rules leaves one rule paying for one pattern on one file. This
// subsection is that pattern. A Rust method that mutates through a #ru[`&mut`]
// inside a #ru[`match`] lends a location out on each arm and takes it back before
// the arm ends, and Prusti encodes the lending and the taking back as ordinary
// permission transfers guarded by the arm's condition. @lst:giveback-lost writes
// that shape directly in Viper, with the transfers spelled out rather than hidden
// in a call.
//
// #viper(
//   caption: [A location released and reacquired inside an arm. The arm
//     re-establishes the value it carried, and the read after the join fails.],
//   label: "lst:giveback-lost",
// )[```viper
// method lost(r: Ref, b: Bool)
// {
//   inhale acc(r.val)
//   r.val := 11
//   if (b) {
//     exhale acc(r.val)
//     inhale acc(r.val)
//     inhale r.val == 11
//   }
//   assert r.val == 11    // fails
// }
// ```]
//
// Nothing in @lst:giveback-lost changes the value. The arm gives the location up
// and takes it back carrying the same number, and the arm that is not taken never
// touches it, so #vi[`r.val`] is #vi[`11`] on both paths. Helium rejects the
// assertion anyway. Weakening it to #vi[`b ==> r.val == 11`] makes the same
// program verify, which places the loss at the join rather than inside the arm.
//
// The reason is the rule @sec:impl-cfg states for facts and states again for
// chunks: a fact established under a block's cube reaches the join as an
// implication of that cube. Helium never merges a derived fact with #vm[`true`]
// outright while a guard is in force. It merges the guarded implication instead,
// because a bare merge would assert the fact on every path and let the verifier
// assume what it has to prove. The arm's #vi[`inhale`] therefore publishes
// #vm[`b ==> r.val == 11`], the join receives that implication, and the
// unguarded read has no unguarded fact to read.
//
// @lst:giveback-lost loses a value. The encoding Prusti emits loses something
// more expensive, because the give-back does not name the location the method
// started with. A reborrow is a
// fresh reference whose pointee is equated to the original's by a postcondition,
// and that postcondition is released under the arm's guard like every other fact.
// @lst:giveback-reborrow adds the reborrow and drops the value.
//
// #viper(
//   caption: [The reborrow. #vi[`q`] is the same reference as #vi[`r`], but only
//     where #vi[`b`] holds, so the permission comes back at an address the ground
//     e-graph cannot see is the one the release names.],
//   label: "lst:giveback-reborrow",
// )[```viper
// method reborrow(r: Ref) returns (q: Ref)
//   ensures q == r
//
// method one_arm(r: Ref, b: Bool)
// {
//   inhale acc(r.val)
//   if (b) {
//     var q: Ref
//     q := reborrow(r)
//     exhale acc(r.val)
//     inhale acc(q.val)
//   }
//   exhale acc(r.val)
// }
// ```]
//
// A heap partition indexes its chunks by the e-class its location resolves to, and
// #vi[`q == r`] holds only under #vi[`b`], so #vm[`val(q)`] and #vm[`val(r)`]
// resolve to two classes. The partition holds two chunks where the program holds
// one location. The join does not repair this. It groups the arms' chunks by their
// canonical addresses and leaves two addresses it cannot see are equal as two
// entries, each carrying the guard of the arm that produced it.
//
// Merging them there would be unsound, and in the direction that matters. The
// location axioms of @sec:impl-heap-repr state that two chunks of one partition
// sum to no more than the bound, so a merge that ignored the guards would read two
// complementary one-sided #vm[`1/1`] chunks as one location holding #vm[`2/1`] and
// derive a contradiction, or, taken the other way, would prove two references
// distinct that a single path never holds at once. The guards are what keep the
// axiom honest, so the join keeps them.
//
// Reconciling the two chunks is left to the release, and the release resolves it
// by descending a ladder much like the prover's. The address lookup misses. The demand is not
// provably zero. A full saturation does not close the gap either, because the
// equation that would close it is guarded. Only then does the consume fall back to
// recovering the permission from the partition rather than from a chunk, and it
// has two ways to do so. Both walk every chunk of the group, and they differ in
// what they do with each one.
//
// The first decides. It collects every held chunk whose address coincides with the
// demanded one under the path condition, reading that off the block scratch when
// the instruction's path condition is the block's own cube and otherwise cloning
// the graph and saturating the clone. The second defers. Rather than decide
// coincidence it gates each chunk's contribution by an equality between that
// chunk's address and the demanded one, and hands the whole sum to the engine:
//
// #align(center)[#vm[`perm(l) = Σ_c ite(c.addr == l, guard(c) ? c.perm : 0, 0)`]]
//
// The two divide the work by where the aliasing comes from. The first assumes the
// instruction's path condition, so it can only find an equality that condition
// implies, and it declines at once when the instruction carries no path condition
// at all. The second assumes nothing and leaves the address equality in the term,
// which is what an equality holding outright needs.
//
// Every give-back in the Prusti corpus is settled by the first. Over
// #attr-giveback-consumes-total consumes that reach the fallback, the summing rung
// runs #attr-giveback-sigma-scans times, because a reborrow's identity with its
// original is exactly an equality the arm's guard implies. The summing rung
// carries the other case, which is what a Viper author writes rather than what
// Prusti emits: withdrawing it costs six of Helium's own regression cases, every
// one of them aliasing two names unconditionally, and the hand-written corpus case
// of @sec:appendix-benchmarks-viper. Withdrawing it costs the Prusti corpus
// nothing. So what this subsection measures is the per-chunk decision under the
// guard rather than the arithmetic beneath it.
//
// Sufficiency is proven per leaf of whichever sum results, each leaf under its own
// guard.
// Proving it as one goal instead does not work, because the arms' contributions
// are live under complementary guards, so no single unguarded goal holds while
// each leaf is trivial. The debit is distributed across the set and gated the same
// way, so nothing is taken on a path where the addresses are unrelated and the
// ground graph still never merges them.
//
// Every gate in that sum is an equality between addresses, and most of them are
// false. Settling them is what `distinguishing-observation` of @sec:results-rules
// does: it is the contrapositive of congruence at an application, so a unary
// function whose results at two classes carry different fingerprints refutes the
// equality of its arguments. Helium needs it because Prusti encodes a primitive
// snapshot as a domain with a retraction rather than as a datatype, so two
// snapshots carry no free-constructor distinctness and only an observation
// separates them. Its failed scans are the hot path, which is why ablating it
// costs exactly the two methods this subsection is about.
//
// Helium reports, per member, the time it spends inside that fallback. Over the
// Prusti corpus, #attr-giveback-files files of #attr-giveback-files-total reach it
// at all. Four of them spend measurable time
// there, and those four are #attr-giveback-0-case, #attr-giveback-1-case,
// #attr-giveback-2-case and #attr-giveback-3-case: the same four files, in the
// same order, that @sec:results-outliers finds furthest below their predicted
// ratio. The fifth is #attr-giveback-4-case, which reaches the fallback
// #attr-giveback-4-consumes times and spends #attr-giveback-4-secs there, and it
// is the corpus's fastest file against Silicon, so reaching the fallback at all is
// not what costs a file its ratio. Reaching it often is. In #attr-giveback-0-case
// the fallback is reached by #attr-giveback-0-members members over
// #attr-giveback-0-consumes consumes, and #raw("m_shape_grow") spends
// #attr-giveback-m-shape-grow-secs there, #attr-giveback-m-shape-grow-share of its
// own verification time.
//
// That last figure is the one to read carefully. The fallback marks the members
// that pay, but it does not by itself contain the cost. The other nine tenths of
// those members go on the permission proofs that succeed without it and on the
// saturation the guarded equalities provoke, which is where
// `distinguishing-observation` and `ite-reduce` spend what @sec:results-rules
// measures. The measurement below prices that larger population, and the tenth
// counted here sits inside it. Splitting #attr-giveback-0-case by member makes the
// same point from the other side. Its two #ru[`&mut`]-through-#ru[`match`] methods
// account for #attr-split-named-share of Helium's time on the file, and Helium
// leads Silicon on them by #attr-split-named-ratio. On the rest of the same file
// it leads by #attr-split-rest-ratio. Both are far below the corpus geometric mean
// of #rust-ratio-geo, so the give-back is where the advantage is thinnest without
// being the whole of why this file is hard: Silicon spends
// #attr-split-named-share-silicon of its own time on the same two methods, so they
// are expensive for both verifiers.
//
// A second measurement prices the reasoning rather than the search. A conditional
// footprint gives a location an amount that is a tree of guards with fractions at
// the leaves, and Helium proves a permission goal by descending that tree and
// discharging each leaf under the guards that reach it. Assuming every such walk
// away, which is unsound and done here only to price it, splits the corpus in two.
//
// #include "../../generated/attribution-permtree.typ"
//
// The descent costs #attr-permtree-branchy-lo to #attr-permtree-branchy-hi on the
// #attr-permtree-branchy-files files whose permissions are branch-structured, and
// at most #attr-permtree-other-hi on the #attr-permtree-other-files that are not,
// with nothing in between. It is the same population again: the files that pay for
// the descent are the files that reach the give-back fallback, which is what one
// should expect, since a permission lent away under a guard is what builds the
// tree in the first place.
//
// The measurement also bounds the explanation. With every permission proof free
// #attr-giveback-0-case still takes #attr-permtree-worst-assumed against
// #attr-permtree-worst-walked, a cut of #attr-permtree-worst-cut, and it builds an
// e-graph of the same size either way. Discharging the permissions is a third of
// what this file costs. The remainder is carrying a state that encodes every arm
// of the #ru[`match`] at once, which is the trade @sec:impl-cfg makes deliberately
// and @sec:future-work proposes to revisit.
//
// Every step above follows from one decision. Helium keeps a single e-graph for
// all the arms, so an arm's guard can never be assumed outright, so the equation
// that identifies the reborrow with its original is only ever available guarded,
// so the addresses diverge and the release has to search. A verifier that forks
// its state at a branch assumes the guard unconditionally in the fork. There, #vi[`q == r`] is an
// ordinary fact, #vm[`val(q)`] and #vm[`val(r)`] are one class, and the chunk
// given back consolidates with the chunk it came from when it is added. The
// release finds it at the first rung, and none of the ladder below runs. The two
// locations never diverge, because the divergence is an artifact of holding one
// graph for every arm rather than a property of the program.
// @sec:future-work develops that model, and this subsection is the measurement
// that motivates it.
//
// === Attribution <sec:results-outliers>
// Fitting the per-file ratio against Silicon's own time gives a baseline in which
// the ratio grows as Silicon's own time to the power #attr-ratio-slope. The model
// is deliberately crude, capturing only that Silicon slows down as a file grows
// and nothing about what the file contains. The residuals against that
// baseline, not the raw ratios, are what separates a file whose shape merely
// predicts a strong result from one whose shape does not.
//
// #attr-worst-0-case does worst against its own prediction: a
// #attr-worst-0-ratio speedup where its size alone would predict
// #attr-worst-0-expected. @sec:results-giveback attributes that gap to its two
// #ru[`&mut`]-through-#ru[`match`] methods and measures what they pay for.
// #attr-worst-1-case falls short the same way at a smaller scale
// (#attr-worst-1-ratio against #attr-worst-1-expected), and
// #attr-worst-2-case and #attr-worst-3-case round out the shortfall. All four are the four files that spend measurable time in the give-back
// fallback of @sec:results-giveback, in that order, which is the sharpest single
// predictor of a poor residual this evaluation found. Reaching the #vm[`implication_decompose`] tier is not that predictor:
// #attr-worst-3-case reaches it on the largest share of any file in the corpus and
// still lands closer to its prediction than #attr-worst-0-case does.
//
// At the other end, #attr-best-0-case (#attr-best-0-ratio against
// #attr-best-0-expected), #attr-best-1-case, #attr-best-2-case and
// #attr-best-3-case all share the shape @sec:results-perf-rust calls out for
// straight-line code. None of them lends a location across a branch, so none
// reaches the give-back fallback, and Silicon's cost on them grows with a block
// count that never translates into work for Helium's e-graph. The residual is
// largest exactly where the pattern Helium is built around, accumulating facts
// once and reusing them everywhere, has nothing standing in its way.
//
// Read together, the four measurements tell one story. The ladder's cheap tiers
// carry the corpus, so what cost remains concentrates in `saturate`, which two
// rules dominate. One of those two is what the worst residuals are paying for, and
// they pay for it because a permission lent across a branch and taken back on the
// far side is exactly the reconciliation that rule exists to decide. Nothing in
// the current rule set decides that reconciliation directly. It is reached by an
// indirect route through fingerprints, one union at a time, and the route is taken
// only because the guard that would settle it in one step cannot be assumed while
// one e-graph serves every arm. @sec:results-giveback traces that chain, and
// @sec:future-work develops the two designs that break it: a fork of the state at
// a branch, and a rule that reads the join's guard directly.
