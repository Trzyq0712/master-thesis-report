#import "../../macros.typ": *
#import "../../generated/attribution-scalars.typ": *
#import "../../generated/perf-rust-scalars.typ": *

== Where Helium Wins and Where It Struggles <sec:results-attribution>
The tables of @sec:results-perf give a ratio per file. This section explains
them. A ranking of ratios on its own says little, because a file Silicon happens
to find hard flatters Helium and a file it finds easy does not, so we read each
ratio against what the file's shape predicts and treat the residuals as the
interesting cases.

Three measurements support the explanation, and all three come from counters
Helium records for itself. Those counters are deterministic, which is what makes
a claim in their terms stronger than a claim in milliseconds.

=== How the prover ladder divides the work <sec:results-tiers>
Helium discharges an obligation by trying a sequence of increasingly expensive
strategies and stopping at the first that succeeds. The design rests on the
expensive strategies being rare, and this is the measurement of how rare they
are.

#include "../../generated/attribution-tiers-rust.typ"

Over the Prusti corpus of @sec:results-perf-rust, a lookup carries the corpus:
`goal_true` alone closes #attr-rust-goal-share of the #rust-members members'
obligations, rebuilding the e-graph and finding the goal already merged with
#vm[`true`] without a single rewrite firing. `inconsistent` and `dead_block`,
the two tiers that close an obligation vacuously, never fire at all, which is
the non-vacuity gate of @sec:results-perf holding rather than a property of the
corpus. `memo` and `ite_decompose` fire only a few dozen times each over the
whole corpus, closing the remainder of what a lookup or a rewrite would
otherwise have to prove by search. `saturate`, the first tier that actually
runs a rewrite search, accounts for under half a percent.

That leaves `probe`, the only tier that clones the e-graph rather than reading
or rewriting the one already there, at #attr-rust-probe-share of the corpus.
The design of @sec:impl-execution rests on that population staying thin, and it
does: three files out of eleven never reach it, and the file that reaches it
most, #raw("state_machine"), still does so for only 2.03% of its obligations. A
clone is not free — @sec:impl-cfg puts one clone per basic block behind it
rather than one per obligation — but at this share it never dominates a file's
time on its own; @sec:results-rules and @sec:results-outliers are where a
file's time actually goes.

The hand-written corpus of @sec:results-perf-viper shows the same shape at a
smaller scale: `goal_true` accounts for #attr-viper-goal-share of its
obligations and `probe` for #attr-viper-probe-share, both directionally the same
as the Prusti corpus and consistent with the process-overhead caveat already
raised in @sec:results-perf-viper — a corpus whose files finish in tens of
milliseconds has too few obligations for its tier shares to add anything beyond
confirming the same story.

=== What the rewrite rules cost <sec:results-rules>
A rewrite rule's cost on its own says little: an expensive rule that nothing
would notice missing is a deletion candidate, and a cheap rule holding up half
the corpus is not. Both numbers come from the same experiment, an ablation that
drops one rule and measures what changes.

Over the rust corpus, two rules dominate the time spent inside `saturate`:
`distinguishing-observation` (#attr-rule-distinguishing_observation-ms) and
`ite-reduce` (#attr-rule-ite_reduce-ms), an order of magnitude ahead of every
other rule Helium applies. `distinguishing-observation` is the contrapositive of
congruence: if a function's results in two e-classes carry distinguishable
fingerprints, the arguments cannot be equal, which is how Helium tells apart
the retraction of an enum snapshot without needing a free-constructor axiom for
it. `ite-reduce` folds a conditional whose guard the e-graph has already
decided down to its live branch, which is what lets a branch merged back
together stop carrying the branch that can no longer be taken.

Dropping either confirms it is load-bearing, and the two failures look
nothing alike. Ablating `distinguishing-observation` drops the corpus's wall
time by #attr-ablate-distinguishing_observation-change
(#attr-ablate-distinguishing_observation-with to
#attr-ablate-distinguishing_observation-without) but costs exactly
#raw("shape_area")'s two #ru[`&mut`]-through-#ru[`match`] methods,
#raw("m_shape_grow") and #raw("m_shape_translate"): the two methods whose join
reconciles a given-out and a given-back permission chunk by telling their
snapshots apart, described in @sec:results-perf-rust's performance analysis.
Every other member in the corpus verifies without it — the rule earns its cost
entirely on one file's pattern. Ablating `ite-reduce` is not a matter of cost at
all: wall time rises by #attr-ablate-ite_reduce-change
(#attr-ablate-ite_reduce-with to #attr-ablate-ite_reduce-without), and ten of
the eleven files time out outright rather than finish slower; the eleventh,
#raw("borrow_fields"), instead loses seven members to insufficient permission.
Without a live conditional collapsing once its guard is settled, the branches
Helium clones at every join keep growing rather than folding back down, and the
corpus stops being tractable rather than merely slower.

A third rule, the built-in projection for `Option`'s payload accessor
(`proj-18446744073709551612`, #attr-rule-proj_18446744073709551612-ms of search
and apply time, close behind the two above), is the deletion candidate the
other two are not: ablating it changes wall time by
#attr-ablate-proj_18446744073709551612-change, inside the noise band of
@sec:results-setup, and costs nothing — every member that verified with the
rule still verifies without it. Every `&mut` reborrow Prusti's encoder emits
goes through this accessor, which is why it ranks third by raw cost despite
being redundant: whatever it proves, some other rule proves as well.

=== Attribution <sec:results-outliers>
Fitting the per-file ratio against Silicon's own time gives a baseline in which
the ratio grows as Silicon's own time to the power #attr-ratio-slope — a
deliberately crude model that captures only that Silicon slows down as a file
grows, nothing about what the file contains. The residuals against that
baseline, not the raw ratios, are what separates a file whose shape merely
predicts a strong result from one whose shape does not.

#attr-worst-0-case does worst against its own prediction: a
#attr-worst-0-ratio speedup where its size alone would predict
#attr-worst-0-expected. @sec:results-perf-rust already attributes the gap to
its two #ru[`&mut`]-through-#ru[`match`] methods, and @sec:results-rules now
supplies the mechanism: those two methods are the entire reason
`distinguishing-observation` costs anything on this corpus. #attr-worst-1-case
falls short the same way at a smaller scale (#attr-worst-1-ratio against
#attr-worst-1-expected) without ever reaching the `probe` tier at all — its
cost comes from the same equality and projection reasoning running on a heavier
mutation pattern, not from cloning. #attr-worst-2-case and #attr-worst-3-case
round out the shortfall; #attr-worst-3-case reaches `probe` on 2.03% of its
obligations, the highest share in the corpus, and still lands short of its
prediction, which is the point already made in @sec:results-tiers: reaching the
cloning tier is not by itself what costs time.

At the other end, #attr-best-0-case (#attr-best-0-ratio against
#attr-best-0-expected), #attr-best-1-case, #attr-best-2-case and
#attr-best-3-case all share the shape @sec:results-perf-rust calls out for
straight-line code: none of them reaches `probe`, and Silicon's cost on them
grows with a block count that never translates into work for Helium's
e-graph. The residual is largest exactly where the pattern Helium is built
around — accumulate facts once, reuse them everywhere — has nothing standing in
its way.

Read together, the three measurements tell a consistent story. The prover
ladder's cheap tiers carry the corpus, so the corpus's cost concentrates in
`saturate`, which two rules dominate. One of those two,
`distinguishing-observation`, is what the worst residual is paying for, and it
pays for it because the pattern that method exhibits — permission given out
across a branch and reconciled at the join — is exactly the pattern that rule
exists to decide. Nothing in the current rule set decides that reconciliation
directly; `distinguishing-observation` proves it by an indirect route through
fingerprints, one union at a time. A rule that read the join's guard and
committed to the reconciliation in one step, rather than discovering it by a
failed-then-successful disequality scan, would collapse the cost this section
attributes without changing what gets proven. @sec:future-work develops that
mechanism.
