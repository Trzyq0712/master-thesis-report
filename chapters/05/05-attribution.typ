#import "../../macros.typ": *

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

#todo[
  *The tier table:* obligations closed by each rung, and each rung's share, over
  the Prusti corpus and over the hand-written corpus separately. Generated into
  #raw("report-tables/tiers-*.typ"); a generator for the Prusti corpus already
  exists.

  The prose must say three things beyond the table. Which rung carries the corpus,
  and by how far. Which rungs essentially never fire, and what they are for —
  a rung that fires five times in a corpus of hundreds of thousands of obligations
  is worth a sentence, not a table row on its own. And the share reaching the rung
  that clones the e-graph, since that rung is the only one whose cost is not
  bounded by the size of the goal, and the whole design rests on its population
  being thin.

  Current belief, to be re-confirmed: the cheapest rung takes over 98% and the
  cloning rung under a quarter of a percent.
]

=== What the rewrite rules cost <sec:results-rules>
#todo[
  *Per-rule cost, with a paired ablation.* Two numbers per rule, and neither is
  useful alone: what the rule costs in search and application time, and what is
  lost when it is dropped. A rule that is expensive and load-bearing is a
  different finding from a rule that is expensive and dead.

  The known case is the equality-refutation rule of @sec:impl-adts. It was most
  of a grid file's wall clock, and almost all of that was its failed scans rather
  than its successful ones. Dropping it cost members, so it is load-bearing, and
  memoizing the failed scan is what the file needed. Report the rule's cost before
  and after, and be explicit that the memoization bought a constant factor and did
  not change the growth rate.
]

=== Attribution <sec:results-outliers>
#todo[
  *The residual analysis.* Fit the per-file ratio against Silicon's own time —
  a deliberately crude model, capturing only that Silicon struggles more as a
  file grows — and take the outliers in both directions. Attribute each from the
  counters already in the sweep: obligations, the share that reached the cloning
  rung, the e-graph peak, and the rewrite rules that took the most time.
]

#todo[
  *The synthesis paragraph, which is what a reader takes away.* The shapes below
  are what the last sweep supports; each is to be re-confirmed on the clean sweep
  and then written as prose, not as a list.

  - *Straight-line blocks.* The largest wins, and they grow with the program:
    Silicon's cost rises with the number of blocks and Helium's stays close to
    linear in instructions. Several of these files cap Silicon and verify in
    seconds here. The counters agree — under one rewrite-rule application per
    obligation, no cloning, no scratch state.
  - *Call density and borrows through calls.* A solid win. The cloning rung never
    fires.
  - *Option and result paths, and state machines.* A smaller but real win. One of
    these files carries the corpus's heaviest cloning share and still wins, which
    is worth saying: the cloning rung being reached is not by itself the problem.
  - *Enum payloads.* The weakest win in the corpus, and the file that explains
    the loss. The counters separate it from everything else by an order of
    magnitude in rewrite-rule applications per obligation, and by the number of
    times the block scratch is cloned.
  - *High variant counts.* An outright loss, and it must be written as one. The
    gate split telescopes over the snapshot tower the discriminant builds, so its
    cost grows exponentially in variant count while payload depth costs only
    linearly. Silicon is nearly flat on both axes. Past a certain variant count
    Helium is slower, and past a higher one it fails outright.

  Close with what would fix the loss, stated as a mechanism rather than as future
  work in general: nothing in the current rule set decides the gate directly, so
  anything that does collapses the telescope to a lookup. @sec:future-work is where
  that is developed.
]
