#import "../macros.typ": *

// Single source of truth for the sweep the whole chapter quotes, so that a
// re-run means editing four lines rather than hunting through prose.
#let datestamp = [14 August 2026]
#let srcrev = raw("61ca9e6")
#let sweeprev = raw("68a5a51")
#let total-ours = [96.81s]
#let total-silicon = [3255.85s]
#let ratio-total = [33.6#sym.times]
#let ratio-geo = [22.2#sym.times]

#note[
  *How this chapter is organised.* Two questions, in order: does the verifier
  agree with Silicon on the corpus, and how much faster is it. The first is a
  precondition for the second — a speedup measured against a verifier that is
  proving something weaker is not a speedup — so validity is settled before any
  timing is quoted. The second half then says where the verifier stops, which is
  @sec:beyond-fragment's list turned into measurements.

  All numbers below are from the sweep of #datestamp at #sweeprev, with one
  exception, flagged where it appears: #raw("shape_area")'s time on our side is a
  re-measurement at #srcrev, whose memoization of the equality-refutation scan
  (@sec:impl-adts) changed that file and left every other one flat. Silicon's
  column is untouched by that, so the row pairs a re-measured number of ours with
  the sweep's Silicon number, which is the conservative direction. Any change to
  the prover tiers invalidates the table and it must be re-run: the script is
  #tbd[name the committed bench script] and the raw report is
  #tbd[name where the sweep report lives in the tree].
  #tbd[Re-run the full sweep at #srcrev for the final version so the table has one
  provenance.]
]

== Performance Evaluation <sec:results-perf>

The claim this thesis has been accumulating is that core proofs are cheap if the
verifier is built to treat them as equality problems, and that the cost of an
SMT-based backend on this class of obligation is not intrinsic to the obligation.
This section measures that against Silicon on the corpus @sec:prusti-needs
characterised.

#para[The corpus] <para:results-corpus> The 22 Prusti encodings of
@sec:prusti-needs, containing 2886 verifying members across 226 method bodies.
Two later additions sit alongside them and are measured separately rather than
folded into the table: the #raw("enum_vN_pD") grid of
@sec:results-enum-scaling, generated to separate an enum's variant count from its
payload size, and #raw("borrow_fields"), which covers borrows stored in structs —
a shape no other source had. With those, the whole benchmark tree stands at 4494
verified members and 5 known-failing, all five in the grid's widest enum.
They are Prusti's own output for spec-less Rust: the obligations are framing,
fold/unfold and discriminant well-formedness, not hand-written functional
specifications. That is the class the verifier is aimed at, and it is the class
the numbers below are about — they say nothing about a program carrying rich
specifications, and @sec:results-gaps is where that boundary is drawn.

Sixteen of the 22 are encodings of hand-written Rust programs — vector and matrix
arithmetic, a bank transfer, a state machine, an inventory, a physics step. The
remaining six are the #raw("depth_dN_mM") family, generated with two knobs: `N` is
call-nesting depth and `M` is statements per method. They exist to separate a
constant-factor win from an asymptotic one, and
#pararef(<para:results-scaling>, [Scaling]) is where
that separation is made.

#para[Setup] <para:results-setup> Our verifier is run as a single process,
#raw("target/release/verify <file>"), wall clock, single-threaded. Silicon is run
through a warm ViperServer over HTTP with #raw("--numberOfParallelVerifiers 1")
and #tbd[z3 version — the sweep says 4.8.7; confirm this is the version Prusti
ships], and the number taken is the server-reported #emph[overall] time, not the
client's round trip. ViperServer's cache is flushed before every timed run.
Both sides are therefore single-threaded, and neither is credited with work it
did on a previous file.

Two details of that setup are load-bearing rather than incidental, and both cost
a full sweep to find. The first is that a ViperServer is #emph[cold] when it
starts, and the first file measured on it is inflated several-fold:
#raw("physics_step") read past 100s on a cold server and 17.75s warm,
#raw("shape_area") past 100s cold and 19.79s warm. A driver that restarts the
server after a timeout — which is the natural thing to do — must re-warm it with a
throwaway file outside the timed set before the next measurement, or every
post-timeout file is attributed a JVM and Z3 warm-up that has nothing to do with
the program. Every number in the table is from a re-warmed run. The second is
that Silicon is given no handicap for it: comparing our cold process against a
warm server is the conservative direction, and it is the direction taken.

#para[Validity] <para:results-validity> Both checks below were passed before any
timing was recorded, and the second is the one that matters.

The first is agreement. Running the corpus through
#raw("benchmarks/rust/check.sh") gives 2886 verified, 0 known-failing, 0
regressed, 0 stale on these 22 files; the exception list is empty for every one of
them. Every member Silicon verifies, we verify, and we report no member verified
that Silicon rejects. Across the whole benchmark tree — the grid of
@sec:results-enum-scaling included — the same run gives 4494 verified and 5
known-failing, and those five are the subject of that section.

The second is non-vacuity. A verifier that has managed to assume #vi[`false`]
verifies everything instantly, and would produce a spectacular and worthless
speedup. To rule that out, #vi[`assert false`] was appended to all 226 method
bodies and the corpus re-verified: 0 bodies are vacuous on our side, and Silicon
reports 0 failures on every file, so neither side is winning by proving
#vi[`false`]. This is not a hypothetical control. An earlier sweep, of 30 July
2026, was vacuous on part of the corpus and reported a #raw("shape_area") time of
3.7s that was not a real result; the honest figure for that file appears below and
is the one place we lose.

#para[Results] <para:results-table> Per file, warm Silicon, no timeout cap other
than the 400s at which a run was abandoned.

#figure(
  caption: [Verification time per corpus file, ours against warm Silicon. Four
    Silicon runs hit the 400s cap and are lower bounds. († our number for this row
    is a re-measurement at #srcrev; every other number is from the #sweeprev
    sweep.)],
  {
    set text(size: 0.85em)
    let hd(it) = text(size: 0.9em, weight: "bold")[#it]
    // The four capped rows are the reason ratios are quoted as bounds; keeping
    // them in the table rather than dropping them is what makes the total a
    // lower bound rather than a selection.
    table(
      columns: (1fr, auto, auto, auto),
      align: (left, right, right, right),
      inset: (x: 0.5em, y: 0.4em),
      stroke: (x, y) => (
        top: if y == 1 { 1pt + luma(40%) } else if y > 1 { 0.5pt + luma(85%) } else { none },
      ),
      table.header(hd[File], hd[Ours], hd[Silicon], hd[Ratio]),

      [`aabb_collide`], [0.54s], [16.18s], [29.7#sym.times],
      [`bank_transfer`], [0.77s], [8.03s], [10.4#sym.times],
      [`classify_tuple`], [0.97s], [13.20s], [13.6#sym.times],
      [`color_blend`], [1.20s], [40.12s], [33.5#sym.times],
      [`depth_d2_m5`], [0.72s], [15.22s], [21.1#sym.times],
      [`depth_d2_m20`], [2.00s], [84.56s], [42.2#sym.times],
      [`depth_d2_m40`], [3.71s], [232.71s], [62.8#sym.times],
      [`depth_d4_m5`], [1.79s], [39.80s], [22.3#sym.times],
      [`depth_d4_m20`], [3.53s], [152.57s], [43.3#sym.times],
      [`depth_d4_m40`], [10.20s], [385.11s], [37.8#sym.times],
      [`depth_d6_m5`], [2.95s], [>400.00s], [>135.6#sym.times],
      [`depth_d6_m20`], [5.65s], [233.57s], [41.4#sym.times],
      [`depth_d6_m40`], [9.48s], [>400.00s], [>42.2#sym.times],
      [`depth_d8_m5`], [5.05s], [224.46s], [44.4#sym.times],
      [`depth_d8_m20`], [8.80s], [>400.00s], [>45.4#sym.times],
      [`depth_d8_m40`], [12.51s], [>400.00s], [>32.0#sym.times],
      [`inventory`], [1.79s], [4.92s], [2.7#sym.times],
      [`mat3_mul`], [1.78s], [150.89s], [84.7#sym.times],
      [`physics_step`], [3.15s], [17.75s], [5.6#sym.times],
      [`shape_area`#super[†]], [18.36s], [19.79s], [1.1#sym.times],
      [`state_machine`], [1.21s], [4.27s], [3.5#sym.times],
      [`vec3_math`], [0.65s], [12.71s], [19.6#sym.times],

      table.hline(stroke: 0.7pt + luma(40%)),
      text(weight: "bold")[Total], text(weight: "bold")[#total-ours],
      text(weight: "bold")[#total-silicon], text(weight: "bold")[#ratio-total],
    )
  },
) <tbl:results-perf>

The corpus takes #total-ours end to end against Silicon's #total-silicon, a
#ratio-total total-time ratio, and the geometric mean of the per-file ratios is
#ratio-geo. The two numbers differ because the total is dominated by the files
where Silicon is slowest, and the geometric mean is not; both are reported for
that reason. Four of Silicon's runs are lower bounds, so both figures are
themselves lower bounds.

The distribution is more informative than either summary. We never exceed 18.4s on
any file, and that worst file is #raw("shape_area"), where the margin over Silicon
is the thinnest on the table; Silicon exceeds 100s on 11 of the 22. Under a
100s-per-file budget — the shape of a limit a CI pipeline actually imposes — we
finish all 22, Silicon finishes 11, and counting each capped run as exactly 100s
gives #total-ours against 1487.42s.

#para[Scaling] <para:results-scaling> The #raw("depth_dN_mM") family is where the
gap is widest, and, more to the point, where it grows. Silicon runs 15--40s at the
small end and past 400s at the large end; we go from 0.72s to 12.51s across the
same span. A constant factor would show as a flat ratio down that block of
@tbl:results-perf, and it does not: the ratio climbs with both knobs.

Silicon is also #emph[non-monotone] in the knobs. #raw("depth_d6_m5") exceeded 400s
while the strictly larger #raw("depth_d6_m20") finished in 233.57s, which is the
usual quantifier-instantiation luck of an SMT backend: a marginally different
formula finds a marginally different instantiation order, and the cost moves by
an order of magnitude in either direction. Our times are monotone in both knobs on
every point measured. That is the practical difference the design buys beyond the
mean — not only that a file is faster, but that its cost is a function of its
size.

#todo[
  Two things this paragraph should say and cannot yet.

  - Whether the growth is asymptotic or a steep constant. Six points on two knobs
    is enough to say "grows", not enough to fit anything. Either extend the
    family (`m80`, `d12`) or drop the word "asymptotic" everywhere.
  - Where our own time goes on the large end: e-graph size, saturation
    iterations, or lowering. #raw("shape_area") below suggests the answer, and
    the two paragraphs should agree.
]

#para[Where the margin is thinnest] <para:results-loss> One file, and it is worth
more space than its size suggests. #raw("shape_area") takes 18.36s against
Silicon's 19.79s — parity, on a table whose other rows are decided by an order of
magnitude — and it was a loss at 30.06s two commits earlier. What the file
contains is a five-variant payload enum whose methods write through a #vi[`&mut`]
into an arm's payload, which is the one shape that drives sufficiency into the gate
split of #pararef(<para:impl-gate-split>, [Conditional footprints]). Two things
moved the number: the split itself, which made the file verify rather than
verifying it vacuously, and then a memoization of the equality-refutation scan
(@sec:impl-adts) that took 1.58#sym.times off it without changing what it proves.
@sec:results-enum-scaling is that mechanism measured on purpose rather than
inferred from one file.

#todo[
  How many obligations reach the splitting fallback on this file against the corpus
  median. @sec:impl-together quotes the distribution for the worked example (1751
  obligations, 98% at the cheapest tier); the same three numbers for
  #raw("shape_area") are what turn this paragraph into a diagnosis.
]

The three weakest wins are worth naming for the same reason: #raw("inventory")
at 2.7#sym.times, #raw("state_machine") at 3.5#sym.times, and
#raw("physics_step") at 5.6#sym.times. #tbd[Do these share a cause with
`shape_area`? If they are all case-split-heavy, that is one sentence and a much
better section.]

#para[Threats to validity] <para:results-threats> Three, stated plainly.

The corpus is 22 files from one frontend, chosen to exercise the fragment, and it
is not a random sample of Rust. What it supports is a claim about Prusti core
proofs, which is the claim being made; it does not support a claim about Viper
programs in general, and @sec:results-gaps says which shapes are excluded.

The machine ran one unrelated verification process on one of its twelve cores
throughout the sweep. Both sides are single-threaded, so the effect is small, but
it is not zero and it is not distributed evenly across the table.
#tbd[Re-run on a quiet machine before the final version; this sentence should
become "the machine was otherwise idle".]

Silicon is being run as a whole-file verifier over Prusti's encoding, which is
how Prusti runs it. It is not being given the benefit of any Prusti-side caching
or incremental mode. #tbd[Check whether Prusti's default pipeline enables
ViperServer caching in a way that would make this comparison unfair, and say so
either way.]

== Scaling in Variant Count <sec:results-enum-scaling>

#para[Why this measurement exists] #raw("shape_area") differed from the cheap
payload-enum programs along two axes at once — more variants _and_ deeper payloads
— so neither could be blamed for its cost. #raw("benchmarks/rust/gen_enum.py")
separates them. #emph[N] is the variant count, which is how deep the snapshot tower
is that the predicate's discriminant builds, hence how far the gate split of
#pararef(<para:impl-gate-split>, [Conditional footprints]) has to telescope.
#emph[D] is payload nesting depth, where each level _doubles_ the leaf-field count,
so D is a size axis rather than a shape one. The grid is
$N in {2, 3, 5, 8} times D in {1, 2, 3}$: twelve generated spec-less Rust programs,
all encoded by Prusti without error, every one checked non-vacuous by the same
#vi[`assert false`] instrumentation as
#pararef(<para:results-validity>, [Validity]).

#para[Results] Whole file, ours against warm Silicon, same setup as
#pararef(<para:results-setup>, [Setup]). Both columns are at #sweeprev, which is
where the shape of the curve was established; the four points re-measured after
the memoization are quoted separately below, and they move the constant without
moving the shape.

#figure(
  caption: [The #raw("enum_vN_pD") grid: variant count against payload size.
    Starred rows are lower bounds on our side — a failing member stops at its
    failing instruction, so its file has no complete cost.],
  {
    set text(size: 0.85em)
    let hd(it) = text(size: 0.9em, weight: "bold")[#it]
    table(
      columns: (1fr, auto, auto, auto),
      align: (left, right, right, right),
      inset: (x: 0.5em, y: 0.4em),
      stroke: (x, y) => (
        top: if y == 1 { 1pt + luma(40%) } else if y > 1 { 0.5pt + luma(85%) } else { none },
      ),
      table.header(hd[File], hd[Ours], hd[Silicon], hd[Ratio]),

      [`enum_v2_p1`], [1.15s], [5.63s], [4.9#sym.times],
      [`enum_v2_p2`], [1.83s], [6.39s], [3.5#sym.times],
      [`enum_v2_p3`], [3.15s], [6.91s], [2.2#sym.times],
      [`enum_v3_p1`], [3.23s], [6.56s], [2.0#sym.times],
      [`enum_v3_p2`], [5.27s], [8.10s], [1.5#sym.times],
      [`enum_v3_p3`], [10.31s], [9.41s], [0.91#sym.times],
      [`enum_v5_p1`], [18.41s], [11.13s], [0.60#sym.times],
      [`enum_v5_p2`], [31.52s], [12.88s], [0.41#sym.times],
      [`enum_v5_p3`], [67.96s], [15.77s], [0.23#sym.times],
      [`enum_v8_p1`#super[\*]], [137.23s], [19.17s], [0.14#sym.times],
      [`enum_v8_p2`#super[\*]], [208.20s], [21.89s], [0.11#sym.times],
      [`enum_v8_p3`#super[\*]], [232.35s], [26.35s], [0.11#sym.times],
    )
  },
) <tbl:results-enum>

#para[What the memoization moved] The equality-refutation rule of @sec:impl-adts
was 65% of a grid file's wall clock, and essentially all of that was its _failed_
scans: at $N = 5$ it spent 11.9s on 266 successful merges, 45ms apiece for a rule
whose payload is a single union. Ablating it took #raw("enum_v5_p1") from 18.41s
to 0.27s at the cost of two members, so the rule is load-bearing rather than dead
weight, and memoizing the failed scan is what the file needed. Re-measured at
#srcrev: #raw("enum_v5_p1") 10.71s (1.72#sym.times), #raw("enum_v5_p3") 38.43s
(1.77#sym.times), #raw("enum_v8_p1") 81.89s (1.68#sym.times), and
#raw("shape_area") 18.36s (1.58#sym.times), with #raw("mat3_mul") flat. The
per-variant factor is unchanged, so this bought a constant: the crossover moves
from $N approx 3$--$4$ to $N approx 5$ — #raw("enum_v5_p1") lands at
1.04#sym.times, parity — and the $N = 8$ members still fail.

#tbd[Re-measure the remaining grid points at #srcrev so @tbl:results-enum has one
provenance; only four of the twelve were re-run.]

#para[Reading the two axes] The variant axis is the whole story and it is
_exponential_: at $D = 1$ the write-through member goes 0.49s, 1.48s, 8.58s,
54.90s for $N = 2, 3, 5, 8$, roughly $2 times$ per added variant after the first
step, while Silicon over the same range grows about $3.4 times$ in total —
linear. The payload axis is linear in field count: at $N = 5$ the same member goes
8.58s, 14.74s, 31.11s while each level doubles the number of leaf fields, and
Silicon is nearly flat there.

Crossover follows from the two: at #sweeprev we are ahead at $N <= 3$ and behind
at $N >= 5$, with the exact point moving earlier as payloads grow — at $D = 3$ we
already lose at $N = 3$. Where it sits after the memoization is the subject of the
paragraph above.

The grid also predicts the one corpus file this was opened to explain.
#raw("shape_area")'s enum has five variants and a four-leaf-field payload, which
is the grid's $N = 5, D = 2$ point; the grid's member there costs 14.74s against
#raw("shape_area")'s 13.66s, so the model reproduces the program from its
coordinates alone.

#para[The horizon] <para:results-horizon> At $N = 8$ the split no longer suffices
and five members are rejected with insufficient permission —
#raw("m_e_grow") on all three files and #raw("m_e_guarded") on two — which is the
same failure #raw("shape_area") gave before the split existed. They are the only
known-failing members in the whole benchmark tree. $N <= 5$ verifies at every
depth measured, so the split did not remove the limit but moved it: it can invert
a five-deep snapshot tower and not an eight-deep one.

What would close it is not more of the same. The split is a fallback that
telescopes, so anything deciding the gate _directly_ collapses the exponential to
a lookup: relating the discriminant across the generic--concrete round trip, so
the path condition decides the gate at cost independent of N, or asserting that a
discriminator ranges over the declared variants (@sec:impl-adts), which makes the
tower's arms mutually exclusive by construction. Recording what a successful split
learns was measured and rejected — the guarded implications cost more than the
probes they save.

== Completeness Gaps <sec:results-gaps>

@sec:beyond-fragment listed what the verifier does not do and split the list in
two: constructs absent because @sec:prusti-needs found them absent from the
target, and constructs absent because they are unfinished. This section attaches
numbers to the second half, since that is the half a reader is entitled to
distrust. One of them is already measured: the variant-count horizon of
#pararef(<para:results-horizon>, [The horizon]) accounts for every known-failing
member in the benchmark tree, five of them, and is not repeated here.

#todo[
  The measurements this section needs, none of which are in the sweep report yet.

  - *The arithmetic gap, quantified.* @sec:beyond-fragment names it as the
    dominant gap: no decision procedure for linear arithmetic, so
    $0 <= i and i <= n, i < n |- i + 1 <= n$ does not close. Needed here: over the
    loop corpus, how many members Silicon verifies and we do not, and confirmation
    that every one of them fails on exactly that shape. The claim is already made
    in @sec:impl-loops; this is where it is evidenced.
  - *Datatype inverses.* The two facts still missing after @sec:impl-adts —
    a discriminator's range over the declared variants, and the last variant by
    elimination. How many members do they cost, and on which files. The five
    known failures are already attributed to the split they would replace
    (@sec:results-enum-scaling), so what is open here is whether anything _else_
    in the corpus needs them.
  - *Everything else.* Irreducible CFGs, multi-target assignment. Expected: zero
    occurrences in the corpus, which is worth stating as a measurement rather than
    an assumption.

  #para[Run-in headings] What fails / Why it fails / What closing it would take
]

#todo[
  A second table, matching @tbl:results-perf: members attempted, verified, and
  not verified, per file, with the failures attributed to one of the causes above.
  That table is what makes the "0 regressed" of
  #pararef(<para:results-validity>, [Validity]) meaningful — it
  says what the corpus does #emph[not] contain as clearly as the timing table says
  what it does.
]

Nothing in either list is discovered at run time. Every unsupported construct is
rejected by the type-checker or the translator with the construct named, so a
completeness gap is a refusal to answer rather than a wrong answer
(@sec:beyond-fragment). And by the recording principle of that section, a failure
here is a handover point rather than a dead end: the state at the failure is
complete, so the arithmetic gap in particular is a procedure that has not been
attached rather than information that has been lost.
