#import "../../macros.typ": *
#import "../../generated/perf-validity.typ": *
#import "../../generated/perf-rust-scalars.typ": *
#import "../../generated/perf-viper-scalars.typ": *

== Performance Evaluation <sec:results-perf>
#todo[
  *The numbers below are from an interrupted sweep.* The hand-written corpus of
  @sec:results-perf-viper is complete; the Prusti-generated corpus of
  @sec:results-perf-rust got through nine of its thirty-five files before the
  sweep was stopped, so its table, both grids and all four plots are missing
  rows. Re-run #raw("experiments/02_rust_corpus.py --with-silicon") into the same
  sweep directory and then #raw("experiments/10_report_perf.py"), and this
  callout goes with the gap.
]

Chapter 3 argued that the proof obligations Prusti's encoder produces are mostly
equality problems, and that the cost an SMT-based backend pays on them is a
consequence of the backend rather than of the obligation. This section measures
that claim against Silicon, on two corpora with different provenance.

=== Validity <sec:results-validity>
Validity comes first, because a speedup measured against a verifier that is
proving something weaker is not a speedup. Two checks come before any timing
below: that the two verifiers agree obligation for obligation, and that neither
of them is discharging a body vacuously.

We compare the two verifiers member by member rather than file by file, so that
a file on which one tool proves fewer obligations cannot pass as a file on which
both agree. Over the Prusti-generated corpus the two tools agree on
#rust-agree-verified members that both verify and #rust-agree-rejected that both
reject. #rust-unsound members are verified by Helium and rejected by Silicon,
and #rust-incomplete are verified by Silicon and rejected by Helium. Those two
classes are the disagreements of @sec:results-incomplete, and the first of them
stops a sweep. Over the hand-written corpus the counts are
#viper-agree-verified and #viper-agree-rejected, with #viper-unsound and
#viper-incomplete disagreements.

A verifier that has managed to assume
#vi[`false`] discharges everything instantly and produces a large, worthless
speedup. To rule that out we insert #vi[`assert false`] into every method body
at two positions and re-verify. Every body must reject the assertion.

The two positions do not carry equal authority, and the difference is reported
rather than averaged away. The first position sits immediately after the opening
brace and is always reached, so a body that verifies there is vacuous and the
result is fatal. The second sits above the body's exit run and above the
unreachable cleanup block Prusti emits for the panic path, which is why it cannot
simply be appended before the closing brace. It can still land in a match arm the
method never takes, so a body that verifies there is inconclusive rather than
vacuous.

#rust-vacuity-first bodies survive the first position in the Prusti-generated
corpus and #viper-vacuity-first in the hand-written one, which is what the gate
demands. #rust-vacuity-last survive the second, all of them in the Prusti-generated
corpus and all three of them named: #raw("inventory::m_maybe_add"),
#raw("inventory::m_slots_move") and #raw("state_machine::m_next_state"). Each
rejects the same assertion placed at its start, so none is vacuous on entry, and
the likely reading is the ordinary one: the textually last block of a match
encoding is an arm the method never takes. It is reported rather than resolved.

The gate is not a ritual. A sweep of 30 July 2026 ran without it, was vacuous
over part of the corpus, and reported a time that was not a result. The check
exists because that happened once.

=== Hand-written Viper <sec:results-perf-viper>
The first corpus is written for this evaluation. Its programs are idiomatic
Viper rather than compiler output: recursive predicates over linked structures
and over trees, predicates layered on one another, domains carrying axioms about
their own operations, algebraic datatypes, pure functions with postconditions a
caller reads, loops whose invariants are permissions, and ownership moved across
method boundaries. There are #viper-files of them, #viper-members members in
all, and they are listed in @tbl:perf-viper.

Two results come out of this corpus, and the second is the less comfortable one.
The first is the cost of verifying such a program with each tool. The second is
what an idiomatic Viper program has to give up before Helium will accept it at
all.

The second is worth stating before the first, because it decides what the first
means. Sequences, sets, multisets and maps are unavailable, quantified
permissions are unavailable, magic wands are unavailable, and every quantifier
must carry a trigger the author wrote, since Helium infers none. Beyond the
constructs @sec:results-unsupported has already ruled out, a further handful of
restrictions showed up only in the writing, each of them a program Silicon
verifies and Helium does not; @sec:results-incomplete discusses them as
instances of the algebraic gaps found there rather than repeating them as a
list of one-off cases here.

The corpus is therefore not a neutral sample of Viper, and nothing here should
be read as though it were. It is a sample of the Viper that Helium can read,
and each restriction is recorded as a case of its own beside the corpus, with
the program Silicon verifies and the one-line change that makes Helium accept
it.

#include "../../generated/perf-viper-table.typ"

Helium takes #viper-ours over the whole corpus against Silicon's
#viper-silicon, a ratio of #viper-ratio-total, and the geometric mean of the
per-program ratios is #viper-ratio-geo. The spread runs from
#viper-worst-ratio on #viper-worst to #viper-best-ratio on #viper-best.

One qualification belongs with those numbers rather than in a footnote. Helium's
times here are tens of milliseconds, which is close to the cost of starting the
process at all. The ratio therefore understates the difference in verification
work, since Helium's column carries a fixed overhead that Silicon's column does
not. That is the conservative direction and it is the direction taken, but
it also means this corpus measures the shape of the advantage rather than its
size. The corpus of @sec:results-perf-rust, whose files are an order of
magnitude larger, is where the size is measured.

=== The Prusti-generated benchmark <sec:results-perf-rust>
The second corpus is Prusti's own output for spec-less Rust. Its obligations are
framing, fold and unfold, and discriminant well-formedness, not hand-written
functional specifications. That is the class Helium is aimed at, and it is the
class these numbers are about. They say nothing about a program carrying rich
specifications, and @sec:results-features is where that boundary is drawn.

The corpus is #rust-files files and #rust-members members, and its sources fall
in three groups. Thirteen are encodings of hand-written Rust
programs: vector and matrix arithmetic, a bank transfer, a state machine, an
inventory, a physics step, a tuple classifier, a shape-area calculator, a colour
blender, a collision test, and borrows stored in struct fields. The
#raw("depth_dD_mM") family varies two knobs of a generated program, control-flow
nesting depth and statements per basic block, and exists to separate a constant
factor from an asymptotic one. The #raw("enum_vN_pD") grid varies an enum's
variant count against its payload nesting depth, and exists to locate the point
at which Helium stops winning.

Every file is committed as Viper rather than regenerated, because regenerating
one costs minutes of Prusti and the encoder is not what is being measured.

@tbl:perf-rust gives the thirteen encodings of hand-written programs, gathered
by the pattern each exercises. The two generated families are held out of it and
plotted instead: twelve near-identical rows would answer the question "what was
the number", and what the families were generated to answer is what the number
does as the knob turns.

#include "../../generated/perf-rust-table.typ"

Over those thirteen files Helium takes #rust-ours against Silicon's
#rust-silicon, a ratio of #rust-ratio-total, with a geometric mean over the
per-file ratios of #rust-ratio-geo. The spread runs from #rust-worst-ratio on
#rust-worst to #rust-best-ratio on #rust-best.

==== Nesting depth and block size <sec:results-perf-depth>
The #raw("depth_dD_mM") family asks whether the advantage is a constant factor
or survives as the program grows. Each knob is plotted with the other held at
its middle value. Averaging across the held knob would mix a run abandoned at
the cap into a mean and quietly turn a bound into a number.

#include "../../generated/perf-depth-plot.typ"

#include "../../generated/perf-depth-grid.typ"

==== Variants and payload depth <sec:results-perf-enum>
The #raw("enum_vN_pD") grid varies two knobs of a Rust enum against each other.
The two are expected to behave differently, and the difference rather than
either curve is the finding.

#include "../../generated/perf-enum-plot.typ"

#include "../../generated/perf-enum-grid.typ"

#todo[
  Write the three findings the two families are for, once the plots are in front
  of you: whether the depth advantage is constant or growing, where the enum
  crossover is, and whether the grid predicts the weakest file of
  @tbl:perf-rust from its coordinates alone. The prediction should be stated and
  confirmed rather than asserted. The limit at the top of the enum grid, any
  member Helium rejects and Silicon verifies, belongs here, named, with the
  obligation it fails.
]
