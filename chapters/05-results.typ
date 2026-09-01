#import "../macros.typ": *


// The chapter is split one file per section, under `chapters/05/`, following
// the layout of chapter 4.
//
// Skeleton, 30 August 2026. Every number this chapter will quote comes from
// `helium-eval`, whose `raw.jsonl` is the single source of truth; the tables are
// generated into `helium-eval/report-tables/` and included here. Nothing is
// typed in by hand. Where a measurement does not exist yet, the prose says so in
// a `#todo` rather than carrying a placeholder that could be mistaken for a
// result.

// The chapter heading `= Results <sec:results>` lives in `main.typ`, as it does
// for every chapter but 4.

= Results and Analysis <sec:results>

In this chapter we report what Helium verifies, how fast it is, and where it
fails. Four questions, in order, with the measurement protocol stated between the
first and the second.

@sec:results-features asks which of Viper Helium implements. It separates two
kinds of gap that a reader has every reason to conflate: a construct Helium does
not translate at all, and a construct it translates but cannot prove anything
about. The first is a feature gap and is visible in the source; the second is a
verification gap and is only visible by measurement.

@sec:results-setup states the machine, the toolchain and the protocol under
which every time in the sections that follow was taken. It comes second rather
than first because @sec:results-features reports verdicts rather than times, and
a verdict does not depend on how a stopwatch was run.

@sec:results-perf compares Helium against Silicon on two corpora. The first is
hand-written Viper, written for this evaluation. The second is the output of
Prusti's encoder on spec-less Rust, which is the input class Helium is aimed at.
Both halves open with validity, since a verifier that has managed to assume
#vi[`false`] is fast and worthless.

@sec:results-attribution then explains the pattern in the timings. It relates
each result to the counters Helium records for itself, and it states the shapes
on which Helium loses to Silicon as plainly as the shapes on which it wins.

#include "05/01-features.typ"
#include "05/02-setup.typ"
#include "05/03-performance.typ"
#include "05/04-attribution.typ"
