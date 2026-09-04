#import "../macros.typ": *


// The chapter is split one file per section, under `chapters/05/`, following
// the layout of chapter 4. Three sections, no `===` anywhere: the parts of each
// are `#para` run-in headings.
//
// Every number the chapter quotes comes from `helium-eval`, whose `raw.jsonl` is
// the single source of truth; the tables are generated into
// `report/generated/` and included here. Nothing is typed in by hand.

= Evaluation and Discussion <sec:results>

This chapter evaluates the pipeline in three parts. @sec:results-qualitative
describes what the intermediate representation contributes to a backend and where
the supported fragment stops, separating a construct VMIR does not represent from
one it represents but about which Helium proves nothing. Neither question
requires a measurement.

@sec:results-quantitative states the machine, the toolchain and the measurement
protocol, argues that the numbers taken under that protocol are valid, and then
compares Helium against Silicon on two corpora. The first is hand-written Viper,
written for this evaluation, and the second is the output of Prusti's encoder on
Rust programs carrying no specifications, which is the input class Helium is
aimed at.

@sec:results-discussion accounts for the pattern in those timings. It relates
each result to the counters Helium records for itself, and it states the shapes
on which Helium loses to Silicon as plainly as the shapes on which it wins.

#include "05/01-qualitative.typ"
#include "05/02-quantitative.typ"
#include "05/03-discussion.typ"
