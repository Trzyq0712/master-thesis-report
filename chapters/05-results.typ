#import "../macros.typ": *


// The chapter is split one file per section, under `chapters/05/`, following
// the layout of chapter 4. Three sections, no `===` anywhere: the parts of each
// are `#para` run-in headings.
//
// Every number the chapter quotes comes from `helium-eval`, whose `raw.jsonl` is
// the single source of truth; the tables are generated into
// `report/generated/` and included here. Nothing is typed in by hand.

= Evaluation and Discussion <sec:results>

This chapter evaluates the proposed system in three parts. @sec:results-qualitative
evaluates what the new intermediate representation contributes to a backend, which
Viper constructs VMIR does not support, and where Helium's reasoning stops.
@sec:results-quantitative then quantitatively measures the performance of VMIR and
Helium against Silicon on two corpora, one of hand-written Viper and
one of Prusti's output on Rust programs carrying no specifications.
@sec:results-discussion accounts for the spread of those timings, relating each
result to the counters Helium records for itself and stating program shapes on which
Helium loses to Silicon alongside those on which it wins.

#include "05/01-qualitative.typ"
#include "05/02-quantitative.typ"
#include "05/03-discussion.typ"
