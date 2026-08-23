#import "@preview/ethz-cadmo-inspired-thesis:0.1.0": *

#import "macros.typ": *

#show: setup.with(
  "My Thesis Title", // title
  "Jakub Adam Trzykowski", // author
  ("Jonáš Fiala", "Prof. Dr. Peter Müller"), // advisors
  thesis-type: "Master Thesis",
  department: "Department of Computer Science",
  bib: bibliography("bib.bib", title: none),
)

#show: code-setup

// Run-in `#para` headings are `outlined: false`, so they would not be bookmarked
// by default. Opt every heading in; `#todo` / `#note` opt their bodies back out.
#set heading(bookmarked: true)

#frontchapter[Abstract]
#include "chapters/00-abstract.typ"

#outline(depth: 2)

#show: mainmatter

= Introduction
#include "chapters/01-introduction.typ"

= Background <sec:background>
#include "chapters/02-background.typ"

= Approach <sec:approach>
#include "chapters/03-approach.typ"

#include "chapters/04-implementation.typ"

= Results <sec:results>
#include "chapters/05-results.typ"

= Future Work <sec:future-work>
#include "chapters/06-future_work.typ"

#show: appendix

#frontchapter[Appendix]

#include "chapters/A-lowering-reference.typ"
