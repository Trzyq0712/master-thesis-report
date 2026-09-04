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

// Figures and listings sit tight against the surrounding text at the default
// spacing. Give every one of them the same extra room above and below.
#show figure: set block(above: 1.6em, below: 1.6em)

// Typst keeps a heading on the same page as the text under it by giving its
// block `sticky: true`. The template's level-2 and level-3 show rules replace
// the heading with bare inline content, which throws that block away and lets a
// section title strand at the foot of a page (5.3 did). Wrap the template's
// output back into a sticky block.
#show heading.where(level: 2): it => block(sticky: true, it)
#show heading.where(level: 3): it => block(sticky: true, it)

#frontchapter[Abstract]
#include "chapters/00-abstract.typ"

#outline(depth: 2)

#show: mainmatter

#include "chapters/01-introduction.typ"

#include "chapters/02-background.typ"

#include "chapters/03-approach.typ"

#include "chapters/04-implementation.typ"

#include "chapters/05-results.typ"

#include "chapters/06-conclusions-future-work.typ"


#show: appendix

#frontchapter[Appendix]

// #include "chapters/A-lowering-reference.typ"
#include "chapters/B-rewrite-rules.typ"
#include "chapters/C-benchmarks.typ"
