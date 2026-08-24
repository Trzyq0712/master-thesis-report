// Standalone excerpt: sections 4.1–4.6 only, callouts stripped.
//
//   typst compile --input no-notes=1 excerpt.typ excerpt.pdf
//
// Sections outside the excerpt cannot be `@`-referenced, since their labels are
// not in this document. The `show ref` rule below prints their titles instead.

#import "macros.typ": *

#set document(title: "Excerpt: VMIR Through Interacting with the Heap")
#set page(paper: "a4", margin: (x: 3.5cm, y: 3cm), numbering: "1")
#set text(font: "New Computer Modern", size: 11pt, lang: "en")
#set par(justify: true, leading: 0.65em, spacing: 1.2em)
#set heading(numbering: "1.1", bookmarked: true)

#show: code-setup

// Chapter 4, sections 1 through 6.
#counter(heading).update((4, 0))

#let external-sections = (
  "sec:prusti-needs": [What Prusti Demands of a Verifier],
  "sec:example": [A Guiding Example],
  "sec:impl-adts": [ADTs],
  "sec:impl-predicates": [Predicates],
  "sec:impl-calls": [Calling Methods],
  "sec:impl-cfg": [Control Flow],
  "sec:impl-functions": [Functions],
  "sec:impl-wildcards": [Wildcard Permissions],
  "sec:beyond-fragment": [Beyond the Fragment],
  "sec:impl-together": [Putting It Together],
  "sec:appendix-rewrites": [Rewrite Rules],
  "sec:results": [Results],
  "lst:example-viper": [the guiding example],
  "lst:example-loop": [the guiding example],
  "lst:example-body": [the guiding example],
)

#show ref: it => {
  let key = str(it.target)
  if key in external-sections {
    emph(external-sections.at(key))
  } else {
    it
  }
}

#align(center)[
  #text(size: 15pt, weight: "bold")[Excerpt — Implementation, §4.1–4.6] \
  #v(0.3em)
  #text(size: 10pt)[Jakub Adam Trzykowski]
]
#v(1.5em)

// The chapter's own intro, from chapters/04-implementation.typ, verbatim.
We present the design and implementation of Viper Mid-Level Intermediate
Representation (VMIR) and Helium verifier in this chapter.
Sections increase in complexity, each building on the ones before it, and each
introduces only the VMIR constructs it needs rather than assuming the
representation up front.

We start by executing the simplest programs a verifier can process, and by
explaining the mechanism by which the verifier discharges the obligations
they raise.

Afterwards, we introduce the symbolic heap and explain how we handle heap
constructs from Viper like fields and predicates. We then proceed
with how user-defined ADTs and domains are encoded and reasoned about.

#include "chapters/04/02-execution-model.typ"
// #include "chapters/04/03-discharging.typ"
#include "chapters/04/04-the-heap.typ"
#include "chapters/04/05-heap-interaction.typ"

#bibliography("bib.bib", title: [References])
