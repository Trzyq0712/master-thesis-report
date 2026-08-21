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
  "sec:vmir-design": [The Verifier's Intermediate Representation],
  "sec:impl-adts": [ADTs],
  "sec:impl-predicates": [Predicates],
  "sec:impl-calls": [Calling Methods],
  "sec:impl-cfg": [Control Flow],
  "sec:impl-functions": [Functions],
  "sec:impl-wildcards": [Wildcard Permissions],
  "sec:impl-together": [Putting It Together],
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
This chapter builds the backend one construct at a time, checking each against
the program presented in @sec:example. It opens with a short look at VMIR
itself, enough that the listings which follow read without a preamble, and then
starts from the smallest thing a verifier can do: execute a heapless instruction
stream and discharge the obligations it raises — the prover's tiers, and the
rewrite rules they run underneath every one of them. The symbolic heap comes
next, without conditional structure at first, so that its operations can be
stated on their own; then fields, the instructions that move permission; then
datatypes, whose rules are what a fold and its unfold cancel by; then
predicates, which is where that cancellation is put to use. Domains and the
quantified axioms they carry close out the values a program can build, and only
then does the chapter turn to calls, method bodies, and control flow — which is
what forces two heaps to be reconciled. Wildcard permissions, functions and
loops close the chapter, each needing the ones before it and nothing after.

The order is deliberate in one further respect. Each section says what its
construct costs the verifier and, where the mechanism differs from Silicon's,
where the difference lies. The claim the chapter is accumulating is not that any
single mechanism is novel, but that a particular set of them composes into a
verifier on which the great majority of a Prusti program's obligations are true by
construction rather than by proof — and @sec:impl-together is where that claim is
checked against the whole of the guiding example.

#include "chapters/04/01-vmir.typ"
#include "chapters/04/02-execution-model.typ"
#include "chapters/04/03-discharging.typ"
#include "chapters/04/04-symbolic-heap.typ"
#include "chapters/04/05-fields.typ"
#include "chapters/04/06-heap-interaction.typ"

#bibliography("bib.bib", title: [References])
