#import "../../macros.typ": *

== Case Study <sec:results-case-study>
The corpora of @sec:results-perf were assembled for this evaluation, which means
they were assembled by someone who knew what Helium supports. This section takes
a published Rust crate that nobody wrote with Helium in mind and reports what
happens to it.

The procedure has three stages, and each one is reported rather than
summarised. First, Prusti encodes the crate's sources and we count what came
through. Second, we remove from the encoding every declaration that uses a
construct Helium does not implement, and we classify each removal. Third, we
verify what remains with Silicon and with Helium and compare the two.

The second stage is the honest part of the section. A pruned program is not the
crate, and quoting a speedup on it without saying what was removed would
overstate the result. Every removed declaration is therefore attributed to one
of two causes: a *feature gap*, meaning Helium does not translate the construct,
or a *verification gap*, meaning Helium translates it and cannot discharge its
obligations. If the pruning list turns out to be most of the crate, that is the
result of this section and it is written as one.

#todo[
  *Choosing the crate.* Not yet chosen, and deliberately not chosen in advance:
  committing to a crate before knowing whether Prusti can encode it turns a case
  study into a bug report about the frontend. The candidates are dependency-free
  and free of #ru[`unsafe`], so that the screen measures Helium and Prusti rather
  than a build. The bar, in order: Prusti encodes it; enough members survive to
  be worth calling a case study; Helium discharges enough of them that the pruning
  list is a subsection rather than the whole section. Take the largest candidate
  that clears the bar.

  The screening result is itself reportable, in one short table: per candidate,
  sources, sources encoded, members, members verified. It says how far a Rust
  crate typically gets, which is a broader claim than the one crate that is then
  studied in detail.
]

#todo[
  *What the section reports, once the crate is fixed.*

  - What the crate does and how large it is, in Rust source terms.
  - What Prusti produced: declarations, methods, functions, predicates, domains.
  - The pruning table: every removed declaration, the construct that forced the
    removal, and which of the two causes it falls under. Aggregated by construct,
    with the count, since a single unsupported construct will account for many
    declarations.
  - The verification result on what remains, both tools, with the ratio.
  - What Helium still fails on the pruned program. Named, with the obligation
    each failure stops at. Helium reports the VMIR instruction it stopped at, so
    this can be attributed rather than guessed.

  If Helium fails to verify the pruned crate at all, that is the finding and the
  section says so directly.
]
