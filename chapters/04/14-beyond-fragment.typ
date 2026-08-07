#import "../../macros.typ": *

== Beyond the Fragment <sec:beyond-fragment>

#todo[
  Renamed from "Missing features" — splitting the list in two is the whole
  point of the section.

  - *Not needed by the corpus*: magic wands, quantified permissions,
    `perm` and `forperm`, the collection types, fractional permission literals,
    `new(*)`. None appear in 217k lines of Prusti output; cite the census
    rather than asserting it.
  - *Genuinely unsupported*: the loop shapes of Loops, ADT disequality
    and injectivity from Domains and ADTs, and anything else that is a gap
    rather than a scoping decision.
  - Close on the recording principle: collect the "what we record" notes and
    state the invariant once, in full. An obligation we cannot discharge still
    leaves the state complete enough for another procedure to take over.
]
