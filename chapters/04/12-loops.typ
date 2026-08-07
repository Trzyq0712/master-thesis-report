#import "../../macros.typ": *

== Loops <sec:impl-loops>

#todo[
  - Invariants, and framing across iterations. Builds directly on the block
    walk of @sec:impl-cfg — a loop is the case where the CFG stops being
    acyclic.
  - Say plainly that Prusti emits a flat `goto` CFG and never `while`, so loops
    are supported because a Viper backend should support them, not because the
    corpus needs it.
  - Point at the open cases under `tests/cases/known_limitations/loops/` and be
    specific about which shapes fail.

  #para[Run-in headings] Invariants / Framing / Where we fall short
]
