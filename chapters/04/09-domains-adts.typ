#import "../../macros.typ": *

== Domains and ADTs

#todo[
  - Domains: uninterpreted functions plus axioms; nothing heap-dependent.
  - ADTs are ordinary function applications plus a metadata side table, not new
    IR nodes, so no match site in the verifier had to learn about them.
  - Projection reduction: a destructor applied to a constructor gives the
    field back.
  - Discriminators via one `@tag` function per ADT rather than per-variant
    `is_C` functions — this avoids $O(n^2)$ rules in the number of variants,
    and the resulting equality then constant-folds.
  - Constructor distinctness falls out for free: forcing two constructors equal
    collides two integer literals in one e-class, which constant folding
    rejects.
  - Be honest about what is deferred: disequality for an opaque scrutinee, and
    injectivity. Say why — an e-graph stores equalities, not disequalities —
    and what the two candidate fixes are.

  #para[Run-in headings] Domains / Constructors and projections /
  Discriminators / What we do not decide
]
