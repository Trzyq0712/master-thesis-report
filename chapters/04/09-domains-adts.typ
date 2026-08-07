#import "../../macros.typ": *

== Domains and ADTs <sec:impl-adts>

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
  - Be honest about what is deferred: disequality for an opaque scrutinee. Say
    why — an e-graph stores equalities, not disequalities — and what the two
    candidate fixes are.
  - Injectivity is *not* deferred, contrary to an earlier version of this note:
    `func_registry.rs:378` pushes `inj_rule` for every constructor, and
    `rewrite.rs:339` justifies it by constructors being free — two applications
    of one constructor can share an e-class without their arguments having been
    merged, so the backward direction carries information. Location functions
    get no such rule; if the contrast is worth drawing it is one clause here,
    not a paragraph in Fields.

  #para[Run-in headings] Domains / Constructors and projections /
  Discriminators / What we do not decide
]
