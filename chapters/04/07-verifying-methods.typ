#import "../../macros.typ": *

== Verifying Methods <sec:impl-cfg>

#todo[
  This is the control-flow half of methods: what it takes to walk a method
  body. Calling a method is a separate concern and lives in the next section.

  Everything up to here has been straight-line. This section is where that
  assumption is discharged, and where the heap of @sec:impl-heap acquires the
  machinery it was deliberately introduced without.

  - Blocks and the order they are visited. Prusti emits a flat `goto` CFG and
    never a structured statement, so block order is the execution order.
  - Path conditions as cubes of branch literals. Why one e-graph with
    pc-gated facts rather than forking a graph per path — say what
    that buys and what it costs.
  - Joining values: two arms producing different values for the same variable
    become a select on the branch condition.
  - Joining heaps, the harder case. A chunk carries the cube under which it is
    held, so a permission taken on one arm stays distinguishable from an
    unconditional one. This is what @sec:impl-heap deferred.

    Say explicitly that this is *not* the treatment a guarded footprint gets.
    @sec:impl-heap pushes a resource body's guard into the amount as a ternary
    and keeps the chunk unconditional; a join deliberately does the opposite,
    carrying a flat cube on the chunk so that the amount stays guard-free and
    no `0` leaf is ever built. Same-shaped problem, opposite answer, and the
    reason is cost. A reader who is not told will assume the first mechanism
    scaled up.
  - Sufficiency, revisited: the demand must now be met by a *sum* over the
    pc-aliased chunks rather than by a single chunk. Give the shape of a
    partially drained chunk, `pc ? 0 : 1/1`, since the next section's findings
    turn on it.

  #para[Run-in headings] Blocks and block order / Path conditions /
  Joining values / Joining heaps / Sufficiency under a path condition
]
