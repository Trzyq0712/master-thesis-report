#import "../../macros.typ": *

== Calling Methods

#todo[
  The other half of methods: a call is a heap transaction, not a control-flow
  event. Nothing here needs the callee's body.

  - Contracts become resources: `m#requires` and `m#ensures`. The same
    mechanism as a predicate, which is the point — one construct covers
    predicates, method contracts and function preconditions.
  - A call site is an exhale of the precondition followed by an inhale of the
    postcondition.
  - Two-state postconditions: the `Ctx` precondition mode, the trailing
    snapshot parameter, and the entry `FromSnap` that widens it back into a
    heap. This is how `old` is handled. Prusti leans on `old` heavily, so this
    had to be fast; the encoding is the natural one for any frontend anyway.
  - Reborrows and aliasing: `&mut` into a call is where the corpus first
    broke. These are real results and deserve writing up as findings, not as
    implementation detail. All four turn on the pc-gated chunks of
    @sec:impl-cfg:
    + The location meets the chunk only after a full saturation, so the miss
      retry has to sit after the provably-zero check — retrying at every miss
      cost 36×.
    + A reborrow minted under an arm's path condition is invisible to
      ground-canonical matching; route the miss through the under-pc lookup.
    + Consecutive reborrows: prove sufficiency over the whole pc-alias set,
      not against the first matching chunk. The first chunk a probe matches
      may be one an earlier consume already drained. The unsoundness case is
      pinned by `pc_alias_ground_miss_double_spend.vpr`.
    + Re-reading a field after a call: the `%pre` token must survive recipe
      slicing. Resolves in Functions.

  #para[Run-in headings] Contracts as resources / Call sites /
  Two-state postconditions / Reborrows and aliasing
]
