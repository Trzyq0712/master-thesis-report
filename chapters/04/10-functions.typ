#import "../../macros.typ": *

== Functions

#todo[
  - Heap-dependent functions: `requires acc(..)` plus a body that unfolds.
    `p_Account_snap` in the worked example is the canonical shape.
  - Bodyless functions with `ensures` — postconditions as axioms. This is the
    `make_generic` / `make_concrete` path: no body at all, and the contract is
    a round-trip inverse, `make_concrete(make_generic(x)) == x`. Pure equality
    facts, which is exactly what the core is good at. Also
    `s_Param_typeof(result) == s_Account_type()`, feeding the tag machinery of
    Domains and ADTs.
  - Recipes: how a function occurrence becomes the steps that unfold its body,
    and the `%pre` token that gates them.
  - Recipe slicing: the backward closure from the result pruned orphan token
    steps, so an occurrence introduced by a method contract stayed opaque and
    two reads of an unchanged field were provably unrelated. Finding 4 of
    Calling Methods resolves here.

  #para[Run-in headings] Heap-dependent functions / Postconditions as axioms /
  Recipes / Slicing
]
