#import "../../macros.typ": *

== A Worked Example

#todo[
  Beat 1 only — this section sets the contract for the rest of the chapter.

  - The Rust source: `Account` from `benchmarks/rust/src/bank_transfer.rs`
    (two `i32` fields, one `&mut` method). Already in the corpus with its
    encoding committed, so #link(<sec:impl-together>)[Putting It Together] can
    show the real thing rather than an imitation.
  - The Prusti encoding, abridged. *Keep:* the snapshot `adt`, the `p_Int` and
    `p_Account` predicates, `p_Account_snap` (with `unfolding` in its body),
    `p_Account_assign`, `s_Param` with `make_generic` / `make_concrete` (the
    only bodyless functions carrying `ensures`, and a round-trip inverse), and
    `p_Param` (the only abstract predicate). *Drop:* the `TypeOf` and trait
    domains, the overflow-checking `mir_binop_*WithOverflow` family, and the
    per-statement `label` blizzard — volume, not new mechanism.
  - State the contract: by the end of the chapter every construct in this
    listing has been covered.

  #para[Run-in headings] The source program / The encoding / What we left out
]
