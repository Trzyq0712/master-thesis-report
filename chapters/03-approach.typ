#import "../macros.typ": *

#note[
  *How this chapter is organised.* This chapter is design; the next is
  mechanism. The order matters: the first section establishes empirically what
  the target actually is, so the principles that follow read as derived from
  evidence rather than declared, and the non-goals read as scoping rather than
  apology.
]

== What Prusti Demands of a Verifier <sec:prusti-needs>

#todo[
  New section, and the evidence base for everything after it.

  - *The corpus.* 22 Prusti encodings committed under `benchmarks/rust/vpr/`
    in the `silver-oxide` tree, roughly 217k lines, 2886 verifying members.
    Emphasise that the sources are _spec-less_ Rust: the obligations come from
    Prusti's own type encoding — framing, fold/unfold, discriminant
    well-formedness — and not from hand-written functional specifications. That
    is precisely the class an equality-reasoning core is aimed at, and it is
    the honest framing of the non-goals below.
  - *A table of what appears,* with counts. The measured picture: domains and
    axioms; `adt` (snapshots are Viper ADTs); predicates, including abstract
    ones; heap-dependent functions; bodyless functions carrying `ensures`;
    methods; `fold` / `unfold` / `unfolding`; `inhale` / `exhale`;
    `acc(.., write)` almost exclusively; labelled `old`; a flat `goto` CFG;
    triggered `forall` inside domain axioms; `let .. in`.
  - *What never appears,* which is just as load-bearing: no `while`, no magic
    wands, no quantified permissions, no `perm` or `forperm`, no `exists`, no
    collection types, no fractional permission literals, no `new(*)`, no
    `decreases`.
  - Conclude by naming the target fragment in one sentence. The implementation
    chapter is then organised against exactly that list, and Beyond the
    Fragment cites this section rather than re-arguing the point.

  #para[Run-in headings] The corpus / What appears / What never appears /
  The target fragment
]

#note[
  Decide whether the table gives raw counts or just presence and absence.
  Counts are more convincing but invite the question "counts of what" — they
  would need a sentence distinguishing declarations from occurrences.
]

== Guiding Principles for the Verifier

#todo[
  - Performance is the goal; say what that costs elsewhere.
  - Separate the decisions Prusti's encoding forces from the ones that are
    right for any frontend, in prose rather than by notation. Forced: the
    scoping above, `write`-only permissions on the fast path, the `goto`-CFG
    execution order, snapshots as first-class ADTs. Right anyway: locations as
    types so that fields and predicates collapse into one concept, a heap
    partitioned by location kind, the e-graph as the symbolic state, exact
    rational permissions, VMIR being SSA at all. The second group is what
    survives a different frontend, and Future Work turns on the distinction.
  - Third principle, and the one most easily lost: *recording without
    discharging.* The symbolic state stays complete even where the decision
    procedure is incomplete. A failed obligation is a failure to prove, not a
    loss of information, so it can be escalated to a stronger procedure rather
    than being unsound or unrecoverable. State it as a property of the design
    here; the implementation chapter marks each place it applies.

  #para[Run-in headings] Performance first / Only support the core /
  Fewer concepts, uniformly treated / Complete state, incomplete procedure
]

With the main goal of the new verifier is performance, this will significantly
influence the design of the new verifier. The guiding principles are thus
the following:

#todo[Turn this list into prose once the principles above are settled.]

- *Only support the core.* This means that in the

== The New Viper Intermediate Representation

#todo[
  Design only — how the verifier _executes_ VMIR belongs in the next chapter.

  - Why an IR at all, rather than running over Silver directly: a smaller
    language means each verifier rule is written once, and the shapes that
    matter can be made explicit rather than recovered from syntax.
  - Values and heap states are both SSA temporaries, but of separate sorts:
    `e` names an e-class, `h` a heap state, and only the former is a value.
  - Resources subsume predicates, method contracts and function
    preconditions, so one mechanism covers all three.
  - What VMIR deliberately does not have, and why.
  - *Pseudo-VMIR is defined here*, in the closing paragraph, and nowhere else.
    It is only definable once the real syntax is on the page: show one
    construct in full — a postcondition, which is a function of its own rather
    than syntax attached to a declaration — beside the schematic form the
    thesis writes instead, and say that listings tagged #emph[pseudo-VMIR]
    elide exactly that kind of mechanical structure while listings tagged
    #emph[VMIR] are what the verifier would be given. @sec:implementation's
    introduction currently carries a standalone version of this; cut it back to
    a pointer once this section exists.

  #para[Run-in headings] Why an intermediate representation / Values and heap
  states / Resources / What VMIR omits / Writing VMIR down
]

== Non-Goals

#todo[
  - Keep the paragraph below, but reframe it: this is a scoping decision
    justified by @sec:prusti-needs, not a limitation being confessed.
  - Tie it to the recording principle: out of scope to _prove_ is not out of
    scope to _record_.
  - Be concrete about which obligation shapes are excluded, and say what
    happens to them when they arise.
]

In general, the new verifier is not meant to be able to discharge functional
specification proofs. While it may occasionally be able to do so, if the obligation
is of a form that can be discharged by equality reasoning, it is not meant to
be able to do it in general. This include
