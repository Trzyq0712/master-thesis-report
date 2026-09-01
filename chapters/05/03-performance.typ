#import "../../macros.typ": *
#import "../../generated/perf-validity.typ": *
#import "../../generated/perf-rust-scalars.typ": *
#import "../../generated/perf-viper-scalars.typ": *

== Performance Evaluation <sec:results-perf>
#todo[
  The two generated families of @sec:results-perf-depth and
  @sec:results-perf-enum are not in this sweep. Everything else below is.
]

Chapter 3 argued that the proof obligations Prusti's encoder produces are mostly
equality problems, and that the cost an SMT-based backend pays on them is a
consequence of the backend rather than of the obligation. This section measures
that claim against Silicon, on two corpora with different provenance.

=== Validity <sec:results-validity>
Validity comes first, because a speedup measured against a verifier that is
proving something weaker is not a speedup. Two checks come before any timing
below: that the two verifiers agree obligation for obligation, and that neither
of them is discharging a body vacuously.

We compare the two verifiers declaration by declaration rather than file by
file, so that a file on which one tool proves fewer obligations cannot pass as a
file on which both agree. A declaration is the unit because Helium reports a
method as three obligations, the body and each of the two contract clauses, where
Silicon reports one; Helium is credited with a declaration only when all three
verify. Over the Prusti-generated corpus the two tools agree on
#rust-agree-verified declarations that both verify and #rust-agree-rejected that
both reject. #rust-unsound declarations are verified by Helium and rejected by
Silicon, and #rust-incomplete are verified by Silicon and rejected by Helium.
Those two classes are the disagreements of @sec:results-incomplete, and the
first of them stops a sweep. Over the hand-written corpus the counts are
#viper-agree-verified and #viper-agree-rejected, with #viper-unsound and
#viper-incomplete disagreements.

A verifier that has managed to assume
#vi[`false`] discharges everything instantly and produces a large, worthless
speedup. To rule that out we insert #vi[`assert false`] into every method body
at two positions and re-verify. Every body must reject the assertion.

The two positions do not carry equal authority, and the difference is reported
rather than averaged away. The first position sits immediately after the opening
brace and is always reached, so a body that verifies there is vacuous and the
result is fatal. The second sits above the body's exit run and above the
unreachable cleanup block Prusti emits for the panic path, which is why it cannot
simply be appended before the closing brace. It can still land in a match arm the
method never takes, so a body that verifies there is inconclusive rather than
vacuous.

Every body in both corpora rejects the assertion at both positions:
#rust-vacuity-first and #rust-vacuity-last survivors in the Prusti-generated
corpus, #viper-vacuity-first and #viper-vacuity-last in the hand-written one.
The second position is therefore reached everywhere it was placed, and no timing
below is taken over a body that assumed its own contradiction.

The gate is not a ritual. A sweep of 30 July 2026 ran without it, was vacuous
over part of the corpus, and reported a time that was not a result. The check
exists because that happened once.

=== Hand-written Viper <sec:results-perf-viper>
The first corpus is written for this evaluation. Its programs are idiomatic
Viper rather than compiler output: recursive predicates over linked structures
and over trees, predicates layered on one another, domains carrying axioms about
their own operations, algebraic datatypes, pure functions with postconditions a
caller reads, loops whose invariants are permissions, and ownership moved across
method boundaries. There are #viper-files of them, #viper-members members in
all, and they are listed in @tbl:perf-viper.

Two results come out of this corpus, and the second is the less comfortable one.
The first is the cost of verifying such a program with each tool. The second is
what an idiomatic Viper program has to give up before Helium will accept it at
all.

The second is worth stating before the first, because it decides what the first
means. Sequences, sets, multisets and maps are unavailable, quantified
permissions are unavailable, magic wands are unavailable, and every quantifier
must carry a trigger the author wrote, since Helium infers none. Beyond the
constructs @sec:results-unsupported has already ruled out, a further handful of
restrictions showed up only in the writing, each of them a program Silicon
verifies and Helium does not; @sec:results-incomplete discusses them as
instances of the algebraic gaps found there rather than repeating them as a
list of one-off cases here.

The corpus is therefore not a neutral sample of Viper, and nothing here should
be read as though it were. It is a sample of the Viper that Helium can read,
and each restriction is recorded as a case of its own beside the corpus, with
the program Silicon verifies and the one-line change that makes Helium accept
it.

We summarise each program below by what it contains and by the obligations it
raises, in the order of @tbl:perf-viper, which gathers the programs by the
construct each is built around.

/ #raw("adt_expr"): An expression language as an algebraic datatype, and a second
  datatype for its values. The obligations are constructor injectivity,
  discriminant exclusivity and the destructor equations.
/ #raw("branch_paths"): Conditionals and their joins. The path count rises from a
  single join over two arms to four independent guards with sixteen paths, and
  the file also covers the #vi[`elseif`] ladder, a ternary against the equivalent
  branch, a #vi[`let`] inside a guard, and calls and allocation under a branch.
  The obligations are the equation each guard supplies and the state the join
  receives from both arms.
/ #raw("dispatch_tags"): One branch point with many arms, which is the shape a
  #ru[`match`] takes once Prusti has encoded it. Three, five and eight arms are
  driven by an algebraic datatype's discriminant, eight more by an integer field,
  and the two forms are nested inside each other, so the cost reads as the cost
  of the split itself.
/ #raw("goto_jumps"): Forward jumps over a reducible control-flow graph: a
  skipped block, two and then four #vi[`goto`]s converging on one exit label, a
  dispatch whose arms jump to a common tail, a jump over a call, a jump out of a
  loop body, and a back edge built from #vi[`goto`] rather than #vi[`while`]. The
  obligations are those of the joins these jumps create.
/ #raw("label_snapshots"): #vi[`label`] and #vi[`old[l]`], with the control flow
  between the label and the read varying over a branch, a join, a loop, a call,
  and labels nested inside one another. Every read sits in a body, since Helium
  rejects #vi[`old[l]`] in a postcondition.
/ #raw("loop_exits"): Loop shape rather than loop framing: three levels of
  nesting, four loops in a row over one permission, a peeled first iteration, a
  body that jumps to the next iteration, a body that leaves through a label past
  the loop, and a loop on either side of a branch. The invariant is held fixed so
  that the cost is attributable to the shape.
/ #raw("domain_axioms"): Pairs, an option and an abstract ordering given only by
  axioms, so the obligations are congruence and axiom instantiation. Every
  quantifier carries a trigger the author wrote.
/ #raw("state_machine"): A protocol whose states are an abstract domain and whose
  transition relation is axioms, with the object holding a state guarded by a
  predicate. Fold and unfold traffic therefore mixes with axiom instantiation.
/ #raw("frame_records"): A multi-field record held through field permissions.
  Most of the work is carrying an unmentioned field's value across a call, and
  splitting a fractional permission and putting it back, so the obligations are
  framing and permission arithmetic.
/ #raw("transfer"): Ownership passed across method boundaries. A predicate stands
  for the right to touch an account, and the obligations are that two accounts
  are distinct and that touching one left the other alone.
/ #raw("pure_functions"): Recursion, mutual recursion, and postconditions a
  caller reads without unfolding the body. Every clause is an equality or a
  disequality, which keeps the arithmetic gap of @sec:results-incomplete out of
  the measurement.
/ #raw("loop_frames"): Invariants that are permissions and equalities rather than
  arithmetic facts, carried around the back edge. It fixes the loop shape and
  varies the invariant, which is the counterpart to what #raw("loop_exits") does.
/ #raw("nested_predicates"): Predicates layered over one another rather than
  recursing, with an abstract predicate at the bottom keeping part of the state
  opaque. The obligations are the permissions each layer holds and the ones an
  abstract predicate refuses to reveal.
/ #raw("list_deep"): A singly linked list under a recursive predicate. Every
  method reaches a fixed depth, so each pays for a chain of unfolds and the
  matching chain of folds, and the obligations are the fold conditions at every
  link.
/ #raw("tree_shape"): A binary tree, whose predicate recurses twice. Unfolding a
  node opens two obligations and the closing fold has to re-establish both, which
  doubles the fold traffic of #raw("list_deep") at each level.

#include "../../generated/perf-viper-table.typ"

Helium takes #viper-ours over the whole corpus against Silicon's
#viper-silicon, a ratio of #viper-ratio-total, and the geometric mean of the
per-program ratios is #viper-ratio-geo. The spread runs from
#viper-worst-ratio on #viper-worst to #viper-best-ratio on #viper-best.

One qualification belongs with those numbers rather than in a footnote. Helium's
times here are tens of milliseconds, which is close to the cost of starting the
process at all. The ratio therefore understates the difference in verification
work, since Helium's column carries a fixed overhead that Silicon's column does
not. That is the conservative direction and it is the direction taken, but
it also means this corpus measures the shape of the advantage rather than its
size. The corpus of @sec:results-perf-rust, whose files are an order of
magnitude larger, is where the size is measured.

=== The Prusti-generated benchmark <sec:results-perf-rust>
The second corpus is Prusti's own output for spec-less Rust. Its obligations are
framing, fold and unfold, and discriminant well-formedness, not hand-written
functional specifications. That is the class Helium is aimed at, and it is the
class these numbers are about. They say nothing about a program carrying rich
specifications, and @sec:results-features is where that boundary is drawn.

The corpus measured here is #rust-files files and #rust-members members, each of
them Prusti's encoding of a hand-written Rust program. Two further families of
generated programs sit beside them and are the subject of
@sec:results-perf-depth and @sec:results-perf-enum. Every file is committed as
Viper rather than regenerated, because regenerating one costs minutes of Prusti
and the encoder is not what is being measured.

The sources carry no specifications, so the obligations are the ones Prusti's
type predicates impose. Each program was written to put one shape of those
obligations under load, and the summaries below name that shape, in the order of
@tbl:perf-rust, which gathers the files by the pattern each exercises.

/ #raw("aabb_collide"): Axis-aligned box tests written as #ru[`if`] and
  #ru[`else`] nested three to five levels deep, with no early return. An inner
  block's path condition is a strict superset of its dominator's, which puts the
  cost of a long cube under load.
/ #raw("color_blend"): Colour blending and clamping written as explicit branch
  chains rather than library calls. A body accumulates a long series of small
  joins, so each block's cube is short and the block count per body is high.
/ #raw("state_machine"): A state enum and an event enum matched against each
  other, so a nested #ru[`match`] produces a grid of arms. Many sibling cubes die
  at the join under one shared dominator cube, and an arm may branch again on top
  of its own discriminant literal.
/ #raw("vec3_math"): Integer vector algebra in which every operation is built
  from calls to the smaller ones. A single block accumulates many call
  obligations, each a fold and unfold plus a snapshot round trip, with almost no
  branching.
/ #raw("shape_area"): An enum whose variants carry nested structs. Each match arm
  must unfold a payload predicate before touching its fields, which is the
  arm-local fold and unfold traffic that makes a block's held permission
  branch-structured.
/ #raw("bank_transfer"): Two #ru[`&mut`] accounts live in one call, with guarded
  debits, credits and swaps. A block's held permission becomes
  branch-structured, and a consumption must be proven against a sum rather than
  against a single chunk.
/ #raw("borrow_fields"): Structs that hold borrows rather than take them as
  parameters, so Prusti's reference predicate appears nested inside another type
  predicate. Folding the struct draws that permission in and unfolding hands it
  back.
/ #raw("physics_step"): A world of three bodies stepped through integrate, clamp
  and bounce, each stage built from smaller helpers. A caller's block inherits
  obligations from several callees, so the ground graph carries a great deal
  before any single block raises its proof.
/ #raw("inventory"): Hand-rolled #ru[`Maybe`] and #ru[`Res`] enums, so error
  paths are ordinary enum arms. A block's cube is a discriminant fact and its
  body then reads the payload, which is where tag knowledge and framing meet.
/ #raw("classify_tuple"): A fixed-arity eight-field buffer classified element by
  element through a match cascade and then summarised. Bodies have a high block
  count where every cube is short, which is the opposite extreme from
  #raw("aabb_collide").
/ #raw("mat3_mul"): Unrolled #ru[`3x3`] integer linear algebra. Every body is one
  long straight-line block with no branching, so the file measures how much a
  single block accumulates before an obligation is raised.

#include "../../generated/perf-rust-table.typ"

Over those #rust-files files Helium takes #rust-ours against Silicon's
#rust-silicon, a ratio of #rust-ratio-total, with a geometric mean over the
per-file ratios of #rust-ratio-geo. The spread runs from #rust-worst-ratio on
#rust-worst to #rust-best-ratio on #rust-best.

==== Nesting depth and block size <sec:results-perf-depth>
The #raw("depth_dD_mM") family varies two knobs of a generated program,
control-flow nesting depth and statements per basic block, and asks whether the
advantage is a constant factor or survives as the program grows. Each knob is
plotted with the other held at its middle value. Averaging across the held knob
would mix a run abandoned at the cap into a mean and quietly turn a bound into a
number.

#todo[
  Not yet measured. Run #raw("experiments/02_rust_corpus.py --with-silicon
  --only") over the twelve #raw("depth_d*") files into the current sweep
  directory, then #raw("experiments/10_report_perf.py"), which emits the plot and
  the grid as soon as the rows are there.
]

==== Variants and payload depth <sec:results-perf-enum>
The #raw("enum_vN_pD") grid varies an enum's variant count against its payload
nesting depth, and exists to locate the point at which Helium stops winning. The
two knobs are expected to behave differently, and the difference rather than
either curve is the finding.

#todo[
  Not yet measured, on the same terms as @sec:results-perf-depth.
]

#todo[
  Write the three findings the two families are for, once the plots are in front
  of you: whether the depth advantage is constant or growing, where the enum
  crossover is, and whether the grid predicts the weakest file of
  @tbl:perf-rust from its coordinates alone. The prediction should be stated and
  confirmed rather than asserted. The limit at the top of the enum grid, any
  member Helium rejects and Silicon verifies, belongs here, named, with the
  obligation it fails.
]
