#import "../macros.typ": *

== Benchmarks <sec:appendix-benchmarks>

=== Hand-written Viper <sec:appendix-benchmarks-viper>
The programs below are the hand-written Viper corpus of @sec:results-quantitative. @tbl:perf-viper-categories aggregates them by construct.

/ #raw("adt_expr"): An expression language as an algebraic datatype, with a
  second datatype for its values. The obligations are constructor injectivity,
  discriminant exclusivity and the destructor equations.
/ #raw("branch_paths"): Conditionals and their joins, from one join over two arms
  up to four independent guards with sixteen paths. The obligations are the
  equation each guard supplies and the state a join receives from both arms.
/ #raw("dispatch_tags"): One branch point with many arms, which is the shape a
  #ru[`match`] takes once Prusti has encoded it. Arms are driven by a
  discriminant and by an integer field, and the two forms nest, so the cost
  reads as the cost of the split itself.
/ #raw("branch_perms"): Permission crossing a branch rather than control flow
  crossing one, over locations written on one arm, on both, or on neither. It
  fixes the branch and varies the heap, which is the counterpart to
  #raw("branch_paths").
/ #raw("goto_jumps"): Forward jumps over a reducible control-flow graph, together
  with a back edge built from #vi[`goto`] rather than #vi[`while`]. The
  obligations are those of the joins these jumps create.
/ #raw("label_snapshots"): #vi[`label`] and #vi[`old[l]`], with the control flow
  between the label and the read varying over a branch, a loop and a call. Every
  read sits in a body, since Helium rejects #vi[`old[l]`] in a postcondition.
/ #raw("loop_exits"): Loop shape rather than loop framing, over nesting, loops in
  sequence, a peeled iteration and exits through a label. The invariant is held
  fixed so that the cost is attributable to the shape.
/ #raw("domain_axioms"): Pairs, an option and an abstract ordering given only by
  axioms. The obligations are congruence and axiom instantiation, and every
  quantifier carries a trigger the author wrote.
/ #raw("state_machine"): A protocol whose states are an abstract domain and whose
  transitions are axioms, with the object guarded by a predicate. Fold and unfold
  traffic therefore mixes with axiom instantiation.
/ #raw("frame_records"): A multi-field record held through field permissions.
  The obligations are framing and permission arithmetic, since the work is
  carrying an unmentioned field across a call and splitting a fraction to put it
  back.
/ #raw("perm_transfer"): #vi[`inhale`] and #vi[`exhale`] written as the program
  rather than as a method contract. Locations are taken and returned whole, in
  halves, under a guard, and around a call.
/ #raw("giveback_join"): A location lent inside a branch arm and handed back at
  an address that equals the original only under that arm's guard, so the release
  after the merge recombines two chunks instead of looking one up. This is
  Prusti's #ru[`&mut`] reborrow inside a #ru[`match`] written directly, and it is
  the only file here that reaches the recovery @sec:results-discussion measures.
/ #raw("transfer"): Ownership passed across method boundaries, with a predicate
  standing for the right to touch an account. The obligations are that two
  accounts are distinct and that touching one left the other alone.
/ #raw("pure_functions"): Recursion, mutual recursion, and postconditions a
  caller reads without unfolding the body. Every clause is an equality or a
  disequality, which keeps the arithmetic gap of @sec:results-qualitative out of
  the measurement.
/ #raw("pure_eval"): Obligations with no heap in them, over destructor equations,
  injectivity, exclusivity and domain axioms at their own triggers.
  #raw("pure_functions") recurses over the heap, and this one removes it.
/ #raw("loop_frames"): Invariants that are permissions and equalities rather than
  arithmetic facts, carried around the back edge. It fixes the loop shape and
  varies the invariant, which is the counterpart to #raw("loop_exits").
/ #raw("nested_predicates"): Predicates layered over one another rather than
  recursing, with an abstract predicate at the bottom. The obligations are the
  permissions each layer holds and the ones an abstract predicate refuses to
  reveal.
/ #raw("list_deep"): A singly linked list under a recursive predicate, with every
  method reaching a fixed depth. Each pays for a chain of unfolds and the
  matching chain of folds, so the obligations are the fold conditions at every
  link.
/ #raw("tree_shape"): A binary tree, whose predicate recurses twice. Unfolding a
  node opens two obligations and the closing fold re-establishes both, which
  doubles the fold traffic of #raw("list_deep") at each level.



=== Prusti-generated benchmarks <sec:appendix-benchmarks-rust>
The files below are the Prusti-generated corpus of @sec:results-quantitative. @tbl:perf-rust-categories aggregates them by pattern.

/ #raw("aabb_collide"): Axis-aligned box tests written as #ru[`if`] and
  #ru[`else`] nested three to five levels deep, with no early return. An inner
  block's path condition is a strict superset of its dominator's, which puts a
  long path condition under load.
/ #raw("color_blend"): Colour blending and clamping written as explicit branch
  chains rather than library calls. A body accumulates many small joins, so each
  path condition is short and the block count per body is high.
/ #raw("state_machine"): A state enum and an event enum matched against each
  other, so a nested #ru[`match`] produces a grid of arms. Many sibling path
  conditions die at the join under the one their shared dominator carries.
/ #raw("vec3_math"): Integer vector algebra in which every operation is built
  from calls to the smaller ones. A single block accumulates many call
  obligations, each a fold and unfold plus a snapshot round trip, with almost no
  branching.
/ #raw("shape_area"): An enum whose variants carry nested structs. Each arm
  unfolds a payload predicate before touching its fields, which is the arm-local
  fold and unfold traffic that makes a block's held permission
  branch-structured.
/ #raw("bank_transfer"): Two #ru[`&mut`] accounts live in one call, with guarded
  debits, credits and swaps. A block's held permission becomes
  branch-structured, so a consumption must be proven against a sum rather than
  against a single chunk.
/ #raw("borrow_fields"): Structs that hold borrows rather than take them as
  parameters, so Prusti's reference predicate nests inside another type
  predicate. Folding the struct draws that permission in and unfolding returns
  it.
/ #raw("physics_step"): A world of three bodies stepped through integrate, clamp
  and bounce, each stage built from smaller helpers. A caller's block inherits
  obligations from several callees, so the ground graph carries a great deal
  before any block raises its proof.
/ #raw("inventory"): Hand-rolled #ru[`Maybe`] and #ru[`Res`] enums, so error
  paths are ordinary enum arms. A block's path condition is a discriminant fact
  and its body then reads the payload, which is where tag knowledge and framing
  meet.
/ #raw("classify_tuple"): A fixed-arity eight-field buffer classified element by
  element through a match cascade. Bodies have a high block count where every
  path condition is short, which is the opposite extreme from
  #raw("aabb_collide").
/ #raw("mat3_mul"): Unrolled #ru[`3x3`] integer linear algebra. Every body is one
  long straight-line block, so the file measures how much a single block
  accumulates before an obligation is raised.

=== Measurements <sec:appendix-benchmarks-tables>
@tbl:perf-viper gives the measurement for each hand-written program and
@tbl:perf-rust for each Prusti-generated file, in the order the descriptions
above take.

#include "../generated/perf-viper-table.typ"

#include "../generated/perf-rust-table.typ"
