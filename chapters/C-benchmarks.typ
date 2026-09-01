#import "../macros.typ": *

= Benchmark Descriptions <sec:appendix-benchmarks>

== Hand-written Viper <sec:appendix-benchmarks-viper>

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

== Prusti-generated benchmark <sec:appendix-benchmarks-rust>

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
