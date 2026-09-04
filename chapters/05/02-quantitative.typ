#import "../../macros.typ": *
#import "../../generated/setup.typ": *
#import "../../generated/perf-validity.typ": *
#import "../../generated/perf-rust-scalars.typ": *
#import "../../generated/perf-viper-scalars.typ": *
#import "../../generated/attribution-scalars.typ": attr-split-named-share

== Quantitative Evaluation <sec:results-quantitative>
Helium rests on the premise that the proof obligations a frontend such as Prusti
generates are predominantly equality problems, and that the cost an SMT-based
backend pays on them derives from the backend rather than from the obligation.
This section measures that premise against Silicon on
two corpora of different provenance: hand-written Viper, and the output of
Prusti's encoder on Rust programs that carry no specifications. Both corpora are
restricted to programs both verifiers accept, following the boundary
@sec:results-qualitative establishes for constructs and for the difficulty of an
obligation.

@tbl:results-setup records the pinned toolchain and the machine. Both verifiers
run single-threaded. Helium is invoked as a fresh
process per file and its time is that process's wall clock, taken as the minimum
of #helium-reps runs. Silicon runs inside a ViperServer instance (#java-opts,
#raw("--numberOfParallelVerifiers 1")) with entity caching disabled, warmed on a
file outside the timed set for #warmup-runs runs. Its time is the server's own
overall verification time.

#include "../../generated/setup-table.typ"

#para[Validity] Two things establish the soundness of the measurements. The first
is agreement: both verifiers accept every file of both corpora, and their verdicts
coincide on every declaration, #rust-declarations of them over the
Prusti-generated corpus and #viper-declarations over the hand-written one. No
program was verified by one tool and rejected by the other. The second check is
for vacuity. We injected an #vi[`assert false`] into each method body at
independent positions, at both of which the
program is expected to be in a consistent state. Every one of the #rust-bodies
bodies of the Prusti-generated corpus and the #viper-bodies bodies of the
hand-written corpus was rejected at both positions, so no measurement below comes
from a state that had already become inconsistent.

#para[Hand-written Viper] The first corpus is #viper-files idiomatic Viper
programs written for this evaluation, #viper-members declarations in all, free of
the artifacts a frontend's encoder introduces. Between them they exercise
recursive predicates over linked structures and over trees, predicates layered on
one another, domains carrying axioms about their own operations, algebraic
datatypes, pure functions whose postconditions a caller reads, loops whose
invariants are permissions, and ownership moved across method boundaries.
@tbl:perf-viper-categories gathers them by the construct each is built around,
and @sec:appendix-benchmarks-viper describes each program and gives the same
measurements per file.

#include "../../generated/perf-viper-categories.typ"

Helium takes #viper-ours over the whole corpus against Silicon's #viper-silicon,
a ratio of #viper-ratio-total, with a geometric mean over the per-program ratios
of #viper-ratio-geo. The best result is #viper-best at #viper-best-ratio, an
expression language written as an algebraic datatype, whose obligations are
constructor injectivity, discriminant exclusivity and the destructor equations.
The worst is #viper-worst at #viper-worst-ratio, a singly linked list under a
recursive predicate in which every method pays for a chain of unfolds and the
matching chain of folds.

#para[Prusti-generated Rust] The second corpus is Prusti's own output for Rust
programs that carry no specifications: #rust-files files, #rust-members
declarations, each the encoding of one hand-written Rust program. Because the
sources specify nothing, every obligation originates in the type predicates
Prusti imposes, and the corpus therefore consists of framing, fold and unfold,
and discriminant well-formedness obligations rather than hand-written functional
specifications. Each program places one shape of those obligations under load.
@tbl:perf-rust-categories gathers the files by that shape, and
@sec:appendix-benchmarks-rust describes each file and gives the per-file
measurements.

#include "../../generated/perf-rust-categories.typ"

Over the corpus Helium takes #rust-ours against Silicon's #rust-silicon, a ratio
of #rust-ratio-total, with a geometric mean over the per-file ratios of
#rust-ratio-geo. The per-file ratios span more than an order of magnitude. The
variation tracks how much permission the encoding moves across a branch, and
straight-line and sequential shallow-block code sits at the top of the
range. #rust-best, at #rust-best-ratio, encodes a matrix multiplication as one
long block of heap operations and snapshot arithmetic with almost no branching,
so it isolates each backend's per-obligation cost from the cost of control flow.

One result runs the other way. #rust-worst, at #rust-worst-ratio, is the weakest
in the corpus, and its cost is concentrated rather than spread: two of its members account for
#attr-split-named-share of Helium's time on the file, and both encode a Rust
method that mutates an enum through a mutable reference inside a #ru[`match`].
@sec:results-discussion derives what that shape costs from the encoding, and
separates the contribution of branching from that of the permissions crossing
it.
