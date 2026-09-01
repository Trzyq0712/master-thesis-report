#import "../../macros.typ": *
#import "../../generated/perf-validity.typ": *
#import "../../generated/perf-rust-scalars.typ": *
#import "../../generated/perf-viper-scalars.typ": *

== Performance Evaluation <sec:results-perf>

In @sec:approach we argued that the proof obligations Prusti's encoder produces are mostly
equality problems, and that the cost an SMT-based backend pays on them is a
consequence of the backend rather than of the obligation. This section measures
that claim against Silicon, on two corpora with different provenance.

For the measurements to be meaningful, one needs to ensure that the verifier exhibits
no unsoundness. To ensure that, we have first checked that Helium does not discharge
obligations vacuously. To ensure that we have inserted #vm[`assert false`] at various
program points, where we expect the program to be in a consistent state. Had
Helium still verified the program, any measurements below would have been meaningless,
as Helium would be discharging obligations via inconsistency.

Additionally, we only constrain the set of programs to those that both verifiers are
able to verify. Concretely, we follow the limitations of Helium established in
@sec:results-features both in terms of constructs and obligation difficulty.

=== Hand-written Viper benchmark <sec:results-perf-viper>

In the first set of benchmarks, we compare Helium against Silicon on a corpus
of hand-written Viper programs. The goal is to measure the performance of Helium
on idiomatic Viper programs, free of the artifacts of Viper frontends encoders.

The benchmark tests various components of idiomatic Viper programs:
recursive predicates over linked structures
and over trees, predicates layered on one another, domains carrying axioms about
their own operations, algebraic datatypes, pure functions with postconditions a
caller reads, loops whose invariants are permissions, and ownership moved across
method boundaries. There are #viper-files of them, #viper-members members in
all, and they are listed in @tbl:perf-viper.

The programs, what each contains, and the obligations they raise are summarized in
@sec:appendix-benchmarks-viper, in the order of @tbl:perf-viper, which gathers
the programs by the construct each is built around.

#include "../../generated/perf-viper-table.typ"

Helium takes #viper-ours over the whole corpus against Silicon's
#viper-silicon, a ratio of #viper-ratio-total, and the geometric mean of the
per-program ratios is #viper-ratio-geo.

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
class these numbers are about.

The corpus measured here is #rust-files files and #rust-members members, each of
them Prusti's encoding of a hand-written Rust program.
The sources carry no specifications, so the obligations are the ones Prusti's
type predicates impose. Each program was written to put one shape of those
obligations under load, and they are summarized in @sec:appendix-benchmarks-rust,
in the order of @tbl:perf-rust, which gathers the files by the pattern each exercises.

#include "../../generated/perf-rust-table.typ"

Over those #rust-files files Helium takes #rust-ours against Silicon's
#rust-silicon, a ratio of #rust-ratio-total, with a geometric mean over the
per-file ratios of #rust-ratio-geo.


=== Performance analysis

This wide variance strongly correlates with the presence of branching control flow. Programs that consist largely of straight-line code or sequential shallow blocks, such as #raw("mat3_mul"), #raw("color_blend"), and #raw("aabb_collide"), exhibit massive speedups ranging from 40#sym.times to over 100#sym.times. In these cases, Helium's e-graph saturation efficiently accumulates arithmetic facts and permissions without the path-exploration overhead typical of symbolic execution engines like Silicon.

Conversely, programs characterized by extensive branching and state manipulation, such as #raw("shape_area"), see their speedups drop to 2.5#sym.times. If we examine what dominates the verification time for #raw("shape_area"), we find that the effort is dominated by exactly two members, which account for about 92% of the total verification time:

#figure(
  caption: [Verification time breakdown for the #raw("shape_area") program.],
  table(
    columns: 2,
    align: (left, right),
    stroke: none,
    table.header([*Method*], [*Time*]),
    table.hline(stroke: 0.5pt + luma(88%)),
    raw("m_shape_translate"), [3.557s],
    raw("m_shape_grow"), [3.427s],
    [Other members], [0.626s],
    table.hline(stroke: 0.5pt + luma(88%)),
    [*Total*], [*7.610s*],
  )
) <tbl:shape-area-times>

Both of these Viper methods encode very similar Rust methods that mutate an enum through a mutable reference (#ru[`&mut`]). The core difficulty arises from properly tracking and exhaling permissions when joining from branches. When mutating through a match statement, a permission chunk is borrowed, mutated, and then given back on each arm. Helium must relate the given-out and returned heap chunks to each other to reconstruct the full permission. Because the returned chunk is added under the path condition of its respective arm, it does not occupy the same location in the heap representation as the original unconditional chunk. Figuring out that the permission was indeed given back, and reconciling these distinct chunks at the control-flow merge point, is the non-trivial and highly computationally expensive part of the verification process. We will investigate the mechanics of why this pattern is particularly slow in @sec:results-attribution.
