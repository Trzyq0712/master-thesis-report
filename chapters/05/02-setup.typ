#import "../../macros.typ": *
#import "../../generated/setup.typ": *

== Experimental Setup <sec:results-setup>
The rest of this chapter reports times, and a time is only a result if the
machine, the toolchain and the protocol behind it are fixed. This section states
them once. @tbl:results-setup gives the pinned toolchain and the machine; the
prose that follows states the protocol the sweep ran under and explains the
parts of it that are load-bearing. The verdicts of @sec:results-features were
taken from the same toolchain, but they do not depend on the timing protocol,
which is why they come first.

The corpora, the runners and the generators live in a separate repository,
which pins Helium, the Prusti fork whose encoder produces the Viper we measure,
and ViperServer as recursive submodules. Pinning ViperServer fixes Silicon and
Silver with it. A sweep appends one row per suite, case, member, tool and
repetition to a single file, and every table and figure in this chapter is
generated from it. No number below is typed by hand.

#include "../../generated/setup-table.typ"

Both verifiers run single-threaded. Helium runs as a fresh process per file,
timed on the wall clock, and the reported number is the minimum of three
repetitions: every source of noise on this machine adds time and none removes
it. Silicon runs inside one long-lived ViperServer over HTTP with
#raw("--numberOfParallelVerifiers 1") and #raw("-Xss512m -Xmx4g"), and the
number taken is the server's own overall time rather than the client's round
trip. A run that exceeds 400 seconds is abandoned. A sweep refuses to start
above a one-minute load average of 1.5.

Prusti ships a Z3 of its own, so a Prusti user
runs Silicon against a solver several years older than the one above. We
give Silicon the newer one, on the principle that a comparison should not be won
by handicapping the incumbent. The choice is a trap for a harness rather than
for a user: Silicon ignores the #raw("Z3_EXE") environment variable when it is
driven through ViperServer and falls back to whatever #raw("z3") is on the path,
so the solver has to be named in the verification argument. The harness records
the binary it named alongside the version that binary reported.

#todo[
  *The spot check this paragraph needs.* Re-measure two or three corpus files
  with the Z3 that Prusti ships and report the direction and size of the
  difference. Without it the claim that the newer solver is the conservative
  choice is an assumption, and a reader is entitled to see it as one. The
  harness takes #raw("HELIUM_EVAL_Z3") for exactly this, and the check needs a
  Prusti build, which the pinned submodule does not yet have.
]

Three details of the Silicon side are load-bearing rather than incidental, and each
was found by a sweep that produced wrong numbers without it. First, a
ViperServer is cold when it starts and inflates its first file several-fold, so
the harness warms it on a file that is never timed and re-warms it after any
restart. Second, the server caches by entity, so the harness confirms that every
entity came back uncached and refuses to record a cache hit as a measurement.
Third, ViperServer's HTTP frontend never releases an abstract-syntax-tree job
slot, so a long sweep silently starts answering with an invalid job identifier
and files that never ran are recorded as timeouts. The harness counts jobs
against a budget of 256 and recycles the server before it runs dry.

Helium is given no equivalent handling, because it needs none: it runs as a
fresh process per file and is timed on the wall clock. Comparing a cold Helium
process against a warm server is the conservative direction, and it is the
direction taken. The number taken from Silicon is the server's own overall time
rather than the client's round trip.

A run abandoned at the cap is recorded as censored. A censored value is a lower
bound, and
every aggregate that includes one inherits the bound, so a total that touches a
capped row is printed with a #sym.gt and a ratio derived from it is a bound
rather than a measurement.

Silicon varies between 5% and 20% from run to run on this corpus and Helium
about 5%, which is what the repetitions and the load-average check are for. A
ratio between #noise-band-low and #noise-band is therefore reported as
indistinguishable rather than as a win or a loss. Where a claim can be made in
terms of the counters Helium records for itself — obligations, rewrite-rule
applications, e-graph size — we make it there instead: those counters are exact,
and Helium's own regression tests hold them as snapshots.
