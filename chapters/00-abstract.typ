#import "../generated/perf-rust-scalars.typ": *
#import "../generated/perf-viper-scalars.typ": *

#pad(x: 10%, y: 8%)[
  Viper verification backends, like Silicon, are built to handle a wide range of
  obligations, making their implementation complex. Because of this they rarely
  optimise for the common cases. Many of the proof obligations are can be
  discharged with simple equality reasoning, avoiding reaching for a general-purpose
  SMT solver.

  This thesis proposes VMIR, a mid-level intermediate representation that
  decomposes Viper into a small set of explicit primitives and promotes
  better proof reuse, and Helium, a verifier
  for VMIR whose only reasoning engine is equality saturation over e-graphs.
  Together the system achieves a speedup of up to around 100#sym.times
  over Silicon on simple straight-line code, and around 15#sym.times average on
  specificationless Prusti-encoded Rust programs.
]
