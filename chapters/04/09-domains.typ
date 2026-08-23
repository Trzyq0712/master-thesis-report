#import "../../macros.typ": *

== Domains <sec:impl-domains>

A domain is a set of uninterpreted functions and the axioms relating them.
Prusti uses domains heavily and for one purpose: one per primitive Rust type,
and the guiding example declares one in @lst:example-viper.

A domain introduces no new kind of instruction. What it contributes is rules —
facts merged into the state that the ladder of @sec:impl-proving runs
underneath every tier.

A domain declaration flattens. Its functions become ordinary
function declarations and its axioms become top-level axioms; the domain itself
survives only as a type.

#lowering(caption: [A domain flattens into functions, a type, and axioms. The
  axiom is simplified to a single instance — the real #vi[`i32_ax_cons`] is
  quantified over every #vi[`i32`], and quantifiers are the next section's
  subject.], label: "lst:domain")[```viper
domain i32 {
  function i32_cons(arg0: Int): i32
  function i32_value(arg0: i32): Int

  axiom i32_ax_cons {
    i32_value(i32_cons(0)) == 0
  }
}
```][```vmir
domain i32

function i32_cons(e0: Int) -> i32
function i32_value(e0: i32) -> Int

axiom i32_ax_cons {
  e0: i32 := i32_cons(0)
  e1: Int := i32_value(e0)
  e2: Bool := e1 == 0
  result: e2
}
```]

An axiom's body is ordinary pure VMIR, and executing it is the same walk as any
other body: each instruction adds its term, and the result is merged with
#vm[`true`]. Axioms are made available up front, before the unit being verified is
walked, and they are _trusted_ — no obligation is checked on an axiom body, not
even division by zero, since an axiom is an assumption about the model rather than
a claim to be discharged.

Nothing about this is heap-dependent, and nothing about it needs quantifiers.
A closed axiom without a #vi[`forall`] is simply a fact merged into the state at
the start. A quantified one is a single value — the #vm[`forall`] on the axiom's first
line — and instantiating it is the next section's subject.
