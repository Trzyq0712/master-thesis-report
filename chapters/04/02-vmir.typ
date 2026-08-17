#import "../../macros.typ": *

== VMIR at a Glance <sec:impl-vmir>

The verifier does not execute Viper. It executes _VMIR_, the intermediate
representation of @sec:approach, and every construct of @lst:example-viper
reaches the verifier only through a lowering. The case for having an IR at all is
made there and not repeated here: a smaller language means each verifier rule is
written once, and the shapes that matter to the design are explicit in the
instruction rather than recovered from syntax. What this section adds is how VMIR
_reads_, so that the listings of the sections after it need no preamble of their
own. It is deliberately partial — each construct arrives with the piece of VMIR
it needs.

#para[What the frontend settles first] Lowering does not start from source text. It
starts from a typed abstract syntax tree, and the resolution that produces one is
the same Silver @viper @silver performs: the surface language's ambiguities are
settled before VMIR is in question. Every intermediate expression carries the type it was
inferred to have, and the values Viper lets a program leave implicit — the amount
in an #vi[`acc(x.f)`] written without one, which is #vi[`write`] — have been
filled in. The translator therefore lowers a program in which nothing remains to
be inferred, and no lowering rule has to recover what a piece of syntax meant.

#para[Flat and named] VMIR is in static single assignment form, and expressions
are flattened: every operation is an instruction of its own, its operands are
temporaries rather than expressions, and its result is a fresh temporary with the
type written out.

#lowering(caption: [Nesting is flattened and every intermediate value is named.], label: "lst:vmir-glance")[```viper
var x: Int
var y: Int := (x + 1) * 2
assert y > 0 || x < 0
```][```vmir
e0: Int := fresh
e1: Int := e0 + 1
e2: Int := e1 * 2
e3: Bool := e2 > 0
e4: Bool := e0 < 0
e5: Bool := e3 ? true : e4
assert e5
```]

Two things in that listing are worth naming. A declaration without an initialiser
is a #vm[`fresh`] value and no more: nothing is assumed about it, and there is no
store mapping #vi[`x`] to anything, only the temporary the name was lowered to.
And the disjunction has become a conditional. VMIR has no negation, conjunction or
disjunction of its own: the only boolean connective it has is the ternary
#vm[`c ? a : b`], and the other three are written in terms of it — #vi[`!b`]
becomes #vm[`b ? false : true`], #vi[`a && b`] becomes #vm[`a ? b : false`], and
the #vi[`||`] of the listing above is #vm[`e3 ? true : e4`]. One rule then covers
what would otherwise need several. That
is the shape of every desugaring in the chapter — a surface form is replaced by
the one primitive that already had to exist.

#para[A textual representation] VMIR is a language with a syntax rather than an
internal data structure, and the listings in this chapter are written in it. That
was a secondary goal rather than a consequence: a program can be printed after
lowering, read back, diffed against an expected form, and handed to something
other than the verifier this thesis builds. A lowering is then testable on its own
terms, and an alternative backend over the same IR — one that discharges the
obligations a different way — needs no part of what follows.
