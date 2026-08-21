#import "../../macros.typ": *

== VMIR: The Intermediate IR <sec:impl-vmir>

The verifier does not execute Viper. It executes _VMIR_, the intermediate
representation of @sec:vmir-design, and every construct of @lst:example-viper
reaches the verifier only through a lowering. What this section adds is how VMIR _reads_, so
that the listings of the sections after it need no preamble of their own. It is
deliberately partial — each construct arrives with the piece of VMIR it needs.

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
type written out. @lst:vmir-glance is two fragments of the guiding example: the
comparison that decides #vi[`account_deposit`]'s branch, and the variant-range
disjunction out of #vi[`own_Transaction`] (@lst:example-viper), with the repeated
discriminant read abbreviated to #vi[`d`].

#lowering(caption: [Nesting is flattened and every intermediate value is named.], label: "lst:vmir-glance")[```viper
var _tmp0: i32
var d: isize

var b: bool :=
  lt_i32_i32(
    i32_cons(0), _tmp0)

assert d == isize_cons(0) ||
       d == isize_cons(1)
```][```vmir
e0: i32 := fresh
e1: isize := fresh

e2: i32 := i32_cons(0)
e3: bool :=
  lt_i32_i32(e2, e0)

e4: isize := isize_cons(0)
e5: Bool := e1 == e4
e6: isize := isize_cons(1)
e7: Bool := e1 == e6
e8: Bool := e5 ? true : e7
assert e8
```]

Two things in that listing are worth naming. A declaration without an initialiser
is a #vm[`fresh`] value and no more: nothing is assumed about it, and there is no
store mapping #vi[`_tmp0`] to anything, only the temporary the name was lowered
to. The declaration _with_ an initialiser produces no instruction of its own
either — #vi[`b`] is a name for the class #vm[`e3`] landed in, and an assignment to
a source variable rebinds the name rather than building anything.

And the disjunction has become a conditional. VMIR has no negation, conjunction or
disjunction of its own: the only boolean connective it has is the ternary
#vm[`c ? a : b`], and the other three are written in terms of it — #vi[`!b`]
becomes #vm[`b ? false : true`], #vi[`a && b`] becomes #vm[`a ? b : false`], and
the #vi[`||`] above becomes #vm[`e5 ? true : e7`]. One rule
then covers what would otherwise need several. That is the shape of every
desugaring in the chapter — a surface form is replaced by the one primitive that
already had to exist.

#para[A textual representation] VMIR is a language with a syntax rather than just an
internal data structure, and the listings in this chapter are written in it. That
was a secondary goal rather than a consequence: a program can be printed after
lowering, read back, diffed against an expected form, and handed to something
other than the verifier this thesis builds. A lowering is then testable on its own
terms, and an alternative backend over the same IR — one that discharges the
obligations a different way — needs no part of what follows.

#para[VMIR-lite] The real form spells out mechanical detail that a listing does
not always need to carry. A listing tagged _VMIR-lite_ in its corner drops that
detail, so what is left is what the snippet is about. It is the same language,
and it agrees with the real form wherever the point being made lives. A listing
tagged plain VMIR is what the verifier would actually be given.
