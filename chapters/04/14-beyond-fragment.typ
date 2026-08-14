#import "../../macros.typ": *

== Beyond the Fragment <sec:beyond-fragment>

The chapter has described what the verifier does. This section is about what it
does not, and the point of it is that the list splits in two. Some of Viper is
absent because @sec:prusti-needs found it absent from the target — a scoping
decision, and one this chapter is organised against. The rest is absent because it
is not finished, and those are gaps. Running the two together would be
misleading in both directions.

#para[Out of scope] Nothing in the following appears anywhere in the 22 encodings
of the corpus, and none of it is supported.

Magic wands are the largest. Quantified permissions are the next — with no
#vi[`forall x :: acc(..)`] there is no way to describe the footprint of an
array, which is the one place @sec:impl-loops's non-goals and this list meet.
#vi[`forperm`] and #vi[`exists`] follow them. The collection types —
#vi[`Seq`], #vi[`Set`], #vi[`Multiset`], #vi[`Map`] — have no encoding, which is
possible only because Prusti's snapshots are #vi[`adt`]s rather than sequences.
#vi[`new(*)`] is rejected in favour of the enumerated form. And #vi[`while`] is
never emitted, which is a statement about the frontend rather than about the
verifier — loops are supported anyway (@sec:impl-loops).

Every one of these is rejected _loudly_, by the type-checker or the translator,
with the construct named. There is no path on which an unsupported construct is
quietly ignored and a program is reported as verified on the strength of a
fragment of itself. That is the property that makes the scoping a decision rather
than a hazard, and it is worth stating plainly because the alternative failure
mode is the one that would matter.

Two constructs on the corpus's never-appears list are supported regardless, and
they are cheap for the same reason: fractional permission literals and the
#vi[`perm`] expression both fall out of amounts being terms
(#pararef(<para:impl-amounts>, [Permission amounts])) rather than needing a
mechanism of their own. A frontend other than Prusti would find them working.

#para[Genuine gaps] The list of things that ought to work and do not is shorter
and more specific.

The first dominates the others: there is no decision procedure for linear
arithmetic. An obligation of the form $0 <= i and i <= n, i < n |- i + 1 <= n$ is
not discharged, and it is not an exotic shape — it is the standard invariant of a
counting loop. Every case in the loop corpus that Silicon verifies and this
verifier does not fails on exactly it (@sec:impl-loops), and the failures have
nothing to do with loops: the same obligation fails with no loop in the program.
The e-graph has arithmetic _identities_ — cancellation, units, folding of
literals — and identities do not decide an inequality between symbolic terms.

The second is the pair of inverse directions on datatypes (@sec:impl-adts):
recovering a constructor from a discriminator value, and concluding the last
variant from having ruled out the others. Both are missing facts rather than
missing machinery, and the section says what stating them would take.

Third, an irreducible control-flow graph — a cycle with more than one entry — has
no natural loop and is rejected. This is a real restriction, though not one any
frontend the author is aware of produces.

Finally two smaller ones, recorded because they are the kind that is easy to lose.
A multi-target assignment is rejected rather than lowered. And #vi[`unfolding`],
being an expression that lowers to statement-level heap instructions, is the one
operation that can sit under a path condition finer than its block's
(@sec:impl-predicates); the effect is scoped and fabricates no permission, so this
is a wrinkle in an invariant rather than an unsoundness, but it is the one place
the block model is not literally true of the instruction stream.

#para[Complete state, incomplete procedure] The sections above each ended by
saying what the verifier records when it cannot prove something, and the reason to
have said it every time is that the property only means anything if it holds
everywhere. Stated once, in full:

_When the verifier fails to discharge an obligation, it has failed to prove
something, not lost the ability to prove it._ The symbolic state at the point of
failure is a complete and faithful description of the program point: the chunk is
in its partition with its permission as a term rather than an approximation; the
path condition is the exact cube, minimised only by a law that preserves its
value; the values are the terms the program built, related by every equality that
was established and by none that was not; and the goal is an e-class in that same
state. Nothing was widened, dropped, or replaced by a symbol standing for what
could not be represented.

The consequence is the one that matters for what comes next. An obligation this
verifier cannot close is not a dead end but a handover point: the same state and
the same goal can be given to a procedure that reasons about rationals, or about
datatypes, or about anything else — and the arithmetic gap above is precisely a
case where that would work. Incompleteness that is confined to the decision
procedure is a boundary that can be moved. Incompleteness in the record would not
be.
