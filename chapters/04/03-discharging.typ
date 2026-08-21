#import "../../macros.typ": *
#import "../../figures/prove-ladder.typ": prove-ladder

== Discharging Obligations <sec:impl-proving>

Every instruction of the preceding section either produced a value, updated the
state, or raised an obligation, and the obligations were discharged only
non-specifically. This section describes the mechanism precisely.

#para[The tiers] <para:impl-tiers> An obligation is a goal e-class and an optional
path condition — an obligation raised where nothing is assumed carries none, and
the tiers that exist to handle a condition have nothing to do on it — and the
verifier answers it by escalating through named tiers, cheapest first. Each tier is strictly more work than the last, so the ordering is the
design: an obligation should cost what it takes to answer it and not what it would
take to answer the hardest one. Where the obligations of a real program actually
stop is a measurement, and @sec:results is where it is made.

#figure(
  prove-ladder,
  caption: [The prove ladder. Each arrow is a tier failing to answer: a tier that
    does answer discharges the obligation and the search stops there.
    #vm[`probe`] answers nothing itself — it copies the graph, fixes the cube in
    the copy and saturates it, after which the same cheap questions are put to
    that copy, with #vm[`ite_decompose`] the last resort on it. The dashed edge is
    an obligation with nothing to assume: #vm[`probe`] would change nothing, so
    the copy's cheap questions are skipped with it.],
) <fig:tiers>

#para[#vm[`inconsistent`]] Asks, on a best-effort basis, whether the state
contains a contradiction: not every inconsistency the graph implies is found, but
every one reported is real. It comes first because a contradictory state proves
everything, making all work below it redundant — and it is cheap because a
contradiction is recorded as it happens rather than searched for, so asking is two
comparisons of class identifiers.

#para[#vm[`goal_true`]] Asks whether the goal holds on its own, before the
implication $"pc" => "goal"$ is built. Building that implication inserts
permanent nodes; an obligation with no path condition, settled by constant
folding the moment it is raised, should not pay for a term nothing ever reads
again.

#para[#vm[`imp_true`]] Builds the implication and asks whether _it_ is
#vm[`true`]. Nothing is cached: discharging an obligation merges its implication
with #vm[`true`] like any other fact of the graph. The tier pays off on
repetition — a Prusti encoding raises the same framing obligation at each
statement of a run that holds the same permission (@sec:prusti-needs), and later
occurrences are answered here for the price of a comparison.

#para[#vm[`saturate`]] Runs the rewrite rules to a fixpoint and asks again. It is
the first tier that does work rather than a lookup, and it sits above the copying
tier because that work is not thrown away: saturation runs on the live graph, so
every equality it derives stays for every later obligation. The rules
(#pararef(<para:impl-rewrites>, [The rewrites])) are identities, so this tier
answers obligations true by rewriting rather than reasoning — a boolean connective
collapsing to the condition it was built from, an assumed equality carried into
congruence — none of which needs a path condition.

#para[#vm[`probe`]] Assumes the path condition. A cube's literals hold on one
path only, so they cannot be merged into the live graph without the verifier
believing them everywhere; instead the graph is copied, the literals fixed in the
copy, and the copy saturated. Inside a method body the copy is not per
obligation: a block's cube is static, so one scratch graph serves every
obligation the block raises (@sec:impl-cfg). The tier earns its cost by what
would otherwise be unprovable — a guarded division, or any obligation raised
under a condition the program itself wrote — rather than by how often it fires.

An obligation with an empty path condition, or whose literals the live graph
already knows at the polarity the cube wants, passes this tier for free — the
copy's cheap questions cannot answer differently from the live graph's — and
drops straight to the last tier.

#para[#vm[`ite_decompose`]] The last tier, and the narrowest by design. VMIR spells
$c => e$ as $ternary(c, e, "true")$ (@sec:impl-vmir), so a goal with a #vm[`true`]
arm is an implication written as a conditional; the tier reads it back as one —
assume $c$, re-check $e$, telescoping a chain of nested implications one
assumption at a time. Its conditions are _read off the goal_ rather than searched
for, which bounds it and separates it from a case split. It works whichever arm
carries #vm[`true`] — the antecedent it assumes just changes polarity — so it
covers an obligation the program wrote as an implication without needing to tell
the two shapes apart, and no tier above can do anything with a conditional as it
stands.

#para[Constant folding] Underneath every tier is one rule set, always on.
Congruence and hash-consing come from the e-graph itself; the rest is an analysis
and a set of rewrites.

The analysis is constant folding, attached to every e-class. A class whose term
evaluates to a literal carries that literal, and it propagates upwards: the
operators fold when both operands are known, an integer cast folds a known
integer, and a conditional whose condition is known takes on the data of the arm
that condition selects. One case does more than evaluate: a class forced to carry
two different literals is a contradiction, which is what the first tier looks
for.

#para[The rewrites] <para:impl-rewrites> The rules that fire during saturation are
identities rather than a theory, and deliberately incomplete: an "explosive" rule
that grows the graph — one whose right-hand side names a term the left-hand side
did not already mention — is excluded on principle, no matter how useful, because
its cost is paid by every saturation from then on and not just the obligations it
helps. Almost every rule below is instead a _subset_ rewrite: the right-hand side
spells out nodes the left-hand side's e-class already contains, so applying it
adds no e-node, only a union. @fig:rewrites lists them.

#figure(
  caption: [The rewrites: arithmetic identities, chosen for the shapes a verified
    program's accounting produces, and conditional identities over
    #vm[`ternary`], the encoding of every boolean connective (@sec:impl-vmir).],
  align(center, table(
    columns: (auto, auto),
    stroke: none,
    align: (left, left),
    inset: (x: 0.7em, y: 0.32em),
    text(size: 0.9em)[$x + 0 -> x$, #h(0.6em) $x - 0 -> x$], text(size: 0.85em, fill: luma(40%))[units],
    text(size: 0.9em)[$x dot 1 -> x$, #h(0.6em) $x \/ 1 -> x$, #h(0.6em) $x dot 0 -> 0$],
    text(size: 0.85em, fill: luma(40%))[units and annihilation],

    text(size: 0.9em)[$(x - p) + p -> x$, #h(0.6em) $(x + p) - p -> x$],
    text(size: 0.85em, fill: luma(40%))[an amount taken and given back],

    text(size: 0.9em)[$x - x -> 0$], text(size: 0.85em, fill: luma(40%))[an amount taken in full],
    text(size: 0.9em)[$x = x -> "true"$, #h(0.6em) $x < x -> "false"$],
    text(size: 0.85em, fill: luma(40%))[reflexivity],

    text(size: 0.9em)[$(b = "true") -> b$, #h(0.6em) $(b = "false") -> ternary(b, "false", "true")$],
    text(size: 0.85em, fill: luma(40%))[boolean equality is a ternary],

    text(size: 0.9em)[$ternary("true", x, y) -> x$, #h(0.6em) $ternary("false", x, y) -> y$],
    text(size: 0.85em, fill: luma(40%))[a folded condition],

    text(size: 0.9em)[$ternary(c, x, x) -> x$], text(size: 0.85em, fill: luma(40%))[both arms agree],
    text(size: 0.9em)[$ternary(c, "true", "false") -> c$],
    text(size: 0.85em, fill: luma(40%))[the condition, literalized in both arms],

    text(size: 0.9em)[$ternary(c, c, "false") -> c$, #h(0.6em) $ternary(c, "true", c) -> c$],
    text(size: 0.85em, fill: luma(40%))[the condition, recurring as an arm],

    text(size: 0.9em)[$ternary(c, c, "true") -> "true"$, #h(0.6em) $ternary(c, "false", c) -> "false"$],
    text(size: 0.85em, fill: luma(40%))[the condition, recurring as its other arm],
  )),
) <fig:rewrites>

The first pair of conditional rules is the one the rest of the chapter relies on:
once a condition is known, everything built under it reduces by the same rule
that simplifies any other conditional, with no case analysis anywhere.

One more rule turns a proven equality back into a merge: an #vm[`==`] node whose
class is known #vm[`true`] unions its two arguments. That is what lets an assumed
equality participate in congruence rather than sitting inertly as a fact, and it
is the rule doing the work in @lst:exec-vmir. A disproven #vm[`==`] node is read
back the other way, into whatever distinctness can be derived from it — that
family is where @sec:impl-adts picks up.

#para[What the ladder cannot do] Three things are missing from it, and the first
two are the price of the property the rest of the section was arguing for: every
tier answers with work proportional to the obligation in front of it, and a tier
that searches does not.

There is no decision procedure for arithmetic. Rewriting closes the
identities of the table above and nothing beyond them, so an obligation like
$i < n tack.r i + 1 <= n$ is
reported unproven.

There is no case split. A goal that needs genuine reasoning by cases over an
opaque condition is reported unproven rather than forked on. Even in its simplest
shape, a case split means probing the graph once per branch, on every obligation
that reaches it — explosive in a way #vm[`ite_decompose`] is not, since that tier
reads its conditions off the goal instead of choosing them. Whether a cheaper form
exists is a question this design leaves open rather than settles.

There is no disequality store. An e-graph records that two terms are equal and has
no way to record that they are not, so distinctness is derived where it can be —
from a constant-folding collision, from the contrapositive of congruence, or from
an observation that separates two values — and is otherwise deferred
(@sec:impl-adts).
