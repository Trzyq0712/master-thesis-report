#import "../../macros.typ": *
#import "../../figures/prove-ladder.typ": prove-ladder

== Discharging Obligations <sec:impl-proving>

Every instruction of the preceding section either produced a value or raised an
obligation, and the obligations were left standing. This section is what becomes
of them.

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

#para[#vm[`inconsistent`]] Asks whether the graph holds #vm[`true == false`]. It
is first because a contradictory state proves everything, so any work below it
would reach a conclusion already reached. It is affordable at that position
because a contradiction is not searched for but recorded as it happens — a class
forced to carry two different constants is merged with the inconsistent class —
so asking is two comparisons of class identifiers.

#para[#vm[`goal_true`]] Asks whether the goal holds on its own, before the
implication $"pc" => "goal"$ is built. The argument is allocation rather than
proving: the implication is a term, and building it inserts nodes that are
permanent. The cost of one is small, but an obligation that needs no path
condition at all — settled by constant folding the moment it is raised — would pay
it for nothing and leave behind a term nothing ever reads again.

#para[#vm[`imp_true`]] Builds the implication and asks whether _it_ is
#vm[`true`]. Nothing is cached to make this work: discharging an obligation merges
its implication with #vm[`true`], and that merge is a fact of the graph like any
other. What the tier is for is repetition: a Prusti encoding raises the same
framing obligation at each statement of a run that holds the same permission
(@sec:prusti-needs), and the second and later occurrences are answered here for
the price of a comparison.

#para[#vm[`saturate`]] Runs the rewrite rules to a fixpoint and asks again. It is
the first tier that does work rather than looking something up, and it sits above
the copying tier because its work is not thrown away: saturation runs on the live
graph, so every equality it derives stays in the state for every later obligation.
The rules themselves are the subject of #pararef(<para:impl-rewrites>,
[The rewrites]); what matters here is that they are identities, so what this tier
answers are the obligations that are true by rewriting rather than by reasoning — a boolean connective
collapsing to the condition it was built from, an assumed equality carried into
congruence — none of which needs a path condition.

#para[#vm[`probe`]] Assumes the path condition. A cube's literals cannot be merged
into the live graph, since they hold on one path only and merging them would make
the verifier believe them everywhere. So the graph is copied, the literals are
fixed in the copy, and the copy is saturated. The tier justifies its cost by what
would otherwise be unprovable rather than by how often it fires: a guarded
division, and every obligation raised under a condition the program itself wrote,
is answered here or not at all.

An obligation whose path condition is empty — or all of whose literals the live
graph already knows at the polarity the cube wants — passes this tier without work
to do, and the cheap questions of the copy cannot come out differently from the
ones already asked of the live graph. Such an obligation drops straight to the
last tier.

#para[#vm[`ite_decompose`]] The last tier, and the narrowest by design. It undoes
the encoding of an implication: VMIR spells $c => e$ as $ternary(c, e, "true")$
(@sec:impl-vmir), so a goal carrying a #vm[`true`] arm is an implication written
as a conditional, and what the tier does is read it back as one — assume $c$,
re-check $e$, and telescope a chain of nested implications one assumption at a
time. Its conditions are _read off the goal_ rather than searched for, which is
what separates it from a case split and keeps it bounded. That is also why the
tier is worth having at all: an obligation the program itself wrote as an
implication, and one arriving under a guarded axiom
(#vi[`b() ? (forall i :: foo(i)) : true`]), both reach the prover in exactly this
shape, and no tier above can do anything with the conditional as it stands.

#para[Constant folding] Underneath every tier is one rule set, always on.
Congruence and hash-consing come from the e-graph itself; the rest is an analysis
and a set of rewrites.

The analysis is constant folding, attached to every e-class. A class whose term
evaluates to a literal carries that literal, and it propagates upwards: the
operators fold when both operands are known, an integer cast folds a known
integer, and a conditional whose condition is known takes on the data of the arm
that condition selects. Two of its cases do more than evaluate. A class forced to
carry two different literals is a contradiction, which is what the first tier
looks for. And a class known to be an application of one datatype constructor,
compared for equality against a class known to be a _different_ constructor of the
same datatype, folds to #vm[`false`] — distinctness derived from the operands'
identity rather than from an axiom about tags (@sec:impl-adts).

#para[The rewrites] <para:impl-rewrites> The rules that fire during saturation are
identities rather than a theory, and the arithmetic ones are chosen for the shapes
a verified program's accounting produces:

#align(center, table(
  columns: (auto, auto),
  stroke: none,
  align: (left, left),
  inset: (x: 0.7em, y: 0.32em),
  text(size: 0.9em)[$x + 0 -> x$, #h(0.6em) $x - 0 -> x$],
  text(size: 0.85em, fill: luma(40%))[units],
  text(size: 0.9em)[$x dot 1 -> x$, #h(0.6em) $x \/ 1 -> x$, #h(0.6em) $x dot 0 -> 0$],
  text(size: 0.85em, fill: luma(40%))[units and annihilation],
  text(size: 0.9em)[$(x - p) + p -> x$, #h(0.6em) $(x + p) - p -> x$],
  text(size: 0.85em, fill: luma(40%))[an amount taken and given back],
  text(size: 0.9em)[$x - x -> 0$],
  text(size: 0.85em, fill: luma(40%))[an amount taken in full],
  text(size: 0.9em)[$x = x -> "true"$, #h(0.6em) $x < x -> "false"$],
  text(size: 0.85em, fill: luma(40%))[reflexivity],
  text(size: 0.9em)[$(b = "true") -> b$, #h(0.6em) $(b = "false") -> ternary(b, "false", "true")$],
  text(size: 0.85em, fill: luma(40%))[boolean equality is a ternary],
))

Each has an integer and a rational form, since the two are separate operators over
separate literals. The rational ones look idle against the rules above; they are
the ones the heap will exercise (@sec:impl-heap).

The conditional rules are the other family, and they matter because VMIR spells
negation and conjunction as #vm[`?:`] (@sec:impl-vmir), so every boolean
connective in the program passes through them. They reduce
$ternary("true", x, y)$ and $ternary("false", x, y)$ by the folded condition,
$ternary(c, x, x)$ to $x$, and the shapes that recover a condition from its own
arms — $ternary(c, "true", "false")$ to $c$, $ternary(c, c, "false")$ to $c$,
$ternary(c, c, "true")$ to #vm[`true`]. The first pair is the one the rest of the
chapter leans on: once a condition is known, everything built under it reduces by
the same rule that simplifies any other conditional, with no case analysis
anywhere.

These are written as a single fused rule rather than as a pattern each. A
two-level pattern like $ternary(c, "true", "false")$ backtracks over the cross
product of a bucket holding thousands of classes; scanning the bucket once and
deciding every shape from the node in hand is linear in it. As separate patterns
this family measured around 70% of all search time — in an e-graph the cost of a
rule is a property of its _shape_ and not of how often it fires.

One last rule turns a proven equality back into a merge: an #vm[`==`] node whose
class is known #vm[`true`] unions its two arguments. That is what lets an assumed
equality participate in congruence rather than sitting inertly as a fact, and it
is the rule doing the work in @lst:exec-vmir.

#para[What the ladder cannot do] Three things are missing from it, and the first
two are the price of the property the rest of the section was arguing for: every
tier answers with work proportional to the obligation in front of it, and a tier
that searches does not.

There is no decision procedure for linear arithmetic. Rewriting closes the
identities of the table above and nothing beyond them, so an obligation like
$i < n |- i + 1 <= n$ — true, and true by an argument no identity makes — is
reported unproven. @sec:beyond-fragment says where that bites.

There is no case split. A goal that needs genuine reasoning by cases over an
opaque condition is reported unproven rather than forked on, and
#vm[`ite_decompose`] is deliberately not a substitute: it assumes the conditions
the goal's own shape names, which is a bounded walk, where a case split chooses
conditions nothing in the goal asked about and must then close both arms. That
cost would fall on every obligation reaching the bottom of the ladder, including
the ones that fail there anyway. Whether a form exists whose cost falls only on
the goals that need it is a question this design leaves open rather than settles.

There is no disequality store. An e-graph records that two terms are equal and has
no way to record that they are not, so distinctness is derived where it can be —
from a constant-folding collision, from the contrapositive of congruence, or from
an observation that separates two values — and is otherwise deferred
(@sec:impl-adts).
