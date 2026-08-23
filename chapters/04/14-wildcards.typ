#import "../../macros.typ": *

== Wildcard Permissions <sec:impl-wildcards>

Everything the heap has done so far has been arithmetic. A chunk holds an amount,
an exhale proves the amount held is at least the amount demanded, and the two
location axioms of @sec:impl-heap are inequalities over sums. Viper has one
permission amount that fits none of that. A #vi[`wildcard`] is a _positive but
unspecified_ share: it says that something is held and refuses to say how much.

It exists because reading is not consuming. A program that only reads through a
location needs to know that _some_ permission is held, so that what it reads is
stable and nobody else may write; it must not name a fraction, because the amount
its caller happens to have is none of its business, and demanding a specific one
would make a read-only client fail against a caller holding less. Two things
produce a wildcard: writing one in the source, and the verifier's own read-only
lowering, which is where the great majority of them come from.

A wildcard is a #vm[`Symbolic::Wildcard`] node — a fresh
symbolic real, assumed $0 < w$ the moment it is created, and distinct from an
ordinary fresh value in exactly one respect: it can be _recognised_. That is its
whole purpose as a separate node. The facts a wildcard carries are the same facts
a fresh positive real would carry; what the distinct node buys is that an
instruction can see it is looking at a wildcard and take a different rule.

Nothing else about it is special, and in particular it is not a value. A wildcard
is legal only as a permission amount and never as an operand. The permission
grammar of @sec:impl-vmir is what enforces that: an amount, a bare
#vm[`wildcard`], or a ternary over the two, and nothing else. A wildcard therefore
cannot escape into a term, and every rule below is selected off that shape rather
than off anything in the e-graph.

#lowering(caption: [A source-level #vi[`wildcard`] is a permission amount and nothing else.], label: "lst:wildcard-inhale")[```viper
inhale acc(own_Account(x), wildcard)
```][```vmir
h1 := h0 + own_Account@loc(e0) @ wildcard
      with fresh
```]

Source-level wildcards are rare and uniform in a Prusti encoding: every one is
a predicate share taken by an #vi[`unfolding`], never a field share and never
in a contract.

#para[Where wildcards come from] <para:impl-readonly> The lowering applies a
_read-only policy_ in the two places where the program is known to be reading: a
function's body, and the resource its precondition lowers to (@sec:impl-functions).
Under that policy every permission amount is weakened as it is lowered — a constant
zero stays zero, a constant nonzero amount becomes a #vm[`wildcard`], and a
symbolic amount $p$ becomes

$ ternary(p > 0, "wildcard", 0) $

The three cases are one rule seen at three levels of information. A demand for
nothing stays a demand for nothing; a demand for something definite is weakened to
a demand for anything positive; and a demand whose size is not known until run time
is weakened to whichever of those two it turns out to be. The gate is what keeps a
_conditional_ footprint conditional: a precondition #vi[`requires b ==> acc(x.val_i32)`]
lowers to a slot whose permission is #vm[`ite(b, wildcard, 0)`], so the slot is
demanded where #vm[`b`] holds and is exactly zero where it does not, and a branch
that const-folds away takes its wildcard with it.

Weakening a function's demand is right for any frontend rather than an
accommodation of Prusti's encoding. It is what makes a function callable from a
caller holding any positive share, which is the property a pure function ought to
have; the fact that Prusti's encoding leans on it heavily
(#pararef(<para:impl-wildcard-buys>, [What it buys])) is a consequence and not the
reason.

#para[Exhaling a wildcard] <para:impl-wildcard-exhale> The subtract of
#pararef(<para:impl-subtract>, [Giving permission back]) discharges

$ p_"held" >= p_"needed" $

and there is no such obligation to state here, since $p_"needed"$ has no value to
compare against. The rule is a different one. The verifier proves

$ 0 < p_"held" $

under the path condition, and replaces the chunk's amount with a _fresh_ remainder
$r$, assumed $r < p_"held"$. The demanded wildcard never enters the result at all:
what leaves the location is known only to be positive and to be less than what was
there, which is everything a wildcard ever says.

Two consequences fall out of that shape rather than out of any case in the rule.
The chunk is never emptied, because the remainder is itself a wildcard and so
positive — a wildcard exhale can be repeated indefinitely and always leaves
something behind. And exhaling a wildcard from a location holding nothing fails, as
it must, because $0 < p_"held"$ is not provable of an absent chunk; a wildcard is
positive by construction, so this is not a completeness gap but the right answer.

The remainder is fresh rather than a subtraction node for a reason worth stating,
because it is the same reason as everywhere else in this chapter. The e-graph
carries no order theory over the reals, so from a node standing for
$p_"held" - w$ neither $0 < p_"held" - w$ nor $p_"held" - w < p_"held"$ follows;
both would have to be assumed, about a term that grows a layer with every exhale.
A fresh $r$ states them once, at any depth: $0 < r$ comes free with its creation, and
$r < p_"held"$ is asserted here. That second fact is not bookkeeping — it is what
makes #vi[`assert perm(x.val_i32) < 1/2`] provable after a wildcard has been taken from a
half share.

#para[Adding a wildcard] <para:impl-wildcard-add> Consolidation
(#pararef(<para:impl-consolidation>, [Consolidation])) folds two chunks at one
location by summing their amounts, and a sum with a wildcard in it is opaque for
the same missing-order-theory reason: from a node standing for $1/2 + w$, even
$0 < 1/2 + w$ is underivable. Building the sum and then attaching facts to it means
restating those facts over a tree that keeps getting deeper.

So the sum is not built. A leaf whose summands mention a wildcard becomes a fresh
share $s$ carrying the facts instead: $0 < s$, which comes free with its creation, and
$x < s$ for each summand $x$ whose _other_ summand is positive. The second is what the sum node never gave, and it
is what makes #vi[`perm(x.val_i32) > 1/2`] provable after inhaling a wildcard onto a half
share. Meeting the location axiom's $p <= b$ from the same partition, it also makes
#vi[`inhale write; inhale wildcard`] come out inconsistent — the state is
unreachable, which is Silicon's verdict on it too.

Both tests are made per _leaf_, after the join's branch structure has already split
the arms apart, and both are structural judgements decided without a prover call. A
leaf with no wildcard in it keeps its sum node, which const-folds — replacing
#vm[`1/2 + 0`] with an opaque symbol would lose information rather than add it. A
leaf whose wildcard is only conditionally present, #vm[`ite(g, w, 0)`], is not
positive, so it states nothing, which is the truth. The facts themselves are
ungated: $x < x + y$ with $y$ positive holds on every path, and the arm-dependence
lives entirely in _which_ leaf, which the positivity test has already decided.

What is _not_ stated is worth as much as what is. Two wildcards are related by
nothing — neither $w_1 < w_2$ nor $w_1 = w_2$ nor any bound on their sum — so two
wildcard shares do not add up to a full permission, and a subsequent
#vi[`exhale acc(x.val_i32, 1/1)`] correctly fails. That is Viper's semantics and not an
approximation of it: two unspecified positive shares genuinely need not be a whole.

Silicon reaches the same place by the opposite route. It materialises the same sums
and hands them to the solver's linear real arithmetic, so it needs no wildcard case
for addition at all — the facts above are consequences the solver derives rather
than facts a rule states. Where it does treat a wildcard specially is
multiplication, collapsing $w * q$ to $w$ for a positive literal $q$, which is the
same observation from the other side: a wildcard carries a sign and no magnitude,
so scaling it changes nothing. The thesis @silicon[Section 2.7] discusses the
permission model and abstract read permissions but not #vi[`wildcard`] itself; the
comparisons in this section are against the implementation, where the exhale rule
of #pararef(<para:impl-wildcard-exhale>, [Exhaling a wildcard]) is the
constrainable-ARP rule.

Which of the two consume rules applies is decided
from the permission's _shape_ — statically, from the instruction the verifier was
given — and never by inspecting the e-graph. The distinction matters more than it
looks. Asking the e-graph whether a term is a wildcard is asking about an e-class,
and congruence can put other nodes into an e-class; a question that was answered
one way early in a method can be answered the other way later, without anything
about the instruction having changed. Reading the shape asks about the program.

Silicon keeps the same separation for the same reason: its wildcard marker drives
no semantics, and the read rule is selected from a set of constrainable permissions
carried in the execution state rather than recognised in a term. The structural
gate on the lowering side is what makes this possible — a gated wildcard is kept as
a permission ternary rather than flattened into a value ternary, so the shape
survives all the way from the source to the rule that dispatches on it.

One use of a wildcard footprint does not want the
wildcard. A heap-dependent function call checks its precondition
(@sec:impl-functions), and what that check needs to establish is that the footprint
is _there_ — the call takes nothing and gives nothing back. For a slot whose
permission is a bare wildcard the verifier therefore builds full permission in the
wildcard's place and subtracts nothing: gated, that is #vm[`ite(g, 1, 0)`], whose
positivity folds to #vm[`g`] itself, so the obligation is exactly the slot's
presence and the heap is untouched.

The reason is cost rather than meaning. Creating a real wildcard here would leave a
ternary over a symbol in the persistent e-graph — one that no reduction can
collapse, since its arms are genuinely different — and every later saturation would
walk it. Building the presence indicator instead leaves a term that folds away
before it is stored. Silicon takes the same shortcut in the same place, answering a
read-only assertion of a wildcard with full permission.

#para[What it buys] <para:impl-wildcard-buys> The read-only policy pays for itself
on one pattern, and it is a pattern Prusti's encoding is built out of. Consider a
function that unfolds a predicate and, _inside_ that unfold, calls another function
which itself requires the same predicate:

#viper(caption: [A function that unfolds a predicate it also passes on. Invented: the corpus's nested calls are always to a _different_ predicate's snapshot function.], label: "lst:wildcard-nested-unfold")[```viper
function get(this: Ref): Int
    requires acc(P(this))
{ unfolding P(this) in this.v }

function get2(this: Ref): Int
    requires acc(P(this))
{ unfolding P(this) in this.v + get(this) }
```]

With written permissions this cannot verify. The outer #vi[`unfolding`] consumes
all of #vi[`P(this)`], and the nested #vi[`get(this)`] finds nothing left to
satisfy its own precondition with. Under the read-only policy both the
#vi[`unfolding`] share and the precondition demand are wildcards, so the unfold
takes some $w < p_"held"$ and leaves a positive remainder — and the nested call
finds a share, as it must, since neither call is consuming anything. The same body
written as a method, where permissions are the ones written, fails exactly as
described. That asymmetry is the point: a function is read-only, and the lowering
is what says so.

What this costs a program with no wildcards in it is nothing. Both the produce and
the consume path are gated on a flag computed once per program, so a wildcard-free
program builds the same terms it would have built without any of this.

Every fact a wildcard carries is stated directly — $0 < w$ at
creation, $x < s$ at a sum, $r < p_"held"$ at an exhale — and nothing chains them.
The gaps are all in that: they are the arithmetic gap of @sec:beyond-fragment seen
from the permission side, and they are narrow enough to name.

Holding $1/2 + w$ and exhaling $1/2$ discharges. The produce rule assumed
$1/2 < s$ of the fresh share, the sufficiency goal is $not (s < 1/2)$, and
asymmetry of a strict order — $a < b => not (b < a)$ — closes the two directly,
now that the rule set states it alongside the fold of $<$ on literals. What still
does not chain is two facts in sequence: after
#vi[`inhale acc(x.f, 1/2)`] and two wildcard inhales the state holds
$1/2 < s_1 < s_2$, and concluding #vi[`perm(x.f) > 1/2`] from it needs
transitivity, which asymmetry alone does not give. The single-fact form of the
same assertion verifies on the strength of asymmetry by itself — the remaining
limit is at chaining two wildcards, not at a single one.

One smaller gap. No upper bound is imposed when a wildcard is created; it arrives
later, from the location axiom of a bounded partition
(#pararef(<para:impl-location-axioms>, [Location axioms])) and from
$r < p_"held"$ at each exhale. The non-negativity obligation an ordinary
permission carries, by contrast, now discharges for a wildcard-bearing amount as
well, including a gated one that is genuinely zero on one path: the creation-time
assumption $0 < w$ closes $not (w < 0)$ by the same asymmetry rule.

None of this is reached by the corpus. Every wildcard in the encodings is a
predicate share taken by an #vi[`unfolding`] at a location holding nothing else, so
no sum of a wildcard with a fraction is ever formed and no order between two shares
is ever needed. What is lost in the chaining case above is a proof and not a
record: the chunk is in its partition with its share as a term, the facts that
were assumed are in the state, and the obligation is a pair of e-classes that a
procedure with transitivity would close.

A wildcard used as an arithmetic operand rather than as a permission amount is
rejected by the lowering outright, and is one of the constructs collected in
@sec:beyond-fragment.

What a wildcard is has been said here; where nearly all of them come from has only
been named. @sec:impl-functions is the construct that applies the read-only policy,
at both of its sites, and it is the section this one exists to serve.
