#import "../../macros.typ": *
#import "../../figures/location-anatomy.typ": location-anatomy
#import "../../figures/heap-partitions.typ": heap-partitions
#import "../../figures/consolidation.typ": consolidation

== The Symbolic Heap <sec:impl-heap>

Everything so far has been values. The heap is the other half of the state, and
this section is what it is made of: what a permission-carrying thing is, where a
chunk holding permission to one lives, and what happens when two chunks turn out
to be at the same place. The instructions that move permission around are
@sec:impl-heap-interaction; the two declaration forms that produce something to
hold permission to are @sec:impl-fields and @sec:impl-predicates.

The section is deliberately restricted to the _straight-line_ heap. Everything
conditional is deferred to @sec:impl-cfg, which is where a branch first forces two
heaps to be reconciled and so where conditional chunks are actually motivated;
what a chunk is and what partitioning it buys can be settled without any of that.

Viper distinguishes between the two kinds of resource a
program can hold permission to: a field of an object, and an instance of a
predicate. VMIR collapses that distinction and knows only about _locations_.

A location type is written #vm[`&[g] T @ p`]. The _stored type_
#vm[`T`] is the type of the value held there. The _permission bound_ #vm[`p`]
caps how much permission any single location of this kind may
hold, and is either a rational constant or #vm[`*`], meaning unbounded. A Viper
program produces only the two extremes: #vm[`1/1`] for a field, matching
#vi[`write`], and #vm[`*`] for a predicate instance, since nothing stops a
program from holding arbitrarily many of those. The _group_ #vm[`g`] identifies
the declaration the location came from.

#figure(
  pad(y: 0.6em, location-anatomy),
  caption: [Anatomy of a location type, against the concrete instance
    #vm[`&[f] Int @ 1/1`] rather than the schematic #vm[`&[g] T @ p`].],
) <fig:location-anatomy>

Because all three live in the type rather than in a side table keyed by syntax,
a location describes itself. This matters because locations are ordinary values
and can therefore be _computed_: a location may be produced by a ternary or
returned from a call. However it was produced, the verifier can still recover
what is stored there and how much permission it may carry, and nothing
downstream requires it to have come from a syntactic field access.

What the heap holds is a set of _chunks_. A chunk is a triple: the
_location_ it sits at, the _permission amount_ held there, and the _value_
stored. For a field chunk the value is the field's contents; for a predicate it
is the instance's snapshot (@sec:impl-predicates).

A chunk names its parts by e-class rather than by term. In particular its
location is an e-class of the graph that already carries the program's
equalities, so two chunks sit at the same location exactly when their location
e-classes are one, and establishing that costs a lookup rather than a query.

The triple is the whole of it on a straight-line path. A chunk carries two further
components that mean nothing until later: a reachability guard, which records the
branch a conditionally-held chunk survived (@sec:impl-cfg), and a provenance for
its value, which lets a function's body be replayed at a call site
(@sec:impl-functions). Both are introduced where they do something.

#para[Partitioning] <sec:impl-heap-partitioning> The symbolic heap is not a
single flat map from locations to chunks. It is partitioned by _location kind_,
which is nothing other than the location type itself: group, stored type and
permission bound. Every chunk lives in exactly the partition its type names,
and the two are looked up together: an access resolves first to a partition and
only then to a chunk within it.

#figure(
  pad(y: 0.6em, heap-partitions),
  caption: [The symbolic heap as boxes, one per location kind. A chunk lives
    in exactly one box; #vi[`x.f`] and #vi[`y.g`] are in different boxes
    despite sharing a stored type and bound; the predicate box is the
    #vm[`*`]-bounded one, dashed, and receives no location axioms.],
) <fig:heap-partitions>

Since the kind is read off the location's type, a computed location is filed as
reliably as one written as a field access, and locations from different
declarations never meet. Aliasing is therefore only ever a question _within_ a
partition, where identity is the location's e-class: two accesses alias exactly
when their location terms have been merged. What remains is to say what becomes of a
pair of chunks that does turn out to be at one location, and what is assumed of
a pair that does not.

#para[Consolidation] <para:impl-consolidation> Equality reasoning can therefore bring two chunks of a
partition to one location after both are already held, simply by merging the
e-classes of their locations. The two then hold permission to the same thing,
and their amounts have to be added up before either can be counted against a
demand. The verifier does this at lookup: resolving a
location scans the chunks of that location's partition, compares canonical
e-classes, and folds together any that have collapsed into one. Because the
heap is indexed by kind, that scan is linear in the size of one partition and
never touches another.

The permission is the easy half of a fold: the amounts add, and the surviving
chunk holds $p_0 + p_1$. The value takes more care. The two chunks may disagree
about what is stored, and only one holding positive permission has any claim to
be right about it. The merged value is therefore
picked asymmetrically, as $ternary(p_0 > 0, v_0, v_1)$, and the
agreement of the two
is _assumed_ rather than asserted:

$ p_0 > 0 and p_1 > 0 => v_0 = v_1 $

Silicon's `combineSnapshots` splits the same three ways and, where neither
fraction is definitely positive, creates a _fresh_ snapshot constrained by both
implications — on the stated grounds that using either of the two values and
constraining it would be unsound. The asymmetric pick is that judgement made
total rather than contradicted: the value is case-analysed on $p_0 > 0$ instead of
being left to a new symbol, which needs no fresh name and is strictly more
precise, since on each side of the case the value that is genuinely held is the
one selected.

Stating it this way makes both cases come out on their own. When both fractions
are positive the antecedent holds, saturation collapses the implication to
$v_0 = v_1$, the two values are merged into one e-class, and the asymmetry of
the pick disappears with them. When one fraction is zero the antecedent is
false, nothing is assumed of a value nobody holds, and the pick selects the one
genuinely held. Equating the values outright would be unsound in the second
case, and is unnecessary in the first.

#figure(
  pad(y: 0.6em, consolidation),
  caption: [Consolidation. The merge of two location e-classes is what
    *triggers* the fold that follows it, rather than being the fold: a
    separate step, drawn as a separate arrow.],
) <fig:consolidation>

Silicon carries the same obligation in a different shape. A chunk there holds
terms, so whether two chunks describe the same location is a question for the
solver, and the _state consolidation_ that answers it iterates to a fix-point:
merging one pair contributes equalities that may in turn permit the next merge.
Its worst case is cubic in the number of heap chunks, and the optimisations
carried by the implementation are reported not to change that bound
@silicon[Section 3.4.2]. Consolidation is therefore scheduled rather than
continuous — partially when permissions are added, fully when an assertion fails
— which trades completeness against cost.

Holding locations as e-classes removes the fix-point rather than the work.
Congruence closure has already propagated the equalities before the heap is
consulted, so one pass over one partition suffices and there is no second round
to run; and because a partition is indexed by location kind, that pass is linear
in one partition rather than in the heap. What that buys is that consolidation
can happen at every lookup rather than at chosen points, so the scheduling
question does not arise.

#para[Location axioms] <para:impl-location-axioms> Two chunks of one partition that have _not_
been merged are the converse case, and partitioning says just as precisely
where a non-aliasing constraint has to be injected: between exactly those
pairs, since
they are the only ones that could still turn out to denote the same location.
Both of the axioms the verifier states over a partition come from its bound.

The first applies to each chunk on its own, and is what makes the bound mean
anything: a chunk of a kind bounded by $b$, holding an amount $p$, satisfies

$ p <= b $

Where an amount folds to more than $b$ this leaves the state inconsistent, and
the verifier reads that as it should — the path cannot be reached, so anything
asked of it holds. Silicon does the same with `assume-valid-permissions`,
constraining each field chunk to at most #vi[`write`] and concluding from that
the infeasibility of certain paths @silicon[Section 3.4.2].

The second is the non-aliasing constraint, and applies to a pair. For two
chunks of the partition holding $p_0$ and $p_1$ at locations $ell_0$ and
$ell_1$, the verifier states

$ ell_0 = ell_1 => p_0 + p_1 <= b $

pairwise within a partition and nowhere else. Neither axiom has anything to say
where the bound is #vm[`*`]: with no $b$ to state them against, a partition of
unbounded kind receives neither.

Silicon states the same implication, but over receivers and against a fixed
bound: for each unordered pair of field chunks it adds the path condition
$x = y => p + q <= 1$ @silicon[Section 4.6]. Phrasing it over locations instead
is what makes it uniform. A field's location function is unary and a
predicate's takes the predicate's arguments, but the constraint mentions
neither, so one form covers a field, a predicate given a bound, and any other
producer whatever its arity — and the bound it is stated against is the one in
the location's type rather than #vi[`write`].

Partitioning by the whole location type, rather than by the group alone, is
what makes this convenient to state. Every chunk of a partition shares one
bound, so wherever a pair is considered the $b$ to state the constraint against
is already to hand.

It is likewise what makes the bound worth carrying in the location type rather
than deriving it from which of Viper's two resource kinds is in play. A
frontend that knows a particular predicate is sound to hold at most twice can
declare it at #vm[`2/1`], and the declaration is not merely documentation: it
moves that predicate's partition from the case that yields no constraint to the
case that yields one. A bound a frontend can justify is non-aliasing reasoning
the verifier then gets for free.

One question the axiom leaves open is how a program ever concludes #vi[`x != y`]
from it, since it is stated over locations and never mentions a receiver. The
answer is that it does not have to. Under #vi[`acc(x.f) && acc(y.f)`] the two
amounts sum past the bound, so the axiom's implication forces its antecedent
false and the two _locations_ are known distinct. Narrowing that to the receivers
is then the contrapositive of congruence: from a disproven #vm[`f(x) == f(y)`],
with every argument pair but one already merged — here there is only one pair —
the remaining pair must differ. That step is sound for any function, injective or
not, which is why the field's location function needed no injectivity axiom to
make it work.


#para[Permission arithmetic] <para:impl-perm-arith> The rewrite rules stated
earlier in this chapter were stated neutrally, because permissions did not
exist yet at that point in the chapter. This is what
half of them are for. $(x - p) + p -> x$ is an amount taken by an exhale and given
back by the matching inhale; $x - x -> 0$ is an amount taken in full; $x + 0 -> x$
is a give-back against a chunk that was already empty; and $ternary(b, p, 0) -> p$
under an assumed guard is a conditionally-held chunk on the path where the guard
holds. Each has a rational form as well as an integer one, and it is the rational
form that runs: a permission amount is a rational term, and the accounting a
verified program does with it is almost entirely of these four shapes. An
obligation that reduces by them is one the prover answers at its cheapest tier
rather than by reasoning about rationals at all.
