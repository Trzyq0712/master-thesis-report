#import "../../macros.typ": *

== The Symbolic Heap <sec:impl-heap>

#todo[
  New section, and it must precede Fields. This is a representation
  contribution in its own right — do not let it get discovered incidentally
  under method calls.

  Deliberately restricted to the *straight-line* heap. Everything conditional
  is deferred to @sec:impl-cfg, which is where a branch first forces two heaps
  to be reconciled and so where conditional chunks are actually motivated.

  Drafted. Permission amounts and proving sufficiency moved to
  @sec:impl-heap-interaction, since both need predicates first; this section
  says what a chunk is and what the partitioning of chunks buys, and nothing
  about operating on one.

  Chunks are presented as the bare triple, deliberately. A chunk also carries a
  reachability guard and a recipe provenance; the first belongs to
  @sec:impl-cfg and the second to functions, and neither means anything yet on
  the straight-line path. Decide later whether they arrive unannounced or get
  one forward sentence here.

  The closing claim of Partitioning — that the corpus never needs a
  non-aliasing constraint — is asserted, not shown. Either cite the evidence
  from @sec:prusti-needs or soften it to what was observed.

  Consolidation has a precision result worth writing up if there is room.
  Silicon's `combineSnapshots` splits the same three ways, but where neither
  fraction is definitely positive it mints a *fresh* snapshot constrained by
  both implications, on the grounds that picking either value and constraining
  it is unsound. Case-analysing on $p_0 > 0$ is that statement made total: no
  fresh symbol, and strictly more precise. Source it from Silicon's
  implementation rather than the thesis before claiming it.

  #para[Run-in headings] Locations / Chunks / Partitioning / Consolidation /
  Location axioms
]

#para[Locations] Viper distinguishes between the two kinds of resource a
program can hold permission to: a field of an object, and an instance of a
predicate. VMIR collapses that distinction and knows only about _locations_.

A location type is written #vm[`&[g] T @ p`] and has three components. The
_stored type_ #vm[`T`] is the type of the value held there. The _permission
bound_ #vm[`p`] caps how much permission any single location of this kind may
hold, and is either a rational constant or #vm[`*`], meaning unbounded. A Viper
program produces only the two extremes: #vm[`1/1`] for a field, matching
#vi[`write`], and #vm[`*`] for a predicate instance, since nothing stops a
program from holding arbitrarily many of those. The _group_ #vm[`g`] identifies
the declaration the location came from.

#todo[
  *Figure.* Anatomy of #vm[`&[g] T @ p`], arrows from each component to its
  name and one-line gloss. Three components in one sentence each is exactly the
  shape prose handles worst. Use a concrete type rather than the schematic one
  — #vm[`&[f] Int @ 1/1`] labelled group / stored type / bound — so the figure
  doubles as the field example that Fields opens with.
]

Because all three live in the type rather than in a side table keyed by syntax,
a location describes itself. This matters because locations are ordinary values
and can therefore be _computed_: a location may be produced by a ternary or
returned from a call. However it was produced, the verifier can still recover
what is stored there and how much permission it may carry, and nothing
downstream requires it to have come from a syntactic field access.

#para[Chunks] What the heap holds is a set of _chunks_. A chunk is a triple: the
_location_ it sits at, the _permission amount_ held there, and the _value_
stored. For a field chunk the value is the field's contents; for a predicate it
is the instance's snapshot (@sec:impl-predicates).

A chunk names its parts by e-class rather than by term. In particular its
location is an e-class of the graph that already carries the program's
equalities, so two chunks sit at the same location exactly when their location
e-classes are one, and establishing that costs a lookup rather than a query.

#para[Partitioning] <sec:impl-heap-partitioning> The symbolic heap is not a
single flat map from locations to chunks. It is partitioned by _location kind_,
which is nothing other than the location type itself: group, stored type and
permission bound. Every chunk lives in exactly the partition its type names,
and the two are looked up together: an access resolves first to a partition and
only then to a chunk within it.

#todo[
  *Figure.* The heap as boxes, one per location kind, chunks inside each. Two
  field groups and one predicate group is enough. It should make three things
  visible at a glance that the prose spends a paragraph on each: that a chunk
  cannot be in two boxes, that #vi[`x.f`] and #vi[`y.g`] are in different
  boxes, and that the predicate box is the #vm[`*`] one that receives no
  axioms.
]

Since the kind is read off the location's type, a computed location is filed as
reliably as one written as a field access, and locations from different
declarations never meet. Aliasing is therefore only ever a question _within_ a
partition, where identity is the location's e-class: two accesses alias exactly
when their location terms have been merged. What remains is to say what becomes of a
pair of chunks that does turn out to be at one location, and what is assumed of
a pair that does not.

#para[Consolidation] Equality reasoning can therefore bring two chunks of a
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

Stating it this way makes both cases come out on their own. When both fractions
are positive the antecedent holds, saturation collapses the implication to
$v_0 = v_1$, the two values are merged into one e-class, and the asymmetry of
the pick disappears with them. When one fraction is zero the antecedent is
false, nothing is assumed of a value nobody holds, and the pick selects the one
genuinely held. Equating the values outright would be unsound in the second
case, and is unnecessary in the first.

#todo[
  *Figure.* Consolidation before and after. Left: one partition, two chunks at
  distinct location e-classes. Middle: the e-classes merge. Right: one chunk
  holding $p_0 + p_1$ and the picked value, with the assumed agreement beside
  it. This is the densest mechanism in the section — a fold, an asymmetric
  pick and a conditional assumption, all in one operation — and the figure is
  the one place the reader could see that the merge is what *triggers* the
  fold, rather than being the fold.
]

Silicon carries the same obligation at a considerably higher price. A chunk
there holds terms, so whether two chunks describe the same location is a
question for the solver, and the _state consolidation_ that answers it must
iterate to a fix-point: merging one pair contributes equalities that may in
turn permit the next merge. Its worst case is cubic in the number of heap
chunks, and the optimisations carried by the implementation are reported not to
change that bound @silicon[Section 3.4.2]. That is too much to pay after every state
update, so consolidation happens at statically and dynamically chosen points —
partially when permissions are added, fully when an assertion fails — trading
completeness against cost. Holding locations as e-classes does not remove the
work so much as the fix-point. Congruence closure has already propagated the
equalities, so one pass over one partition suffices, and it is cheap enough to
run at every lookup rather than be scheduled.

#para[Location axioms] Two chunks of one partition that have _not_
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

None of this is needed to verify the corpus of @sec:prusti-needs. Prusti's
encoding does not ask the verifier to derive that two references are distinct,
so the constraint is stated because a Viper backend should state it, not
because the target frontend depends on it.
