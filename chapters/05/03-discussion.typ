#import "../../macros.typ": *
#import "../../generated/setup.typ": timeout-cap
#import "../../generated/attribution-scalars.typ": *
#import "../../generated/attribution-permtree-scalars.typ": *
#import "../../generated/perf-rust-scalars.typ": *

== Discussion <sec:results-discussion>
The per-file ratios of @sec:results-quantitative spread over more than an order of
magnitude, and this section accounts for that spread. The explanation is not that
the slow files ask harder questions. Helium's prover ladder settles almost
everything the corpus puts to it at the cheapest of its tiers, and does so on a
slow file as readily as on a fast one. A member's cost follows instead the size of
the e-graph it builds, and the e-graph grows large only where a permission travels
across a branch. Most of the evidence below comes from counters Helium
records for itself, which are deterministic and therefore support a firmer claim
than a wall clock does.

#para[Discharging an obligation] Helium attempts the tiers of @sec:impl-execution
in order and stops at the first that succeeds, a design that rests on the
expensive tier being rare. @tbl:results-tiers-rust measures how rare it is. The
verifier credits exactly one tier per query, so a share of the ladder is a share
of the queries the corpus raised. Every tier reads the ground e-graph except
#vm[`implication_decompose`], which reads the copy described below.

A query and a proof obligation do not correspond one to one. The heap machinery puts questions to the ladder that it is prepared to hear a no to,
such as whether a demand is provably zero or whether two addresses coincide, and
it reads that no as a fact about the heap rather than as a failure. A single
obligation may equally raise several queries, since proving that the permission
held at a location covers what an exhale demands descends a tree of guards and
asks a query at each leaf. The #emph[declined] row therefore counts the queries no tier settled rather than
the obligations Helium failed. A member fails to verify only when its caller has
no route left.

#include "../../generated/attribution-tiers-rust.typ"

The cheapest tiers carry the corpus. #vm[`goal_true`] alone closes
#attr-rust-goal-share of the queries, rebuilding the e-graph and finding the goal
already merged with #vm[`true`] without a single rewrite firing.
#vm[`inconsistent`] fires #attr-rust-dead-block times, every one of them a block
whose own path condition is unsatisfiable rather than an e-graph that has turned
contradictory. Those are the dead arms of @sec:impl-cfg, which a #ru[`match`]
produces in quantity, and the non-vacuity check of @sec:results-quantitative
confirms that the unreachability originates in the encoding rather than in a state
Helium has corrupted. #vm[`implication_true`] fires #attr-rust-implication-true
times, so the weakening it applies earns almost nothing the tier above had not
already closed. #vm[`saturate`], the first tier to run a rewrite search, accounts
for under half a per cent.

That leaves #vm[`implication_decompose`] at #attr-rust-decompose-share. Alone
among the tiers it reads a graph with the path condition assumed, and so alone
pays for a copy. Inside a method body that copy is the block
scratch: the assumption is made once per basic block, and every later obligation
of the block reads the scratch that already exists, so the cost is amortised over
the block rather than paid per obligation.

The ladder therefore answers cheaply for almost everything the corpus asks, and an
expensive file does not differ from a cheap one in how often it reaches the
expensive tier. Whatever separates the two lies outside the ladder, in the amount
of state each query is asked against. The rest of this section locates it there.

#para[The give-back at a join] The per-file ratios run from #rust-best-ratio down
to #rust-worst-ratio, and the files at the bottom share one shape: a Rust method
that mutates through a #ru[`&mut`] inside a #ru[`match`]. Each arm lends a
location out and takes it back before the arm ends, and Prusti encodes the lending
and the taking back as ordinary permission transfers guarded by the arm's
condition. The shape is expensive because the give-back does not name the location
the method started with. A reborrow is a fresh reference whose pointee is equated
to the original's by a postcondition, and that postcondition is released under the
arm's guard like every other fact the arm establishes. @lst:giveback states the
shape directly in Viper.

#viper(
  caption: [A location lent out inside an arm and taken back at a second name for
    it. #vi[`q`] is the same reference as #vi[`r`], but only where #vi[`b`] holds,
    so the permission returns at an address the ground e-graph cannot identify
    with the one the release names.],
  label: "lst:giveback",
  placement: auto,
)[```viper
method reborrow(r: Ref) returns (q: Ref)
  requires acc(r.val)
  ensures  acc(q.val) && q == r

method one_arm(r: Ref, b: Bool)
{
  inhale acc(r.val)
  if (b) {
    var q: Ref
    q := reborrow(r)
  }
  exhale acc(r.val)
}
```]

Helium merges a fact established under a block's path condition into the join as
an implication of that condition rather than as the fact itself.
Consequently #vi[`q == r`] holds only under #vi[`b`], so at the join point #vm[`val(q)`]
and #vm[`val(r)`] resolve to two different e-classes, preventing the two heap
chunks from merging.

At the join point the heap effectively holds two chunks: #vm[`val(q)`]
with #vm[`b ==> 1/1`] permission and #vm[`val(r)`] with #vm[`!b ==> 1/1`] permission.
The exhale demands #vm[`1/1`] permission at #vm[`val(r)`], which the verifier
cannot assert directly. The e-graph records only #vm[`b ==> q == r`], from which
the two chunks coincide under #vm[`b`] and together carry a full permission.
Deriving that lies beyond Helium's reasoning, so the mechanism falls back to a
recovery that case splits on the permission amounts, which can be slow on real
code.

Over the Prusti-generated corpus #attr-giveback-files files of
#attr-giveback-files-total reach the recovery at all, and four spend measurable
time there: #attr-giveback-0-case, #attr-giveback-1-case, #attr-giveback-2-case
and #attr-giveback-3-case. The fifth, #attr-giveback-4-case, reaches it just
#attr-giveback-4-consumes times, and is among the corpus's fastest files against
Silicon. A file's ratio therefore suffers from reaching the recovery often and in
more complex state, not from reaching it at all. The heaviest user is
#raw("m_shape_grow"), which spends #attr-giveback-m-shape-grow-secs in the
recovery, #attr-giveback-m-shape-grow-share of its own verification time.

The recovery thus accounts for about a tenth of what the corpus's slowest file
pays, which leaves the other nine tenths to account for. Part of the remainder
goes on the permission sufficiency checks. If not discharged immediately, the
verifier descends down the ternary tree attempting to prove sufficiency.
Discharging every such check for free, which is unsound and done here only to
establish an upper bound, splits the corpus in two. Both columns of
@tbl:results-permtree are measured outside a sweep, so they sit a little under
the times reported in @sec:results-quantitative, and only the difference between
them carries meaning.

#include "../../generated/attribution-permtree.typ"

The descent costs #attr-permtree-branchy-lo to #attr-permtree-branchy-hi on the
#attr-permtree-branchy-files files whose permissions are branch-structured, and at
most #attr-permtree-other-hi on the #attr-permtree-other-files that are not, with
nothing in between. The files that pay for the descent are those that reach the give-back recovery,
as expected, since a permission lent away under a guard builds the tree.

The descent nonetheless leaves most of the cost unexplained. With every permission
proof free, #attr-giveback-0-case takes #attr-permtree-worst-assumed against
#attr-permtree-worst-walked, a reduction of #attr-permtree-worst-cut. Discharging
permissions therefore accounts for roughly a quarter of what the slowest file
pays, and the remainder lies elsewhere.

#para[Cost and state size] The remainder is the size of the state. Helium verifies
each member in its own e-graph, and @fig:results-member-size sets what a member
costs against how large that graph grows. Verification time grows as the
#attr-size-exponent power of the number of e-nodes, with an $R^2$ of
#attr-size-fit over three orders of magnitude in both quantities. The growth
steepens to the #attr-size-large-exponent power on the graphs above
#attr-size-large-cut e-nodes.

#include "../../generated/attribution-member-scatter.typ"

The four files that spend measurable time in
the give-back recovery lie on the same line as the seven that do not, and
#rust-worst's members sit at #attr-size-worst-residual their predicted time. A
slow file is therefore slow because it carries more state, at the price per
e-node every other file pays for a graph of the same size:
#attr-size-worst-member builds #attr-size-worst-nodes e-nodes and takes
#attr-size-worst-secs, against #attr-size-smallest-nodes e-nodes for the
smallest member in the corpus.

#para[Scaling with branching] The Prusti-generated corpus varies many things at
once. To vary a single parameter we generate two families of Viper programs over
the number of chained conditionals a method contains.
Both close with the same obligation: two locals are updated
identically on every arm, so their equality holds on all paths and proving it is
the join's work rather than any arm's. The first family does nothing else. The
second lends a location out inside every arm and takes it back through a reborrow
whose identity with the original holds under that arm's guard alone. Because the obligation is held fixed, the difference between the
curves is the cost of the permission traffic. Helium is measured on the give-back family only to
#attr-branch-perm-helium-depth conditionals, where it already takes
#attr-branch-perm-hi with its e-graph growing by
#attr-branch-perm-nodes-growth per conditional, so its curve stops there while the
other three run the full range.

#include "../../generated/attribution-branching.typ"

@fig:results-branching plots both families. Without permission traffic Helium is
flat: it takes #attr-branch-pure-lo at one conditional and #attr-branch-pure-hi at
#attr-branch-depths, while Silicon in its default configuration goes from
#attr-branch-pure-silicon-lo to #attr-branch-pure-silicon-hi as the paths it
explores double. Helium's lead over that configuration therefore widens with the
branching, from #attr-branch-pure-ratio-lo to #attr-branch-pure-ratio-hi. The
e-graph grows by #attr-branch-pure-nodes-step e-nodes per conditional in
@tbl:results-branching-size, from #attr-branch-pure-nodes-lo to
#attr-branch-pure-nodes-hi.

Silicon's growth on the branch-only family is a property of that configuration
rather than of symbolic execution. Bösiger's join points @perf-impr are available
as #raw("--moreJoins 2"), at which Silicon merges the arms of a conditional
wherever it can rather than exploring each path to the end. This family is the
best case that mechanism can be given, since the two arms agree on every
variable, so a merge has one conditional expression to build and no permission to
scale. Under
the flag Silicon's curve flattens accordingly, from #attr-branch-morejoins-lo at
one conditional to #attr-branch-morejoins-hi at #attr-branch-depths,
#attr-branch-morejoins-gain faster than its default at the widest setting. Over
the whole range the three configurations grow by #attr-branch-pure-helium-growth
for Helium, #attr-branch-morejoins-growth for Silicon under the flag and
#attr-branch-pure-silicon-growth for Silicon's default. Joining thus removes most
of what branching costs Silicon without removing all of it, and Helium degrades
least of the three. A constant separates the two verifiers
otherwise: Helium leads Silicon's better configuration by
#attr-branch-morejoins-ratio-hi at #attr-branch-depths conditionals. We attribute
that constant to Silicon's per-obligation overhead, of which forming an SMT query
and reading the answer back is the part the e-graph does not pay.

The give-back reverses the result. Helium goes from #attr-branch-perm-lo at one
conditional to #attr-branch-perm-hi at #attr-branch-perm-helium-depth, where
Silicon takes #attr-branch-perm-silicon-at-helium-hi, and Silicon reaches only
#attr-branch-perm-silicon-hi at #attr-branch-depths. A lead of
#attr-branch-perm-ratio-lo at one conditional becomes a deficit of
#attr-branch-perm-ratio-hi at #attr-branch-perm-helium-depth, and the two
verifiers cross at #attr-branch-crossover conditionals. The time is spent on the
e-graph, which grows from #attr-branch-perm-nodes-lo to
#attr-branch-perm-nodes-hi e-nodes, a factor of #attr-branch-perm-nodes-growth per
conditional against the branch-only family's fixed increment of
#attr-branch-pure-nodes-step. Each conditional contributes a chunk whose address
equals the previous one under that conditional's guard alone, so the partition the
release traverses grows with the family and every term reasoning about it carries
one more guard. The guards differ from one conditional to the next, so the terms
mentioning them differ too and share nothing across the family.

Silicon's own two curves stay close together and grow at the same rate,
#attr-branch-pure-silicon-growth over the range without the permission traffic and
#attr-branch-perm-silicon-growth with it, which is the other half of the result.
Permission moving across a branch is ordinary work for a symbolic execution
engine, because each path is explored with its own guard assumed and the
reborrow's identity with its original is an ordinary fact there. The two families
consequently separate branching from the permissions crossing it. They confirm
over a generated family what the attribution above establishes over the corpus: a
branch Helium can merge costs it a constant, while a branch across which
permission moves costs it a state that grows with the branching. Read together with the
#raw("--moreJoins") curve, the two families bound the contribution of the
representation more tightly than the corpus does. Once Silicon is allowed to join,
Helium's advantage on branch-heavy code is a constant factor per obligation rather
than a better asymptote, and it is confined to the branches across which no
permission travels. @sec:future-work develops the design that would lift the
second restriction, a fork of the verification state at a branch, in which an
arm's guard is assumed outright and the reborrow's identity with its original
becomes the same ordinary fact it is for Silicon.

