#import "../../macros.typ": *

== Loops <sec:impl-loops>

@sec:impl-cfg assumed the block graph was acyclic, cut the back edges, and named
the exchange at the cut without saying how it is performed. This section is that. It is also the one section
whose subject the measured corpus does not exercise: the encodings of
@sec:prusti-needs are loop-free by construction, and the two loops this chapter
works from are the guiding example's, which is not among them (@sec:example). What
that means for the reading of what follows is that the mechanism is pinned down by
a program rather than by a benchmark: it is complete as a mechanism, and limited by
something else.

#para[Where a loop comes from] A loop is _any back edge_: an edge whose target
dominates its source. Source-level #vi[`while`] is desugared at the control-flow
graph and is only a special case; a Prusti-shaped method carries its invariant on
the loop head's #vi[`label`] and reaches it with a #vi[`goto`], and back-edge
detection finds both without distinguishing them. This mirrors Silver's own loop
detector, which likewise runs dominator-based detection over the goto graph and
classifies edges only afterwards.

Detection yields three things the lowering needs: the edges to cut, which leaves a
DAG and so preserves the topological order @sec:impl-cfg walks in; one natural
loop per head, with its body; and a classification of every edge by which loops it
leaves and which it enters — innermost-first for the former, since leaving two
loops at once has to unwind them in order. A cycle with more than one entry is
irreducible, has no natural loop, and is rejected with a diagnostic.

#para[The cut] At a loop head the verifier stops threading the incoming state and
performs an exchange. The invariant is _exhaled_ from the heap the forward
predecessor arrived with, at the pre-havoc values: that is the entry obligation,
and it is a claim about the state control actually arrives in. What the exhale
leaves behind is the _frame_ — everything the invariant did not ask for. Every
variable the loop body writes is then replaced by a fresh value, and the body's
entry heap is built by inhaling the invariant into #vm[`empty`].

That inhale binds #vm[`with fresh`], and it is the one place in a method body
besides an allocation where that is the point rather than an admission
(@sec:impl-predicates). A cut exists in order to discard information: the values the invariant's
footprint holds at the body's entry must be an arbitrary iteration's, not the
entry iteration's, and binding them to the snapshot the entry exhale just yielded
would defeat the havoc as surely as leaving the written variables alone would.

So the body starts from the invariant and from nothing else. The frame is not
visible to it, the pre-loop values of written variables are gone, and whatever the
body can prove it proves for an arbitrary iteration. A back edge exhales the
invariant again and stops; nothing flows out of it, since the edge was cut and no
successor reads its heap. Permission left over at the back edge is not required to
be empty and is simply lost, which is what Silicon does too.

The havoc set is every variable the body assigns or declares, computed
syntactically. Over-approximating it is sound — a needlessly havoc'd variable only
loses information — and under-approximating it is not, so the analysis errs in the
direction that costs precision.

#para[Framing] What the invariant does not mention survives the loop untouched,
and that is not a modifies analysis: it is permission arithmetic. The frame is an
ordinary heap, named by a temporary like any other heap, and an edge leaving the loop simply
takes the _sum_ of the body's live state and the frame that head set aside.
Leaving nested loops sums them innermost-first. Silicon needs a stack of invariant
contexts at this point only because its heap threads implicitly; here the frame
has a name, and the operation that uses it is the same union that adds any two
heaps held at once.

The sum is where a subtlety arises. Two chunks at one location must agree on their
value — but only where both are actually held, and the frame's residual after an
exhale may be a chunk holding nothing. Equating values outright let a stale
pre-loop value merge with the loop's havoc'd symbol, erasing the havoc on the
branch where the loop ran. The rule is therefore the same one @sec:impl-heap
states for any pair of chunks: the values are merged only where both fractions are
provably positive, and otherwise the asymmetric pick and its conditional agreement
carry the case.

That is also what makes read-only framing work, and it works by arithmetic rather
than by a rule about reading. An invariant demanding a #vm[`wildcard`] share
leaves the frame a positive residual, so the frame still holds the location, so
the location's value survives the loop. An invariant demanding #vi[`write`] takes
everything, the frame's residual is empty, and the value does not survive. Two
programs differing only in that amount therefore differ in whether an assertion
after the loop holds — and both agree with Silicon, which is the pair the test
corpus uses to pin the mechanism down.

#para[Where we fall short] The mechanism above verifies loops that Silicon
verifies: a zero-iteration loop, a load-bearing invariant established and
preserved and consumed, a #vi[`break`], nested loops, loops under a path
condition, a linked structure traversed by unfolding, and a half-permission frame
restored at the exit. The control that matters is the negative one: the same
program with its invariant dropped must fail, and it does — a cut that quietly
threaded the pre-loop state through would pass the positive case and be silently
unsound.

What fails is a family of cases that look like loop failures and are not. A
counting loop — #vi[`while (i < n) invariant 0 <= i && i <= n`] — is rejected, and
the obligation it fails on is $0 <= i and i <= n, i < n |- i + 1 <= n$. That
obligation has nothing to do with loops: it fails identically with no loop
anywhere in the program. It is the arithmetic gap of @sec:impl-proving, and
every case in the loop corpus that Silicon verifies and this verifier does not
fails on exactly it. The structural cases — where the loop is driven by a
discriminator test on a recursive datatype rather than by a counter — exercise the
same cut with no arithmetic anywhere, and they pass. The guiding example has one
of each, and they split exactly that way: #ru[`sum_balances`] walks its list by
unfolding and goes through, #ru[`sum_up_to`] counts and does not.

Two things are out of scope rather than unfinished. Quantified permissions are
not supported at all (@sec:beyond-fragment), so an index-based loop over an array
— which needs #vi[`forall i :: acc(a[i].f)`] to say what it holds — is out of
reach for a reason that is not about loops either. And termination is not checked:
#vi[`decreases`] is ignored and the guarantee is partial correctness, matching
Silicon's default.

#para[What we record] A loop that cannot be verified fails at a named obligation
in a named block, with the cut already performed: the invariant's exhale, the
havoc and the rebuilt entry heap have all happened, and the state at the failure
is the state of an arbitrary iteration. Nothing about the loop was approximated to
get there — what was missing was a decision procedure for the goal, and the goal
is still in the state to be handed to one.
