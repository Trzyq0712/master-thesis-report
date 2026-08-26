#import "../../macros.typ": *

== Functions <sec:impl-functions>

Viper's functions are pure, and in VMIR they are pure in a stronger sense: a
function takes values and returns one, and no function application mentions a
heap. That is a claim which has to be justified, because a Viper function may demand
permission and read through it — #vi[`snap_Account`] of @lst:example-viper is
the shape every Prusti encoding is built from. This section is about how a
function that reads the heap becomes one that does not, and about what a call site
gets to know when it applies one.

The mechanism for a heap-dependent function is the snapshot of
@sec:impl-predicates, applied to a precondition. A function whose #vi[`requires`]
contains an #vi[`acc`] has that precondition lowered to a self-framed resource,
and the function gains a trailing parameter: the snapshot of that resource. Its
body then opens by widening the snapshot back into a heap and reads from it.

#lowering(caption: [A heap-dependent function takes its precondition's snapshot.], label: "lst:heapdep-fn")[```viper
function snap_i32(self: Ref)
  : i32
  requires acc(own_i32(self), write)
{
  (unfolding acc(own_i32(self), write)
    in self.val_i32)
}
```][```vmir
resource snap_i32#requires(e0: Ref) {
  e1: &[own_i32] own_i32@snap @ *
     := own_i32@loc(e0)
  h0 := empty + e1 @ wildcard with self
  result: (h0, true)
}

function snap_i32(e0: Ref,
    e1: snap_i32#requires@snap)
  -> i32
  requires snap_i32#requires(e0, e1)
{
  h0 := empty inhale
        snap_i32#requires(e0)
        @ wildcard with e1
  h1, e2 := h0
        - own_i32@loc(e0) @ wildcard
  h2 := h1 inhale own_i32(e0) @ wildcard
        with unwrap(e2)
  e3: &[val_i32] i32 @ 1/1
     := val_i32(e0)
  e4: i32 := *[h2] e3
  result: e4
}
```]

Everything in the body has appeared before, and no instruction in it is peculiar
to functions. The first line is a resource #vm[`inhale`] like any other
(#pararef(<para:impl-resource-ops>, [The resource operations])), bound to the
snapshot parameter rather than to #vm[`fresh`]: it walks the precondition's
footprint into an empty heap, giving every slot the value the snapshot records
there. That is what "widening a snapshot back into a heap" is — there is no
separate instruction for it, and the same line is what reconstructs a two-state
postcondition's pre-state (@sec:impl-calls). The two that follow are the unfold
pair of @sec:impl-predicates, and the read is @sec:impl-heap-interaction
unchanged. What is new is only that the heap the body works in is manufactured
from a parameter rather than inherited from a caller.

That a function body may inhale at all is worth a sentence, since a body has to be
deterministic — a function of its parameters, its snapshot and nothing else. The
rule that secures this is not "no inhale"; it is that no instruction in such a body
may create a value. #vm[`with fresh`] is what would violate it, and #vm[`with e1`]
does not: the values are the parameter's, projected. Two evaluations of the same
call therefore build the same terms, which is what the next listing turns on.

One detail in the resource is not cosmetic. Every permission in a function's
precondition footprint — and in its body — is weakened to a #vm[`wildcard`], which
is the read-only policy of
#pararef(<para:impl-readonly>, [Where wildcards come from]) applied at its two
sites. A function frames rather than consumes: it needs to know that _some_
permission is held so that the values it reads are stable, and it must not require
the amount a caller happens to have. What that weakening costs and buys is
@sec:impl-wildcards; what the rest of this section needs from it is only that a
wildcard demand is discharged by proving the location holds a positive share rather
than by comparing fractions.

At a call site the snapshot is built, and building it is where the precondition is
checked:

#vmir(caption: [Two calls of one heap-dependent function against one heap. #vi[`account_over_limit`] makes exactly this pair — two applications of #vi[`snap_RefImm`] to #vi[`_1p`], one per field it reads — in a single block.], label: "lst:heapdep-call")[```vmir
_, e2 := h0 exhale snap_i32#requires(e0) @ wildcard
e3: i32 := snap_i32(e0, e2)
_, e4 := h0 exhale snap_i32#requires(e0) @ wildcard
e5: i32 := snap_i32(e0, e4)
e6: Bool := e3 == e5
assert e6 [h0]
```]

The check is an #vm[`exhale`] of the precondition, and the blank binder is what
makes it a check rather than a payment. An exhale walks the footprint, proving
sufficiency at each slot, asserts the resource's boolean, and yields the snapshot
assembled from the values it read — and here only that second result is asked for.
The heap it would have produced is never built, which is precisely what "a
function frames rather than consumes" means: the caller keeps everything it held.

Nothing is skipped by not building it. Every obligation the walk raises is raised
either way; what an unrequested result buys is that the subtraction chain is not
materialised, and with it the wildcard arithmetic that would otherwise be left
sitting in the state — which is the frame-only case of @sec:impl-wildcards. This is the case @sec:impl-heap-interaction promised: a
blank binder is written by the translator and means something, so no later pass may
introduce one — blanking the heap of a genuine exhale would turn a consume into a
frame check.

The permission is #vm[`wildcard`] on both sides, and that is the same symmetry
seen from the two ends: the call site exhales the precondition at wildcard and
gets a snapshot, the body inhales the same resource at wildcard bound to that
snapshot. One resource, one permission mode, mirrored.

That the check happens here, and only here, is what makes the application itself
pure. #vm[`snap_i32(e0, e2)`] is an ordinary two-argument application with no heap in
sight, and everything the heap contributed to it is in #vm[`e2`].

It also makes the framing question trivial in the case that matters. The two
calls above read one heap and one resource, so they build the same snapshot term
— literally the same e-class — and the two applications are congruent. The
assertion that they agree is discharged by congruence, with no obligation raised
and no reasoning about what #vi[`snap_i32`] does. Silicon reaches the same conclusion
through the function's framing axiom and a solver query; here there is nothing to
query, because the two terms were never distinct.

A function may have no body at all, and then its
contract is all there is. Prusti's #vi[`generic_Account`] and #vi[`concrete_Account`]
(@lst:example-viper) are the canonical pair: no bodies, and postconditions saying
that the two are inverse and that a generic value's type tag is the concrete
one's.

Such a function exports one guarded fact, the shape of which is

$ f "#requires"(overline(x)) => f "#ensures"(overline(x), f(overline(x))) $

replayed at every occurrence of the application. For #vi[`generic_Account`]
the postcondition is an equality, so what an occurrence contributes is
#vi[`concrete_Account(generic_Account(a)) == a`] — and a fact of that shape is what the
reasoning core is best at. It is merged, congruence propagates it, and a
round-trip through the two functions collapses to the identity without any
obligation being raised.

The guard is not decoration. A fact from a postcondition holds only where the
precondition does, so it is stated as an implication and released only when the
antecedent is established. For a heap-free function that antecedent is the
lowered #vi[`requires`] boolean, made true at a call site by the assertion that
checks it. For a heap-dependent one it cannot be: the precondition also demands a
footprint, and so is not a function of the arguments and the snapshot alone. There
the antecedent is an opaque token over the precondition resource, which the
precondition exhale stamps exactly where its check passed.

#para[Recipes] <para:impl-recipes> A function _with_ a body is verified once, and
what verification
leaves behind is a _recipe_: the body captured as a sequence of pure steps over
the parameters, with every callee already resolved. At each occurrence of
#vm[`f(args)`] the recipe is replayed — the steps are rebuilt with the parameters
bound to the arguments — and the result is merged with the occurrence's class.
That is the definitional equation #vi[`f(args) == body`], installed lazily, one
occurrence at a time, as saturation encounters them.

Replaying rather than importing is the property that matters. A recipe adds terms
and never carries an e-class across: nothing that was merged while the body was
being verified is carried into a caller. This is not merely a performance concern. The
body is verified under its own precondition, so the merges it establishes are
conditional on that precondition, and importing them would let a caller that has
not established it inherit facts it has no right to. Rebuilding from the steps
means the caller derives whatever it needs itself, from what it can actually
establish.

The replay is gated the same way a postcondition fact is. The definitional union
fires only where a token for the same arguments is present — the marker that this
occurrence came from a genuine call rather than from a term some rule happened to
build — which keeps a function from being unfolded at an occurrence nobody wrote.
Silicon does the same thing with the same shape of trigger.

A resource is kept the same way, and by the same machinery: its footprint is two
recipes per slot and its body one more
(#pararef(<para:impl-slot-recipes>, [Slots and recipes])). The difference is only
what the recipe is replayed _into_ — a function's into an equation between an
application and its body, a resource's into chunks and an assertion about them.

Recursion is handled by unfolding exactly once. A recursive function's recipe
targets a _limited twin_ of itself at its in-cycle calls: an uninterpreted
function equal to the original at every occurrence, but with no unfold rule of its
own. Unfolding a recursive body therefore produces the twin at the smaller
arguments and stops. What still fires at the twin is the postcondition fact, and
that is what makes induction over a recursive call work at all — it is the only
thing the caller learns about the recursive occurrence, and it is precisely what
the function's contract promised.

A recipe is built by a backward closure: start from the result and
keep the steps it depends on. That is the right default — a body may compute
things it does not return, and replaying them at every occurrence would be waste —
and it is where finding four of @sec:impl-cfg comes from.

The tokens gating a callee's facts are emitted alongside the callee's application,
and their value is read by nothing. They are therefore unreachable from the
result, and the closure pruned them. The effect was silent and specific: a
resource replayed at a client rebuilt the callee's application _without_ its
token, so the callee stayed dormant at that occurrence for the rest of the
verification. Re-reading a field after a call went through such a resource — a
method's postcondition — and so two reads of a field nothing had touched came out
unrelated.

The fix is to treat a token as a root of the closure rather than as a dead step.
It applies to a resource's body boolean and not to the slot recipes, since a slot
resolves its inputs against the slot values built so far and pulling in a token
that mentions a later slot would reach past the end.

A function whose postcondition cannot be discharged is
reported at the assertion its own body raises, with the body's terms in the state
and the contract's occurrence intact. A call site whose precondition cannot be
established fails at the #vm[`snap`], naming the footprint slot it could not
prove a positive share for — and the application itself is still a well-formed
pure term, which is what would let a stronger procedure take the same obligation
from the same state.
