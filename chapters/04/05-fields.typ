#import "../../macros.typ": *

== Fields <sec:impl-fields>

The first of Viper's two ways of declaring something a program can hold
permission to is also the smaller one. A field declaration is lowered to a unary
function from a receiver to the location of that receiver's field. Prusti emits
one field per _primitive type_ and never per Rust field, so one declaration,
below, is where every value of that type in the whole encoding is stored.

#lowering(caption: [A field declaration becomes a location function.], label: "lst:field-decl")[```viper
field f: Int
```][```vmir
function f(e0: Ref)
  : &[f] Int @ 1/1
```]

The declaration fixes all three components of the location type (@sec:impl-heap):
the stored type is the field's own, the bound is #vm[`1/1`] matching
#vi[`write`], and the group is the field's name. The last of these is the
load-bearing one. A group per declaration is a partition per declaration, so
chunks of two distinct fields can never be brought to one location and nothing
has to be stated to rule it out. In a Prusti encoding that partitioning is
coarser than it looks — every Rust value of that primitive type, anywhere in
the program, shares one partition — which is why the aliasing question below
is one the design has to answer rather than one the frontend arranges away.

The mapping from a receiver to a location is not injective. The function is
declared and nothing else: no body, no axiom, no postcondition. This is where our verifier diverges from field
semantics in Silicon or Carbon. The other two verifiers make fields an injective
mapping implicitly. It comes down to how they state the non-aliasing axiom: they
talk directly about the receivers and not about the locations.

Does the missing injectivity matter? Not in the usual direction, which is
concluding that two receivers are distinct.

#viper(caption: [Distinctness of receivers, derived without injectivity.], label: "lst:field-distinct")[```viper
inhale acc(x.f, write) && acc(y.f, write)
assert x != y
```]

The pair axiom of @sec:impl-heap gives
#vm[`f(x) == f(y) ==> write + write <= write`], whose
right-hand side constant-folds to false, so the two locations are distinct. The
contrapositive of congruence — from #vm[`g(a) != g(b)`] conclude #vi[`a != b`] —
narrows that to #vi[`x != y`]. Neither step needs the location function to be
injective, which is why this direction is not missed.

Injectivity is the converse: concluding #vi[`x == y`] from an equality between
their locations. A program reaches for it when it learns an aliasing fact by
_counting permission_ rather than by being told it.

#viper(caption: [The shape that needs an injective field mapping.], label: "lst:field-inj-need")[```viper
inhale acc(x.f, 1/2) && acc(y.f, 1/2)
assume perm(x.f) == write
assert x == y
```]

The assertion holds in Viper: what is genuinely held at #vi[`x`]'s location is
$1\/2 + ternary(ell_x = ell_y, 1\/2, 0)$, so the assumption can hold only where
the condition does. Our verifier rejects it, and injectivity is only the second of
two missing steps — concluding that the two locations coincide from the sum
reaching #vm[`1/1`] is arithmetic driving a case analysis on a condition the
program never mentions, which is exactly the general-prover reasoning the core is
not built to do (@sec:impl-proving).

Were the fact wanted, it could be stated by declaring an inverse beside the
location function.

#lvmir(caption: [How injectivity of a field mapping would be stated.], label: "lst:field-inv")[```lvmir
function f(e0: Ref): &[f] T @ 1/1
  ensures e0 == f_inv(result)

function f_inv(e0: &[f] T @ 1/1): Ref
```]

From #vm[`f(x) == f(y)`], congruence gives #vm[`f_inv(f(x)) == f_inv(f(y))`], and
the postcondition rewrites each side to its own receiver.

The case for stating it is stronger in VMIR than in Viper. A Viper program can
name a location only by writing a field access, so a receiver is always at hand;
VMIR locations are ordinary values (@sec:impl-heap) that can be computed, passed
and compared directly, and a frontend reasoning about them that way has no other
route back to the receivers. No such frontend is in view here. Prusti's encoding
never asks for two references to be equated, let alone by counting permission, so
no obligation in the corpus of @sec:prusti-needs depends on a field mapping being
injective, and the declaration stays bare.

That is the whole of what a field _is_. What a program does with one — take
permission to it, read it, write it — is not field-specific at all, and is the
subject of @sec:impl-heap-interaction; predicates, which need those operations to
state their bodies with, follow in @sec:impl-predicates.
