#import "../../macros.typ": *

== Fields <sec:impl-fields>

The first of Viper's two ways of declaring something a program can hold
permission to is also the smaller one. A field declaration is lowered to a unary
function from a receiver to the location of that receiver's field.

#lowering(caption: [A field declaration becomes a location function.], label: "lst:field-decl")[```viper
field f: Int
```][```vmir
function f(e0: Ref): &[f] Int @ 1/1
```]

The declaration fixes all three components of the location type (@sec:impl-heap):
the stored type is the field's own, the bound is #vm[`1/1`] matching
#vi[`write`], and the group is the field's name. The last of these is the
load-bearing one. A group per declaration is a partition per declaration, so
chunks of two distinct fields can never be brought to one location and nothing
has to be stated to rule it out.

The function is declared and nothing else: no body, and no axiom alongside it —
not even that it is injective. Distinctness of two receivers, where a program
needs it, is derived from the permission they hold rather than assumed of the
function, which is @sec:impl-heap's account and not something a field declaration
adds to.

That is the whole of what a field _is_. What a program does with one — take
permission to it, read it, write it — is not field-specific at all, and is the
subject of @sec:impl-heap-interaction; predicates, which need those operations to
state their bodies with, follow in @sec:impl-predicates.
