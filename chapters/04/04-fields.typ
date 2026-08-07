#import "../../macros.typ": *

== Fields <sec:impl-fields>

Fields are the first and simplest producer of the locations of @sec:impl-heap.
A field declaration is lowered to a unary function from a receiver to the
location of that receiver's field.

#lowering(caption: [A field declaration becomes a location function.], label: "lst:field-decl")[```viper
field f: Int
```][```vmir
function f(e0: Ref): &[f] Int @ 1/1
```]

The three components of the resulting location type are fixed by the
declaration. The stored type is the field's own type, #vm[`Int`] here. The
permission bound is #vm[`1/1`], matching Viper's #vi[`write`]: a field location
may never hold more than full permission. The group is the field's name, so every
field declaration in the program gets a partition of the symbolic heap to
itself, and distinct fields are non-aliasing by construction.

#todo[
  Beat 3 is missing: what the verifier actually does at a read and at a write.
  Resolve the location to an e-class, find the chunk, check sufficiency, then
  read or replace the value. Cross-reference @sec:impl-heap rather than
  restating it.
]
