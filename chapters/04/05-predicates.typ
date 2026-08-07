#import "../../macros.typ": *

== Predicates <sec:impl-predicates>

#todo[
  Beat 2 is below; beat 1 prose and beat 3 are both missing.

  - Resource bodies evaluate to a pair of a heap and a value: the footprint
    they build, and the pure condition they assert.
  - Two derived members, neither of which appears in the source: the snapshot
    type and the location function. Explain the `@` notation here.
  - Snapshot slots are `Option`-typed because a slot is present-or-absent;
    `fold` packs `present ? Some(v) : None`. One `acc` in the body gives one
    slot.
  - Abstract (bodyless) predicates get an opaque domain instead — exactly
    `p_Param` in the worked example.

  #para[Run-in headings] Resource bodies / Derived members / Snapshots /
  Abstract predicates
]

#viper[```viper
predicate gt(x: Ref, b: Int) {
  acc(x.f) && x.f > b
}
```]

#vmir[```vmir
resource gt(e0: Ref, e1: Int) {
  e2: &[f] Int @ 1/1 := f(e0)
  h0 := empty + acc(e2, 1/1)
  e3: Int := *[h0] e2
  e4: Bool := e3 > e1
  h0, e4
}
```]

Each resource also has two implicitly generated VMIR members, a snapshot type
and the location function.

These are implicitly defined (the `@` syntax). The snapshot is syntactically defined
by the shape of the predicate -- every acc expression corresponds to an optional value in a snapshot.

#vmir[```vmir
adt gt@snap { #0(Option[Int]) }

function gt@addr(e0: Ref, e1: Int): &[gt] gt@snap @ *
```]

#note[
  `gt@addr` does not match the implementation, which names the derived location
  function after the resource itself (`gt`), and a real translation dump calls
  it as `gt(..)`. Either adopt `@addr` as deliberate notation for "implicit
  member" and say so, or drop it for consistency with `function f(..)` in
  Fields. The `@snap` spelling does match the implementation.
]
