#import "../../macros.typ": *

== Execution Model

#todo[
  Beat 3 is here already in spirit; make the structure explicit.

  #para[Run-in headings] Symbolic state — the e-graph *is* the state, SSA
  temporaries are e-classes / Path conditions — cubes of branch
  literals / Joins — what survives a merge / The reasoning core — congruence
  and constant folding, always on
]

The execution model of the new Verifier is strongly based off of the
symbolic execution model of Silicon. The main difference is that in this new
verifier, it is us who is responsible for managing the symbolic state, rather
than Z3. On one hand this means that there is a lot more bookkeeping we have to do, but
on the other hand, it means we have a lot more control over the symbolic state,
giving us the opportunity to optimize the process for the common case.

#viper[```viper
var x: Bool
var y: Bool := x ? false : true
assert y == !x
```]

While this example is actually a case where we need to do functional reasoning,
we can still use it to illustrate the execution model. In this case, we can
actually coincidentally discharge this due to structure, but this will not hold
in general. Let us now look how this method will look when translated down to VMIR.

#vmir[```vmir
e0: Bool := fresh             // x == e0
e1: Bool := e0 ? false : true // y == e1
e2: Bool := e0 ? false : true // !x is desugared to a ternary
e3: Bool := e1 == e2          // y == !x
assert e3
```]

The verifier will execute this method line by line, and at each step update the symbolic state.
When it eventually reaches the assertion, it will check if the obligation is satisfied.
More concretely, it will verify that the value #vm[e3] is in the same e-class as #vm[true].
