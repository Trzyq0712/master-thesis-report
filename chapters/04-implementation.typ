#import "../macros.typ": *

// The chapter is split one file per section, under `chapters/04/`.

= VMIR and Helium <sec:implementation>
We present the design and implementation of Viper Mid-Level Intermediate
Representation (VMIR) and the Helium verifier in this chapter.
Sections increase in complexity, each building on the ones before it, and each
introduces only the VMIR constructs it needs rather than assuming the
representation up front. They share a shape. A section states the Viper
constructs it covers and what VMIR makes of them, works through how Helium
executes the result, and, where Silicon does the same job by another route,
closes with a subsection comparing the two.

@sec:impl-execution executes the simplest programs a verifier can process, a
stream of value-only instructions, and states the mechanism by which Helium
discharges the obligations they raise. In @sec:impl-heap we add the heap, where
a field access becomes a location, a value like any other.

@sec:impl-predicates covers predicates, and with them the resource: VMIR's
generalisation of the self-framing assertion a predicate is. A method contract
and a function precondition have the same shape, so one construct carries all
three. @sec:impl-data turns to user-defined data, where an #vi[`adt`] and a
#vi[`domain`] declare new types and a #vm[`forall`] instruction carries a
quantified axiom.

The last three sections are about the units a program is written in. In
@sec:impl-methods we describe what a method contract becomes and what a call
site executes in place of a body. @sec:impl-cfg lifts the restriction to
straight-line bodies, dividing a body into basic blocks and reconciling their
heaps at a join. @sec:impl-functions covers functions and what one exports to
its callers.

#include "04/01-execution-model.typ"
#include "04/02-the-heap.typ"
#include "04/03-predicates.typ"
#include "04/04-adts.typ"
#include "04/05-methods.typ"
#include "04/06-control-flow.typ"
#include "04/07-functions.typ"
