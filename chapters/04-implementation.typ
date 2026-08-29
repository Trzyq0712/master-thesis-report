#import "../macros.typ": *

// The chapter is split one file per section, under `chapters/04/`.

= VMIR and Helium <sec:implementation>
In this chapter we present the design of VMIR and its verification in Helium.
The presentation is incremental: each section admits one further class of Viper
construct, gives its VMIR encoding, and then the strategy Helium uses to verify
it. Each section closes with a comparison to Silicon, naming where the two
designs diverge and what the divergence costs.

@sec:impl-execution starts from the smallest program a verifier can process, a
stream of value-only instructions, and defines the mechanism by which Helium
discharges an obligation. In @sec:impl-heap we admit the heap, giving the
location types that represent fields, the heap representation Helium executes
against, and the instructions that manipulate it. @sec:impl-predicates
generalises self-framing assertions into VMIR resources, from which the
predicate operations follow. We then cover user-defined data in @sec:impl-data:
ADTs, domains and their axioms, and the quantifiers those axioms need.

The last three sections concern Viper's two callable constructs. In
@sec:impl-methods we verify straight-line method bodies, covering contract
translation, body verification and calls. @sec:impl-cfg lifts the straight-line
restriction by partitioning bodies into basic blocks, and gives the
consequences for verification. Finally, @sec:impl-functions encodes functions
and their contracts, and separates the verification paths for the recursive
and heap-dependent cases.

#include "04/01-execution-model.typ"
#include "04/02-the-heap.typ"
#include "04/03-predicates.typ"
#include "04/04-adts.typ"
#include "04/05-methods.typ"
#include "04/06-control-flow.typ"
#include "04/07-functions.typ"
