#import "../macros.typ": *

// The chapter is split one file per section, under `chapters/04/`.

= VMIR and Helium <sec:implementation>

Guided by the minimal feature set established in the previous chapter, we now present the concrete design of VMIR and its verification pipeline within Helium.

The presentation is incremental: each section admits one further class of Viper construct from our target fragment, details its VMIR encoding, and explains the strategy Helium uses to verify it. Most sections close with a comparison to Silicon, highlighting where the two designs diverge and what trade-offs those divergences introduce.

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
consequences for verification. @sec:impl-functions then encodes functions
and their contracts, and separates the verification paths for the recursive
and heap-dependent cases.

Finally, @sec:impl-pipeline turns from the individual construct to the whole
VMIR program, and states which of its declarations Helium verifies, in what
order, and what each one leaves for the units that follow.

#include "04/01-execution-model.typ"
#include "04/02-the-heap.typ"
#include "04/03-predicates.typ"
#include "04/04-adts.typ"
#include "04/05-methods.typ"
#include "04/06-control-flow.typ"
#include "04/07-functions.typ"
#include "04/08-pipeline.typ"
