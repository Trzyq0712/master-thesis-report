#import "../macros.typ": *

// The chapter is split one file per section, under `chapters/04/`.

= VMIR and Helium <sec:implementation>
We present the design and implementation of Viper Mid-Level Intermediate Representation (VMIR) and Helium verifier in this chapter.
Sections increase in complexity, each building on the ones before it, and each
introduces only the VMIR constructs it needs rather than assuming the
representation up front.

We start by executing the simplest programs a verifier can process, and by
explaining the mechanism by which the verifier discharges the obligations
they raise.

Afterwards, we introduce the symbolic heap and explain how we handle heap
constructs from Viper like fields and predicates. We then proceed
with how user-defined ADTs and domains are encoded and reasoned about.

The later sections are dedicated to methods. These explain what a contract
becomes, how a body is verified against one, and what a call site executes,
and then how the verifier handles bodies with control flow.

// #include "04/01-vmir.typ"
#include "04/02-execution-model.typ"
// #include "04/03-discharging.typ"
#include "04/04-the-heap.typ"
#include "04/05-predicates.typ"
// #include "04/05-fields.typ"
#include "04/06-adts.typ"
#include "04/07-heap-interaction.typ"
#include "04/08-methods.typ"
#include "04/10-control-flow.typ"
// #include "04/11-functions.typ"
// #include "04/12-loops.typ"
// #include "04/13-putting-together.typ"
// #include "04/14-beyond-fragment.typ"
