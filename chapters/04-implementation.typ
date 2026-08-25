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

The later couple of sections are dedicated to methods. These explain
how the new infrastructure handles method calls and verifies bodies
with control flow. To complete the picture, we then describe calling and
verification of functions.

At the end of the chapter, we put all the components together and explain
how they work together to verify a complete user specification-free
Prusti-generated program.


// #include "04/01-vmir.typ"
#include "04/02-execution-model.typ"
// #include "04/03-discharging.typ"
#include "04/04-the-heap.typ"
#include "04/05-predicates.typ"
// #include "04/05-fields.typ"
#include "04/06-heap-interaction.typ"
#include "04/07-adts.typ"
#include "04/08-domains.typ"
#include "04/09-quantifiers.typ"
#include "04/10-calling-methods.typ"
#include "04/11-verifying-methods.typ"
#include "04/12-control-flow.typ"
#include "04/13-functions.typ"
#include "04/14-loops.typ"
#include "04/15-putting-together.typ"
#include "04/16-beyond-fragment.typ"
