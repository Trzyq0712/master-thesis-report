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

The later sections are dedicated to methods, control flow, and functions. These
explain what a contract becomes, how a body is verified against one, and what a
call site executes, how a branching body is divided into basic blocks and its
heaps reconciled at a join, and what a function exports to its callers.

#include "04/01-execution-model.typ"
#include "04/02-the-heap.typ"
#include "04/03-predicates.typ"
#include "04/04-adts.typ"
#include "04/05-methods.typ"
#include "04/06-control-flow.typ"
#include "04/07-functions.typ"
