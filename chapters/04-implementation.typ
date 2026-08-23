#import "../macros.typ": *

// The chapter is split one file per section, under `chapters/04/`.

= VMIR and Helium <sec:implementation>
In this chapter we present the design and implementation of the new IR and the
verifier. The components are presented in the order of increasing complexity,
with the later ones building on top of the earlier.

We start with the new Viper Mid-level Intermediate
Representation (VMIR). We introduce the syntax and semantics, as well as motivate
the design decisions taken. We then
describe how the new verifier -- Helium -- executes
simplest of programs consisting of heap independent statements. We follow that
by explaining in closer detail the mechanisms by which the verifier
discharges obligations.

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

// This chapter builds the backend one construct at a time, checking each against
// the program presented in @sec:example. It opens with a short look at VMIR
// itself, enough that the listings which follow read without a preamble, and then
// starts from the smallest thing a verifier can do: execute a heapless instruction
// stream and discharge the obligations it raises — the prover's tiers, and the
// rewrite rules they run underneath every one of them. The symbolic heap comes
// next, without conditional structure at first, so that its operations can be
// stated on their own; then fields, the instructions that move permission; then
// datatypes, whose rules are what a fold and its unfold cancel by; then
// predicates, which is where that cancellation is put to use. Domains and the
// quantified axioms they carry close out the values a program can build, and only
// then does the chapter turn to calls, method bodies, and control flow — which is
// what forces two heaps to be reconciled. Wildcard permissions, functions and
// loops close the chapter, each needing the ones before it and nothing after.
//
// The order is deliberate in one further respect. Each section says what its
// construct costs the verifier and, where the mechanism differs from Silicon's,
// where the difference lies. The claim the chapter is accumulating is not that any
// single mechanism is novel, but that a particular set of them composes into a
// verifier on which the great majority of a Prusti program's obligations are true by
// construction rather than by proof — and @sec:impl-together is where that claim is
// checked against the whole of the guiding example.

#include "04/01-vmir.typ"
#include "04/02-execution-model.typ"
#include "04/03-discharging.typ"
#include "04/04-symbolic-heap.typ"
#include "04/05-fields.typ"
#include "04/06-heap-interaction.typ"
#include "04/07-adts.typ"
#include "04/08-predicates.typ"
#include "04/09-domains.typ"
#include "04/10-quantifiers.typ"
#include "04/11-calling-methods.typ"
#include "04/12-verifying-methods.typ"
#include "04/13-control-flow.typ"
#include "04/14-wildcards.typ"
#include "04/15-functions.typ"
#include "04/16-loops.typ"
#include "04/17-putting-together.typ"
#include "04/18-beyond-fragment.typ"
