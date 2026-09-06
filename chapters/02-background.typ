#import "../macros.typ": *
// The chapter is split one file per section, under `chapters/02/`.


= Background <sec:background>
In this chapter we give relevant background on the Viper verification infrastructure.
We take a closer look at the Viper verification language, the frontends that encode
high-level language programs into Viper, focusing on Prusti, and the execution
backends, focusing on Silicon.

We also discuss equality reasoning in the context of symbolic execution, and how e-graphs
can be used to encode and discharge obligations that arise during symbolic execution of
a program.

Last, we discuss the related work: Viper's other backend, another attempt to
make symbolic execution of Viper programs faster that modified Silicon,
the libraries that implement equality saturation, and the other verifiers that
take Rust as their source language.

#include "02/01-viper.typ"
#include "02/02-silicon.typ"
#include "02/03-prusti.typ"
#include "02/04-equality.typ"
#include "02/05-related-work.typ"
