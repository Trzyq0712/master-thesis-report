#import "../macros.typ": *

= Background <sec:background>
== Automated Program Verification with _Viper_
=== Symbolic Execution

== The _Prusti_ Verification Frontend

== Equality Reasoning

Equality reasoning decides whether an equality follows from a set of assumed
equalities. Given $x = y$ and $f(y) = z$, does $f(x) = z$ follow?

Equality is reflexive, symmetric and transitive, so the assumptions partition
terms into equivalence classes, and two terms are equal exactly when they share
a class. The rule that matters is _congruence_: if $x = y$ then $f(x) = f(y)$.
Congruence ties the classes to the structure of terms. Merging two classes can
make other terms congruent, forcing further merges. For example, if $f(x) = z$
and $f(y) = w$, then merging the classes of $x$ and $y$ will consequently merge
the classes of $z$ and $w$. This process continues until no further merges are
possible -- a fixpoint.

Core proofs consist of obligations of this shape. A heap location is denoted by
a term, and the same location may be denoted by many syntactically distinct terms during a
symbolic execution. Establishing that a permission is held where the program
accesses memory means establishing that two such terms are equal. Permission
amounts behave the same way: a caller passing a fraction $p$ to a callee retains
$1 - p$, and when the callee returns it the caller must again establish full
permission, $(1 - p) + p = 1$.

- Equivalence classes of expressions
- Representing equivalent expressions via e-graphs
=== _egg_ E-Graph and Saturation Engine

== Related Work
@perf-impr
