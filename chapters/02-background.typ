#import "../macros.typ": *
#import "../figures/egraph-congruence.typ": egraph-congruence

= Background <sec:background>
In this chapter we give relevant background on the Viper verification infrastructure.
We take a closer look at the Viper verification language, the frontends that encode
high-level language programs into Viper, focusing on Prusti, and the execution
backends, focusing on Silicon.

We also discuss equality reasoning in the context of symbolic execution, and how e-graphs
can be used to encode and discharge obligations that arise during symbolic execution of
a program.

Last, we discuss the related work: the earlier attempts to make symbolic
execution of Viper programs faster, the provers our reasoning engine descends
from, and the other verifiers that take Rust as their source language.

== Automated Program Verification with Viper <sec:bg-viper>

Unlike software testing, which checks program behavior against concrete inputs, deductive program verification aims to formally prove that a program satisfies its specification for all possible inputs.
Viper @viper is a verification infrastructure designed to facilitate this process through flexible, permission-based reasoning. It consists of three parts:

- an intermediate verification language, in which a program carries its formal
  specification as part of its text,
- verification backends, which prove that a program in that language satisfies
  its specification,
- language-specific frontends, which translate a program written in a
  high-level language into the intermediate language.

We present Viper's constructs in the order our implementation presents
them, paired with examples we return to later. Viper programs consist of
fields, methods, functions, predicates and domains.

Two further features are outside the scope of this thesis. A magic wand describes a partial data structure as a resource that yields one assertion when combined with another, and quantified permissions state a permission for every element of an unbounded set of locations at once. Neither is covered here nor supported by the verifier we present.

#para[Statements] Viper programs are composed of statements and expressions. Basic statements
include variable declarations, assignments, and structural control flow.
Verification-specific statements include `assert` (which requires the verifier
to prove a property holds at that point), and `assume` (which adds a property
to the known state without proof).

#no-numbers[```viper
var a: Int
assume a == 42
assert a == 42
```]

#para[The heap and fields] Viper uses the `Ref` type for heap-allocated objects with globally declared fields. A field declaration is global, so every field is nominally accessible through every reference: given #vi[`x: Ref`] and the two declarations below, both #vi[`x.value`] and #vi[`x.next`] are expressions the program may write.

#no-numbers[```viper
field value: Int
field next: Ref
```]

Whether a program may read or write #vi[`x.value`] is decided by permissions. Viper treats a field of a reference as a resource, and the expression #vi[`acc(x.value)`] denotes the permission to access it. Permissions are fractional. The amount #vi[`write`], equivalently #vi[`1/1`], is the maximum any state may hold, and it grants both reading and writing. Any amount above zero grants reading alone. A fraction is therefore what lets one part of a program lend read access while retaining the rest, and #vi[`acc(x.value, 1/2)`] states that half of the permission to #vi[`x.value`] is held.

Permissions move between states through two statements. The #vi[`inhale`] statement adds permissions and assumes properties, and #vi[`exhale`] asserts that the stated permissions are held, then removes them.

#no-numbers[```viper
var x: Ref
inhale acc(x.value, write)
x.value := 42
exhale acc(x.value, 1/2)
assert x.value > 0
```]

After the #vi[`exhale`], half of the permission remains, which is enough to read #vi[`x.value`] but no longer enough to assign to it.

#para[Separating conjunction] The conjunction #vi[`&&`] acts as a separating conjunction when its operands are permission assertions: it sums their amounts rather than requiring both to hold independently. The assertion #vi[`acc(x.f, 1/2) && acc(x.f, 1/2)`] is therefore equivalent to #vi[`acc(x.f, write)`], and #vi[`acc(x.f, write) && acc(y.f, write)`] implies that #vi[`x`] and #vi[`y`] are distinct, because the two amounts would otherwise sum past the maximum.

The permission model is modular for this reason. A method that holds full permission to a location knows that no other part of the program holds any, so it may reason about that location without considering aliases.

#para[Predicates] Predicates are packed, named permission assertions. A predicate declaration bundles a set of permissions with logical constraints on the values they guard. Predicate bodies may be recursive, which is what allows a finite assertion to describe an unbounded structure such as a list or a tree. One instance of the predicate below carries the permissions to every node reachable from #vi[`this`].

#no-numbers[```viper
field val: Int
field next: Ref

predicate LinkedList(this: Ref) {
  acc(this.val, write) &&
  acc(this.next, write) &&
  this.val >= 0 &&
  (this.next != null ==> acc(LinkedList(this.next), write))
}
```]

A predicate body must be _self-framing_: it grants the permissions its own heap
reads go through, which is what fixes the order of its conjuncts. The body above
reads #vi[`this.val`] and #vi[`this.next`] only after the #vi[`acc`] that grants
each.

Two statements exchange a predicate instance for the resources it packs. The #vi[`unfold`] statement requires the instance, consumes it, and produces the permissions and properties of the body. The #vi[`fold`] statement is its inverse: it requires everything the body states and produces the instance. Reading #vi[`this.val`] of some #vi[`acc(LinkedList(this))`] therefore takes an #vi[`unfold LinkedList(this)`] first, to exchange the predicate instance for its body.

#para[Data types] Alongside built-in primitive types, Viper supports complex data types. Algebraic
data types allow defining structural types with named constructors, and Viper
derives the destructors and the discriminator of each variant from the
declaration alone, so the datatype below also provides #vi[`isCircle`] and the
destructor #vi[`r`].

#no-numbers[```viper
adt Shape {
  Circle(r: Int)
  Square(s: Int)
}
```]

Domains are the more general mechanism. A domain declares a type, together with
functions over that type. Domain functions are uninterpreted: they carry no body
and no contract, so the verifier knows only that equal arguments produce equal
results. Their meaning comes entirely from the axioms declared alongside them,
which are assumed to hold everywhere in the program.

#no-numbers[```viper
domain Box {
  function box(v: Int): Box
  function unbox(w: Box): Int
}
```]

#para[Axioms and quantifiers] An axiom is a closed assertion the verifier assumes everywhere in the program, and a domain gives its functions meaning through axioms. A single axiom constrains a single case, so stating a property of every value of a type takes a quantifier. Viper offers the universal quantifier #vi[`forall`] and the existential quantifier #vi[`exists`]. The axiom below quantifies over every integer, and it makes #vi[`box`] and #vi[`unbox`] mutual inverses: unboxing a boxed integer yields the integer it started from.

#no-numbers[```viper
axiom round_trip {
  forall v: Int :: { box(v) }
    unbox(box(v)) == v
}
```]

The term in curly braces is a _trigger_. A backend instantiates the quantifier for the values that make some term in the program match it, so this axiom is available exactly where the program boxes an integer. Viper infers a trigger where the source omits one.

An instance is released under a guard, because a quantifier need not be true
where its trigger matches. A trigger is matched against the whole e-graph, and
nothing about a term matching one says the quantifier holds at the point that
term was built. The program below assumes a quantifier under an implication and then asks for
an instance on either side of the assumption.

#no-numbers[```viper
var b: Bool
assume b ==> forall v: Int :: {box(v)}
  unbox(box(v)) == v

assert unbox(box(3)) == 3   // triggers forall, but fails assertion
assume b
assert unbox(box(3)) == 3   // succeeds
```]

Both assertions build #vi[`box(3)`], so the trigger matches at the first one
already. What a match adds is the implication

$ q ==> "body" $

where $q$ is the quantifier itself, so an instance contributes its body once $q$
is #vm[`true`]. At the first assertion only the assumed implication is known,
$q$ is open, and the goal stands unproven. The #vi[`assume`] between the two
puts #vi[`b`] at #vm[`true`] and $q$ with it, and the instance already in the
graph closes the second assertion. Matching a quantifier whose truth is open is
therefore sound, and the verifier is free to match one on a path it is still
exploring, or one it is checking rather than using. A precondition token the
body carries is subject to the same guard, so a callee's facts arrive with the
quantifier's truth.

An algebraic data type is a domain with a fixed set of axioms. Before any
backend sees the program, Viper rewrites the declaration into a domain whose
functions are the constructors, one destructor per constructor argument, and a
#vi[`tag`] function giving the index of the constructor that built a value. It
then generates three families of axioms, each a quantifier triggered on the
term it constrains:

/ Destruction: for every constructor, a destructor applied to a construction
  returns the argument it was given, $D_i (C(p_1, ..., p_n)) = p_i$.
/ Tagging: for every constructor, the tag of a construction is that
  constructor's index, $"tag"(C(p_1, ..., p_n)) = i$.
/ Exclusivity: once per datatype, every value of the type equals a construction
  by one of the constructors,
  $t = C_1 (D_11 (t), ...) or ... or t = C_n (D_(n 1)(t), ...)$.

The first two answer questions about a value some constructor visibly built. The
third lets a verifier reason about a value none did, and it makes a case
analysis over the variants complete.

#para[Methods] Methods are imperative code blocks serving as the fundamental unit of verification in Viper. They are annotated with contracts: `requires` for preconditions and `ensures` for postconditions. Methods can modify the heap.

#no-numbers[```viper
field val: Int

method bump(c: Ref)
  requires acc(c.val, write)
  ensures acc(c.val, write)
{
  c.val := c.val + 1
}
```]

A call transfers permission in both directions, and the two sides of the call see mirror images of the same transfer. On entry the callee inhales its precondition and on return it exhales its postcondition. At the call site the caller exhales the precondition, losing the permissions it names, and inhales the postcondition once the call returns.

Methods enable modular reasoning. A caller learns nothing about a callee beyond what the callee's contract states, so the call below fails to verify: the contract of #vi[`bump`] returns the permission to #vi[`x.val`] without saying how the value changed.

#no-numbers[```viper
method client(x: Ref)
  requires acc(x.val, write)
{
  x.val := 42
  bump(x)
  assert x.val == 43 // fails
}
```]

#para[Control flow] A method body directs its execution with three constructs: #vi[`if`], #vi[`while`], and #vi[`goto`] paired with #vi[`label`]. @lst:bg-control uses all three.

#viper(
  caption: [A method clamping an integer into the range from zero to ten,
    written with a conditional, a loop and a jump.],
  label: "lst:bg-control",
  placement: auto,
)[```viper
method clamp(x: Int) returns (r: Int)
  ensures 0 <= r && r <= 10
{
  r := x
  if (r < 0) {
    r := 0
    goto done
  }
  while (10 < r)
    invariant 0 <= r
  {
    r := r - 1
  }
  label done
}
```]

A loop is verified against its invariant. The verifier proves the invariant on entry, proves that one arbitrary iteration preserves it, and then continues after the loop knowing the invariant and the negated loop condition. The pairing of #vi[`goto`] and #vi[`label`] turns a body into a control-flow graph (CFG) of arbitrary shape, so a backend cannot assume that control flow is structured.

#para[Functions] Functions are parameterized, side-effect-free expressions. Like methods, they
are annotated with contracts, but their body is a single expression and thus
cannot modify the heap.

#no-numbers[```viper
function div(s: Int, n: Int): Int
  requires n != 0
{
  s / n
}
```]

The body gives an application its meaning: wherever the function is applied, the
definition unfolds to it, so a caller of #vi[`div(a, b)`] learns
#vi[`div(a, b) == a \ b`]. The precondition makes that body well-defined, and it
has to hold wherever the function is applied. A declaration with no body leaves
its application opaque, and a caller then learns only what the contract states.

A function carries an #vi[`ensures`] clause for three reasons. With no body the
clause is the only thing a caller can rely on, as the bodyless declaration
below shows.
With a body it can state a property that holds but is not apparent from the body
itself. For a recursive function it serves as the induction hypothesis, since
the body cannot unfold into itself.

#no-numbers[```viper
function abs(x: Int): Int
  ensures result >= 0
```]

Function definitions may be recursive, and a function may read the heap. A function that does so states the permissions it needs in its precondition, so its result depends on the heap as well as on its arguments. The function below sums a linked list. The expression #vi[`unfolding`] is the counterpart of the #vi[`unfold`] statement: it exchanges the predicate instance for its body within the expression that follows.

#no-numbers[```viper
function sum(this: Ref): Int
  requires acc(LinkedList(this), write)
{
  unfolding acc(LinkedList(this), write) in
    this.val + (this.next == null ? 0 : sum(this.next))
}
```]

A recursive definition cannot be unfolded indefinitely, since each unfolding
exposes the recursive application again. A verifier therefore bounds the
unfolding, and @sec:bg-silicon describes how Silicon does so.

== Verification Frontends and Prusti <sec:bg-prusti>

Viper's intermediate language is a target rather than a source. A frontend takes a program in some high-level language and produces a Viper program whose verification establishes the property the frontend cares about. Prusti @prusti does this for Rust, Nagini @nagini for Python, Gobra @gobra for Go, and VerCors @vercors for Java. What they share is the hard part of the translation: each has to express its source language's memory model in Viper permissions, so that holding a permission in the encoded program corresponds to being allowed to touch the memory in the original one.

The obligations a frontend produces fall into two groups, and the split is by who writes them. A _functional specification_ is written by a person and states what the program computes. It is an arbitrary first-order assertion, and proving one may take arithmetic, quantifiers and rich theories. The _core proof_ is generated by the frontend, and it is the set of obligations that result from encoding the source language's memory and ownership semantics: that a permission is held wherever memory is accessed, that ownership transfers correctly across a call boundary, and that a structure's invariant is re-established before it is handed on. The distinction is visible in what Prusti does with an unannotated program: it still emits the full encoding of the obligations that follow from Rust's memory model, and there is simply no functional specification alongside them.

Rust makes the core proof interesting to us. Its type system enforces that a value is either shared or mutable but never both, and the borrow checker establishes this statically, before verification begins. Prusti therefore derives the whole core proof from the program text and Rust's semantics @prusti-oopsla, with no annotation from the programmer. Python, Go and Java carry no such ownership discipline, so a Nagini, Gobra or VerCors user writes the permission structure by hand as part of the specification, and a program with no specification yields no obligations. Prusti is consequently the only frontend that produces the workload this thesis targets: a large, highly structured set of obligations from a program that says nothing about what it computes.

An encoding Prusti produces is built from a small number of shapes. Ownership of a Rust value becomes a predicate, the value itself becomes an instance of an algebraic data type, and the body of a Rust function becomes a flat graph of basic blocks connected by #vi[`goto`]. A borrow that outlives the statement or the call creating it becomes a magic wand: Prusti reads the borrow checker's unblock graph, and wherever a borrowed place is unblocked it emits the wand that returns the permission, together with any pledge attached to that borrow. When a returned mutable reference dies, for instance, the wand is applied and full permission to the underlying object returns to the caller, which is how the encoding models Rust's borrow semantics.

== Symbolic Execution with Silicon <sec:bg-silicon>

Silicon @silicon is one of Viper's verification backends, and it operates by symbolic execution. Instead of running the program on concrete inputs, Silicon runs it on symbolic values that stand for every input at once, in the Smallfoot style @smallfoot. The state it carries as it goes has three parts: a store mapping each local variable to a symbolic value, a symbolic heap holding one chunk per location the state has permission to, and a path condition recording every assumption made to reach the current point.

Viper's other backend, Carbon @carbon, reaches the same goal from the other direction. Carbon generates verification conditions: it translates a whole method into a single formula whose validity implies the method's correctness, emits it as a Boogie program @boogie, and lets Boogie resolve it. Silicon instead walks the program and asks a separate question at every point where the program demands something. A verification condition generator makes one large query, whose failure is harder to attribute to a particular statement. A symbolic executor makes many small ones and knows exactly which statement raised each.

To answer those questions Silicon encodes them into SMT-LIB and discharges them with the SMT solver Z3 @z3. Proving a goal means asking whether its negation is unsatisfiable together with the current path conditions, so every obligation in the program is a round trip to an external process. Silicon uses the solver incrementally, pushing the assumptions of a path onto the solver's stack and popping them when it leaves that path. The encoding of the heap goes through symbolic snapshots, which capture the values at a program point through a custom `Snap` sort, and sort wrappers encode and decode values of each Viper type into that one sort. Almost everything else is encoded as uninterpreted functions constrained by universally quantified axioms, so the solver reaches most of what it needs by e-matching against the triggers of those axioms.

The cost this thesis also targets comes from branching. When Silicon reaches a conditional and the path condition decides neither outcome, it forks: it explores the two paths independently, each with the branch condition assumed one way. Whatever follows the conditional is then executed once per path. The method below has two conditionals and one statement after them, and Silicon executes that statement four times.

#no-numbers[```viper
method twice(a: Bool, b: Bool, x: Ref)
  requires acc(x.val, write)
{
  if (a) { x.val := 1 } else { x.val := 2 }
  if (b) { x.val := x.val + 1 } else { x.val := x.val - 1 }
  exhale acc(x.val, write) && 0 <= x.val
}
```]

Generalising, $n$ conditionals in sequence give $2^n$ paths, and the work after the last of them is repeated on all of them. What keeps this from being the whole story is pruning: before Silicon explores a path it asks the solver whether the branch condition is consistent with the path condition, and abandons the path when it is not. Pruning is effective when the branches are correlated, which is the common case in generated code, where a later condition is frequently settled by an earlier one and a whole execution subtree. The number of paths a real program explores is therefore far below the bound.

Functions receive an encoding of their own. Silicon axiomatises a function with
a small family of symbols: the function itself, a limited version of it, and a
precondition function @silicon. Every one of them takes a snapshot of the heap
as its first argument, so a function that reads no heap is encoded exactly as
one that does. The definitional axiom equates an application with the body and
is guarded by the precondition function, so a definition unfolds at an
application only where its precondition is known to hold, and it is triggered on
the application itself.

The precondition function also carries down into the body. One axiom states that
where a function's precondition holds at an application, so do the preconditions
of every call the body makes, which is what allows those callees to unfold at
the client in turn; a second does the same for the calls a postcondition names.
The limited version bounds recursion: an axiom equates it with the full
application and is triggered on that full application, so the definition unfolds
once and the recursive occurrence it exposes reaches the limited symbol, which
has no definition to unfold.

One case escapes that bound deliberately. Where a recursive call sits inside an
#vi[`unfolding`], Silicon adds a trigger to the definitional axiom that fires on
the term it assumes whenever the surrounding predicate is unfolded, so a
recursive heap-dependent definition unfolds one further level at each unfold of
the predicate. Annotating the function #vi[`@opaque`] turns this off.

== Equality Reasoning <sec:bg-equality>

Equality reasoning decides whether an equality follows from a set of assumed
equalities. Given $x = y$ and $f(y) = z$, does $f(x) = z$ follow?

Equality is reflexive, symmetric and transitive, so the assumptions partition
terms into equivalence classes, and two terms are equal exactly when they share
a class. The rule that matters is _congruence_: if $x = y$ then $f(x) = f(y)$.
Congruence ties the classes to the structure of terms. Merging two classes can
make other terms congruent, forcing further merges. For example, if $f(x) = z$
and $f(y) = w$, then merging the classes of $x$ and $y$ will consequently merge
the classes of $z$ and $w$. This process continues until no further merges are
possible, a fixpoint known as the _congruence closure_ of the assumptions.

Core proofs consist of obligations of this shape. A heap location is denoted by
a term, and the same location may be denoted by many syntactically distinct terms during a
symbolic execution. Establishing that a permission is held where the program
accesses memory means establishing that two such terms are equal. Permission
amounts behave the same way: a caller passing a fraction $p$ to a callee retains
$1 - p$, and when the callee returns it the caller must again establish full
permission, $(1 - p) + p = 1$. An obligation of this shape is settled by
computing a congruence closure, which involves no theory reasoning, no case
split, and no external process.

The data structure that computes one is the _e-graph_. An e-graph holds
_e-classes_, each an equivalence class of terms known to be equal, and each
e-class holds one or more _e-nodes_. An e-node applies an operator to e-classes
rather than to terms, so a single e-node stands for every term formed by
choosing one member of each argument class. Adding a term to the graph is a
lookup: an e-node with the same operator over the same argument classes is
already there, or it is created. Two terms are equal exactly when the lookup
returns the same class for both, which makes an equality query a comparison of
two class identifiers.

Merging two classes makes the structure more than a union-find. After a
merge, e-nodes that were distinct may have become congruent, because their
arguments now name the same classes, and every such pair has to be merged in
turn. @fig:egraph-congruence shows one step of this. Restoring the invariant
until no congruent pair is left is exactly the fixpoint described above, so an
e-graph with its invariant restored is a congruence closure.

#figure(
  egraph-congruence,
  caption: [Congruence in an e-graph. A solid box is an e-node, a dashed box is
    the e-class holding it, and an arrow runs from a node to the class of each
    of its arguments. Merging the classes of $x$ and $y$ leaves the two #vm[`f`]
    nodes applied to the same class, so they are congruent and their classes
    merge as well.],
) <fig:egraph-congruence>

We build on _egg_ @egg, a Rust library implementing e-graphs and equality
saturation. It provides three things this work uses. The first is _rebuilding_:
rather than restoring the congruence invariant after every merge, egg defers the
work and restores it in batches, which amortises the cost across a run of
merges. The second is the _e-class analysis_, a value drawn from a lattice that
is attached to each class and maintained across merges, which gives a place to
compute a fact about every term in a class at once. The third is _equality
saturation_: given a set of rewrite rules, egg applies every rule everywhere it
matches, repeatedly, until no rule produces anything new or a limit is reached.
A rule extends the closure with equalities that congruence alone does not give,
without an explicit proof search over the rules.

Saturation carries the cost of this approach. Arithmetic reasoning is
available to an e-graph, since the laws of arithmetic are rewrite rules like any
other and saturating over them derives their consequences. The difficulty is
that the rules which make arithmetic useful are also the ones that grow the
graph fastest. Commutativity and associativity together generate an e-node for
every permutation of a term's arguments, and distributivity multiplies a product
of sums into a sum of products. A rule set rich enough for general arithmetic
therefore blows the representation up long before saturation reaches the goal.
A verifier built on an e-graph must pick a rule set that saturates quickly, and
accept that an obligation needing genuine arithmetic or a case split lies
outside what that rule set reaches. @sec:results-qualitative reports where
our choice of rules falls short.

== Related Work <sec:bg-related>

#para[Joining symbolic execution branches] The path explosion of @sec:bg-silicon has
been attacked inside Silicon before. Bösiger @perf-impr added join points to
Silicon for #vi[`if`] statements and for the impure conditional expressions and
implications Silicon leaves forked, so that the two states are merged back into
one and the code after the conditional is executed once. A merge rewrites each
store entry into a conditional expression over the branch condition, and scales
each heap chunk's permission amount by that condition, giving a chunk the full
amount on the branch that produced it and none on the other. The result was a
verification time roughly 3% higher than without joining, measured over
frontend-generated programs from VerCors, Prusti, Gobra, Vyper and Nagini.
Joining helped only the smallest programs, about 3.3% of the corpus with a base
verification time under half a second, and the penalty grew with base
verification time. The number of merges performed showed no correlation with the
change. That thesis diagnoses the cause as the state a merge leaves behind: fewer
paths were bought with a more complex symbolic state, and the conditional
permission amounts a merge introduces make every later query harder for the
solver.

That diagnosis separates their result from ours. Joining fails there
because the merged state is handed to an SMT solver, where a conditional
permission amount becomes a term the solver must reason about at every later
query. Helium merges into an e-graph instead, where a conditional permission is
one more term in a structure that was going to hold it anyway.
@sec:impl-cfg shows what that buys.

#para[Reducing the reliance on quantifier instantiation] Gasser @theory-enc attacks
Silicon's encoding rather than its search, replacing the uninterpreted functions
and quantified axioms that @sec:bg-silicon describes with interpreted functions
and the solver's native theories. With quantifier instantiation heuristics
disabled entirely, that encoding verifies 53 of 176 test cases where the
existing encoding verifies 33. The two works target the same layer from opposite
sides: that one makes the solver's job more predictable and keeps the solver,
and this one removes the solver from the core proof.

#para[Congruence closure in provers] The reasoning of @sec:bg-equality is not new
machinery. Congruence closure is the decision procedure for the theory of
equality with uninterpreted functions, due to Nelson and Oppen @nelson-oppen,
and the E-graph that implements it sits at the centre of Simplify @simplify. A
modern SMT solver still contains one, underneath the theory solvers and the
case-splitting search it layers on top. The contribution here is therefore not a
new decision procedure. It is the observation that a core proof needs only the
bottom layer, and that removing the rest makes it fast.

#para[Other Rust verifiers] Prusti is not the only tool that derives obligations
from Rust's ownership discipline. Creusot @creusot translates Rust to WhyML and
discharges the result through Why3, Verus @verus verifies Rust against a
specialised SMT encoding, Aeneas @aeneas translates borrow-checked Rust into a
pure functional model and so avoids separation logic altogether, and RefinedRust
@refinedrust targets a foundational proof in Iris. Each of them ends at an SMT
solver or at a proof assistant. Our contribution is not another encoding of
Rust, but a cheaper way to discharge one that already exists.
