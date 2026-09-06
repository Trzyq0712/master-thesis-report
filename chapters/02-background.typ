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

Last, we discuss the related work: Viper's other backend, another attempt to
make symbolic execution of Viper programs faster that modified Silicon,
the libraries that implement equality saturation, and the other verifiers that
take Rust as their source language.

== Automated Program Verification with Viper <sec:bg-viper>

Deductive program verification proves that a program satisfies its specification for all possible inputs, where software testing checks its behaviour against concrete ones.
Viper @viper is a verification infrastructure that simplifies the development of
program verifiers for such proofs and supports the rapid prototyping of
verification techniques. It supports permissions natively and uses them to
express ownership of heap locations, which distinguishes it from infrastructures
such as Boogie @boogie and makes it a target for permission logics such as
separation logic and implicit dynamic frames. It consists of three parts:

- an intermediate verification language, in which a program carries its formal
  specification as part of its text,
- verification backends, which prove that a program in that language satisfies
  its specification,
- language-specific frontends, which translate a program written in a
  high-level language into the intermediate language.

The language is sequential, object-based and imperative. It is designed as a
target for a frontend, and it carries both the high-level constructs that make a
verification problem convenient to state by hand and the low-level constructs a
frontend needs to encode a source language automatically. Two backends verify a
program written in it, and both discharge the obligations they produce with the
Z3 @z3 SMT solver. Silicon @silicon executes the program symbolically, raising a
separate query at every point where the program demands something, and this work
takes it as the point of comparison. Carbon @carbon takes the other route,
generating verification conditions.

We present Viper's constructs with a small example of each. Viper
programs consist of fields, methods, functions, predicates, domains and ADTs. The two
constructs the section closes with, magic wands and quantified permissions, are
part of the language but not of the verifier we present.

#para[Statements] Viper programs are composed of statements and expressions. Basic statements
include variable declarations, assignments, and structural control flow.
Verification-specific statements include #vi[`assert`] (which requires the verifier
to prove a property holds at that point), and #vi[`assume`] (which adds a property
to the known state without proof).

#no-numbers[```viper
var a: Int
assume a == 42
assert a == 42
```]

#para[The heap and fields] Viper uses the #vi[`Ref`] type for heap-allocated objects with globally declared fields. A field declaration is global, so every field is nominally accessible through every reference: given #vi[`x: Ref`] and the two declarations below, both #vi[`x.value`] and #vi[`x.next`] are expressions the program may write.

#no-numbers[```viper
field value: Int
field next: Ref
```]

Whether a program may read or write #vi[`x.value`] is decided by permissions. Viper treats a field of a reference as a resource, and the expression #vi[`acc(x.value)`] denotes the permission to access it. Permissions are fractional. The amount #vi[`write`], equivalently #vi[`1/1`], is the maximum any state may hold, and it grants both reading and writing. Any amount above zero grants reading alone. A fraction is therefore what lets one part of a program lend read access while retaining the rest, and #vi[`acc(x.value, 1/2)`] states that half of the permission to #vi[`x.value`] is held.

A program that needs to read a location without committing to how much of it to hold writes #vi[`wildcard`] in place of a fraction. The amount is positive but unspecified, and it is settled only where the assertion is used. Inhaling a wildcard yields a fresh positive amount. Exhaling one requires the location to hold something already and gives away strictly less than that, so a positive remainder always stays behind. A wildcard therefore lends read access that can be handed out repeatedly without being exhausted, and it never grants writing, which needs #vi[`write`].

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

Permissions therefore support modular reasoning. A method that holds full permission to a location knows that no other part of the program holds any, so it may reason about that location without considering aliases.

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

Two statements exchange a predicate instance for the resources it packs. The #vi[`unfold`] statement requires the instance, consumes it, and produces the permissions and properties of the body. The #vi[`fold`] statement is its inverse: it requires everything the body states and produces the instance. Where an instance of #vi[`LinkedList(this)`] is held, the statements below unfold it to reach #vi[`this.val`] and fold it again afterwards.

#no-numbers[```viper
unfold acc(LinkedList(this), write)
this.val := this.val + 1
fold acc(LinkedList(this), write)
```]

#para[Data types] Alongside built-in primitive types, Viper supports complex
data types. Four container types are built in, #vi[`Seq[T]`], #vi[`Set[T]`],
#vi[`Multiset[T]`] and #vi[`Map[K, V]`], each with its own literal syntax and
operators. Algebraic data types allow defining structural types with named
constructors, and Viper
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
results. Their meaning comes entirely from the axioms declared alongside them.

#no-numbers[```viper
domain Box {
  function box(v: Int): Box
  function unbox(w: Box): Int

  axiom round_trip {
    forall v: Int :: { box(v) }
      unbox(box(v)) == v
  }
}
```]

An axiom is a closed assertion the verifier assumes everywhere in the program. A
single axiom constrains a single case, so stating a property of every value of a type takes a quantifier. Viper offers the universal quantifier #vi[`forall`] and the existential quantifier #vi[`exists`]. The axiom above quantifies over every integer, and it makes #vi[`box`] and #vi[`unbox`] mutual inverses: unboxing a boxed integer yields the integer it started from.

The term in curly braces is a _trigger_. A backend instantiates the quantifier for the values that make some term in the program match it, so this axiom is available exactly where the program boxes an integer. Viper infers a trigger where the source omits one.

#para[Methods] Methods are imperative code blocks serving as the fundamental unit of verification in Viper. They are annotated with contracts: #vi[`requires`] for preconditions and #vi[`ensures`] for postconditions. Methods can modify the heap.

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

#para[Control flow] A method body directs its execution with three constructs: #vi[`if`], #vi[`while`], and #vi[`goto`] paired with #vi[`label`]. The statements below use all three to clamp #vi[`r`] into the range from zero to ten.

#no-numbers[```viper
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
#vi[`div(a, b) == a / b`]. The precondition makes that body well-defined, and it
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

#para[Magic wands] A magic wand #vi[`A --* B`], for assertions #vi[`A`] and
#vi[`B`], is a resource that can be exchanged for the resources of #vi[`B`] once
combined with the resources of #vi[`A`]. A state holds instances of a wand as it
holds permissions and predicate instances, and #vi[`inhale`] and #vi[`exhale`]
move them in the same way. Two statements relate a wand to the resources around
it. The #vi[`package`] statement creates an instance, proving from the resources
currently held that giving up #vi[`A`] would yield #vi[`B`], and it takes a block
in which that proof is carried out. The #vi[`apply`] statement is the inverse: it
consumes the instance together with #vi[`A`] and produces #vi[`B`]. The
statements below package a wand exchanging permission to #vi[`x.val`] for an
instance of a predicate #vi[`P(this)`] whose body is
#vi[`acc(this.val, write)`]. The proof block folds #vi[`P(x)`], which consumes
exactly the permission the left-hand side of the wand supplies, so packaging
needs nothing from the state and precedes the #vi[`inhale`] that obtains that
permission. The #vi[`apply`] then trades the two for the instance.

#no-numbers[```viper
package acc(x.val, write) --* acc(P(x), write) {
    fold acc(P(x), write)
}
inhale acc(x.val, write)
apply acc(x.val, write) --* acc(P(x), write)
```]

#para[Quantified permissions] A quantified permission states permission to an
unbounded set of locations at once, by writing an accessibility predicate under a
#vi[`forall`]. The receiver of the location is an expression in the quantified
variable, so the assertion below grants one permission for each element of
#vi[`nodes`], an iterated separating conjunction over the set.

#no-numbers[```viper
forall n: Ref :: { n.val }
  n in nodes ==> acc(n.val, write)
```]

Quantified permissions and recursive predicates address the same problem. A
predicate fixes the order in which a proof visits a structure, which fits one
traversed from the top down, while a quantified permission names the locations
through a set and thereby fits a random-access structure such as an array or an
unordered one such as a general graph.



== Symbolic Execution with Silicon <sec:bg-silicon>

Silicon @silicon is one of Viper's verification backends, and it operates by symbolic execution. Silicon executes a program on symbolic values, each of which stands for every concrete input at once, in the Smallfoot style @smallfoot. The state it carries as it goes has three parts: a store mapping each local variable to a symbolic value, a symbolic heap holding one chunk per location the state has permission to, and a path condition recording every assumption made to reach the current point.

#para[Execution model] Silicon encodes the questions it asks into SMT-LIB and
discharges them with the SMT solver Z3 @z3. The solver runs as a separate
process, reading its commands from standard input. Proving a goal means
asserting the negation of that goal and asking whether the result is
unsatisfiable together with the assumptions already on the solver's stack. Every
obligation in the program is therefore a round trip to that process. Silicon
uses the solver incrementally: it pushes the assumptions of a path onto the
stack and pops them when it leaves the path. The solver's state consequently
follows the execution.

#para[The heap] The symbolic heap is a flat sequence of chunks, one per resource
the state holds permission to. A chunk names the field or predicate it stands
for, and carries the argument terms identifying the location, a term for the
value stored there, and a term for the permission amount held. Producing a
resource adds a chunk. Consuming one finds the chunk for the location demanded,
asks the solver whether the amount held covers what the assertion asks, and
subtracts it. Permission amounts are terms, so an amount may depend on the path
taken, and a check over an amount is a question for the solver like any other.

A lookup filters the sequence by the chunk's field or predicate, matches the
argument terms of the remaining chunks syntactically, and falls back to a solver
query against each candidate still standing. Two chunks whose argument terms
differ may still name the same location, since the equality of two terms is a
question for the solver. Silicon therefore consolidates the heap. It merges the
chunks whose arguments are known to be equal, summing their permission amounts
and equating the values they hold.

A merge of this kind runs whenever a chunk is added, and compares the new chunk
against those already held. A full consolidation compares every chunk against
every other and repeats until no new equality is derived. It then assumes the
properties that relate chunks pairwise, among them that two amounts summing past
#vi[`write`] imply distinct receivers. The filter by declaration confines every
comparison to chunks of the same field or predicate, but a full pass remains
cubic in the number of chunks in the worst case @silicon[Section 3.4.2]. Silicon
performs a full consolidation at a join, and on a path it retries after a failed
check.

#para[Predicates] A folded predicate instance is a chunk of the shape above,
holding the predicate's arguments and the amount of the instance. The value it
carries is a #emph[snapshot]: a single term recording the values of every
location in the predicate's footprint. The sort #vi[`Snap`] is the same whatever
the predicate. A snapshot is built by combining the values of the footprint
pairwise into one term, with wrappers encoding a value of any Viper type into
that sort and decoding it back out.

Verifying a predicate starts from an empty heap, with the formal parameters
bound to fresh symbols. Silicon produces the body into it against a fresh
snapshot, which confirms that the body is well-formed.

A #vi[`fold`] consumes the predicate's body. It removes the chunks the body
names from the heap, collects the values they held into a snapshot, and
produces a single predicate chunk carrying that snapshot and the amount
folded. An #vi[`unfold`] runs the same exchange backwards, taking the value of
each location the body names out of the stored snapshot. The values a program
held before a fold are therefore the values it sees after the matching unfold.

Both statements walk the predicate body itself, and so does an #vi[`unfolding`]
expression. Silicon evaluates it as though it were written inline at that point,
conjunct by conjunct, in the state that reaches it. Every side condition the
body carries is consequently discharged again, and every heap access it makes is
resolved against the heap as it stands now.

Silicon therefore walks the body once at the predicate, for the well-formedness
check, and once at every #vi[`fold`], #vi[`unfold`] and #vi[`unfolding`]. A
predicate folded or opened $n$ times has its body walked $n + 1$ times.

#para[Domains, ADTs and quantifiers] A domain becomes a declaration in the
solver's own vocabulary. The domain's type is declared as an uninterpreted sort,
its functions are declared as uninterpreted symbols over that sort, and its
axioms are asserted once, in a preamble emitted before any statement is
executed. A generic domain is monomorphised: Silicon collects the ground
instantiations the program uses, and emits one sort, one set of functions and
one set of axioms for each. The built-in container types arrive by the same
route. Silicon carries a Viper source file for each of them, declaring a generic
domain with that type's functions and axioms, and instantiates it exactly as it
would a domain the program declared.

An algebraic data type reaches Silicon as a domain of exactly this kind. Before
any backend sees the program, the declaration is desugared into a domain. The
functions of that domain are the constructors, one destructor per constructor
argument, and a #vi[`tag`] function giving the index of the constructor that
built a value. Viper then generates three families of axioms, each a quantifier
triggered on the term it constrains:

/ Injectivity: for every constructor, a destructor applied to a construction
  returns the argument it was given, $D_i (C(p_1, ..., p_n)) = p_i$.
/ Tag: for every constructor, the tag of a construction is that
  constructor's index, $"tag"(C(p_1, ..., p_n)) = i$.
/ Exclusivity: once per datatype, every value of the type equals a construction
  by one of the constructors,
  $t = C_1 (D_11 (t), ...) or ... or t = C_n (D_(n 1)(t), ...)$.

The first two answer questions about a value some constructor visibly built. The
third applies to every value of the type, whatever built it, which makes a case
analysis over the variants complete.

Quantifiers are discharged by the solver as well. Silicon emits a quantified
assertion with its triggers attached, and leaves the instantiation to the
underlying solver. The solver instantiates by e-matching: when a term it has built matches
a trigger, it adds the body of the quantifier for that term.

An instance carries the truth of the quantifier it came from. A quantifier
assumed under a condition therefore contributes its body only where that
condition holds, which makes matching a trigger sound whatever the solver has
settled at the time.

#para[Methods] Verifying a method starts from an empty state. Silicon produces
the preconditions into it, which confirms that they are well-formed, and records
the resulting heap as the pre-state the #vi[`old`] expressions of the contract
read. From that state it produces the postconditions into an empty heap, which
confirms that they are well-formed. It separately executes the body from that
state and consumes the postconditions at the end, which confirms that the method
meets its contract.

At a call Silicon binds the callee's formal parameters to the evaluated
arguments and consumes the preconditions. It then draws a fresh symbol for each
of the callee's return values, records the heap at the call as the pre-state of
the callee's #vi[`old`], and produces the postconditions. The returns are fresh,
so the only facts the caller holds about them come from the postconditions.

Silicon walks the precondition of a method once, when it produces it at the
start of verification, and the postcondition twice, once to confirm
well-formedness and once to consume it after the body. Every call adds one walk
of each, a consume of the precondition and a produce of the postcondition. A
method with a body and $n$ call sites therefore has its precondition walked $n + 1$ times
and its postcondition $n + 2$ times.

#para[Control flow]
When Silicon reaches a conditional and the path condition decides neither
outcome, it branches over it. The two paths are explored independently, each
with the branch condition assumed one way, and whatever follows the conditional
is executed once per path. The method below has two conditionals and one
statement after them, and Silicon executes that statement four times.

#no-numbers[```viper
method twice(a: Bool, b: Bool, x: Ref)
  requires acc(x.val, write)
{
  if (a) { x.val := 1 } else { x.val := 2 }
  if (b) { x.val := x.val + 1 } else { x.val := x.val - 1 }
  exhale acc(x.val, write) && 0 <= x.val
}
```]

Generalising, $n$ conditionals in sequence give $2^n$ paths, and the work after
the last of them is repeated on all of them. Pruning bounds the growth in
practice. Before Silicon explores a path it asks the solver whether the branch
condition is consistent with the path condition, and abandons the path when it
is not. Pruning is effective
when the branches are correlated. Correlation is the common case in generated
code, where a later condition is frequently settled by an earlier one and a
whole execution subtree is abandoned with it. The number of paths a real program
explores is therefore far below the bound.

At a loop head Silicon draws a fresh symbol for every variable the body writes
and produces the invariant into an empty heap, which confirms that the invariant
is well-formed and gives the state in which the body is executed. It consumes
the invariant from the state before the loop, which confirms that the invariant
holds on entry, and retains the heap left over as the frame the loop does not
touch. Every remaining edge into the loop head consumes the invariant again,
which confirms that an iteration preserves it. An edge leaving the loop merges
that frame back into the heap at the edge, and execution continues from the
result. Silicon therefore walks the invariant twice for the entry, once as a
produce and once as a consume, and once more for every remaining edge into the
loop head. A loop with $n$ back edges has its invariant walked $n + 2$ times.

#para[Functions] A function becomes a symbol $f$ taking a snapshot of the
precondition's footprint as its first argument and returning the function's
result. A function that reads no heap is encoded in the same way and applied to
the unit snapshot.

Verifying a function starts from an empty heap, with the formal parameters and
#vi[`result`] bound to fresh symbols. Silicon produces the precondition into it
under the snapshot symbol, which confirms that the precondition is well-formed,
and produces the postcondition from the state that results, which confirms that
the postcondition is well-formed. It then evaluates the body in the
precondition's state, assumes that #vi[`result`] equals the term the body
evaluates to, and consumes the postcondition, which confirms that the function
meets its contract.

At an application Silicon consumes the precondition, which confirms that the
permissions it names are held and yields a snapshot $s$ of them. It builds the
term $f(s, macron(x))$ from that snapshot and the arguments, and assumes
$f%"precondition"(s, macron(x))$ on the branch the application sits on. A
function reads the heap rather than claiming it, so the consume leaves the
caller's permissions in place.

The definition of the function reaches the solver as an axiom, triggered on
$f(s, macron(x))$ and guarded by $f%"precondition"(s, macron(x))$. Silicon emits
it once, into the preamble it assembles after verifying every function and
before verifying any method. An application supplies both of the axiom's
requirements at once, the term its trigger matches and the guard it is
conditioned on, and the solver thereby learns that $f(s, macron(x))$ equals the
body. The precondition symbol carries no defining axiom of its own, so it
becomes true only where an application has discharged the precondition.

Two further symbols carry the rest. The _limited symbol_ $f%"limited"$ has the
signature of $f$ and denotes the same value, and Silicon gives it no
definitional axiom, so an occurrence of it ends the unfolding. The stateless
symbol $f%"stateless"$ takes the arguments alone and returns a boolean recording
that the function has been applied to them.

@fig:fn-axioms gives the six axioms these four symbols carry. Three trigger on
the full application and three on the limited one, so a term that mentions only
the limited symbol still receives the postcondition, while the definition
unfolds only where the full symbol appears.

#figure(
  $
    &"limited:" #h(0.7em) && {f(s, macron(x))} #h(0.7em)
    && f%"limited"(s, macron(x)) = f(s, macron(x)) \
    &"stateless:" #h(0.7em) && {f%"limited"(s, macron(x))} #h(0.7em)
    && f%"stateless"(macron(x)) \
    &"definition:" #h(0.7em) && {f(s, macron(x))} #h(0.7em)
    && f%"precondition"(s, macron(x)) ==> f(s, macron(x)) = "body" \
    &"postcondition:" #h(0.7em) && {f%"limited"(s, macron(x))} #h(0.7em)
    && f%"precondition"(s, macron(x)) ==> "post" \
    &"body propagation:" #h(0.7em) && {f(s, macron(x))} #h(0.7em)
    && f%"precondition"(s, macron(x)) ==> "calls"("body") \
    &"post propagation:" #h(0.7em) && {f%"limited"(s, macron(x))} #h(0.7em)
    && f%"precondition"(s, macron(x)) ==> "calls"("post") \
  $,
  caption: [The six axioms Silicon emits for a function $f$. Each is quantified
    over the snapshot $s$ and the arguments $macron(x)$, and carries its trigger
    before its body. Here $"body"$ and $"post"$ are the function's body and its
    postcondition, with #vi[`result`] standing for $f%"limited"(s, macron(x))$,
    and $"calls"(e)$ is the conjunction of $g%"precondition"$ over every
    function $g$ applied in $e$.],
) <fig:fn-axioms>

The two propagation axioms carry a precondition inwards: where a function's
precondition holds at an application, so do the preconditions of the
applications its body and its postcondition make. Silicon emits the limited,
stateless, postcondition and post-propagation axioms once the specification is
confirmed well-formed, and the definition and body-propagation axioms once the
body verifies. A function without a body therefore contributes no definition.

Silicon translates every access predicate, magic wand and impure quantifier in
the precondition to $"true"$, so $f%"precondition"$ stands for the pure part of
the precondition. While it verifies a body or evaluates an application it
asserts read access only: consuming an #vi[`acc`] confirms that some permission
is held and leaves the chunk in place, and a #vi[`wildcard`] evaluates to full
permission. The amount a precondition names therefore does not reach the solver.

Silicon orders the functions by height and translates every application of a
function of the same or greater height, a recursive application among them, to
the limited symbol. The right-hand side of the definition mentions
$f%"limited"$ at the recursive occurrence, so a definition unfolds one level.
The definition carries a further trigger for the predicate that the outermost
#vi[`unfolding`] around a recursive application opens, pairing
$f%"stateless"(macron(x))$ with a term Silicon assumes whenever an instance of
that predicate is folded, unfolded or opened by an #vi[`unfolding`] expression.
A program that folds a list predicate around each of three nodes and applies a
recursive #vi[`len`] to the head therefore establishes #vi[`len(l) == 3`].

Silicon therefore walks the precondition once at the function, for the
well-definedness check, and once at every application. It walks the
postcondition twice at the function, once produced and once consumed, and never
at an application. A function applied $n$ times consequently has its
precondition walked $n + 1$ times and its postcondition twice, whatever $n$ is.
A caller of a method receives the postcondition by producing it, whereas a
caller of a function receives it from an axiom.


== Verification Frontends and Prusti <sec:bg-prusti>

Viper's intermediate language is a target rather than a source. A frontend takes a program in some high-level language and produces a Viper program whose verification establishes the property the frontend cares about. Prusti @prusti does this for Rust, Nagini @nagini for Python, Gobra @gobra for Go, and VerCors @vercors for Java. What they share is the hard part of the translation: each has to express its source language's memory model in Viper permissions, so that holding a permission in the encoded program corresponds to being allowed to touch the memory in the original one.

The obligations a frontend produces fall into two groups, and the split is by who writes them. A _functional specification_ is written by a person and states what the program computes. It is an arbitrary first-order assertion, and proving one may take arithmetic, quantifiers and rich theories. The _core proof_ is generated by the frontend, and it is the set of obligations that result from encoding the source language's memory and ownership semantics: that a permission is held wherever memory is accessed, that ownership transfers correctly across a call boundary, and that a structure's invariant is re-established before it is handed on. The distinction is visible in what Prusti does with an unannotated program: it still emits the full encoding of the obligations that follow from Rust's memory model, and there is simply no functional specification alongside them.

Rust makes the core proof interesting to us. Its type system enforces that a value is either shared or mutable but never both, and the borrow checker establishes this statically, before verification begins. Prusti therefore derives the whole core proof from the program text and Rust's semantics @prusti-oopsla, with no annotation from the programmer. Python, Go and Java carry no such ownership discipline, so a Nagini, Gobra or VerCors user writes the permission structure by hand as part of the specification, and a program with no specification yields no obligations. Prusti is consequently the only frontend that produces the workload this thesis targets: a large, highly structured set of obligations from a program that says nothing about what it computes.

The rest of this section takes the Rust constructs one at a time and gives the
Viper each becomes. No example below carries a specification, so everything
shown follows from Rust's semantics alone. Identifiers are shortened throughout,
and the comments Prusti attaches recording the MIR statement behind each line
are dropped.

#para[Scalars] A built-in scalar becomes four declarations: a domain giving the
type its values, a field and a predicate giving it a place in the heap, and a
function reading the one out of the other.

#viper(
  caption: [The declarations Prusti emits for #ru[`i32`]. #vi[`bool`] and the
    unit type follow the same pattern.],
  label: "lst:prusti-scalar",
  placement: auto,
)[```viper
domain i32 {
  function i32_cons(v: Int): i32
  function i32_value(s: i32): Int

  axiom { forall s: i32 :: {i32_value(s)}
    i32_cons(i32_value(s)) == s }
  axiom { forall s: i32 :: {i32_value(s)}
    -2147483648 <= i32_value(s) && i32_value(s) <= 2147483647 }
}

field p_i32_val: i32
predicate p_i32(self: Ref) { acc(self.p_i32_val, write) }

function p_i32_snap(self: Ref): i32
  requires acc(p_i32(self), write)
```]

The domain is the value. #vi[`i32_cons`] and #vi[`i32_value`] convert between a
snapshot and the integer behind it, and the axioms state that the two are
inverse and that the value stays inside the type's range. Every axiom carries a
trigger the encoder writes, since the encoding never relies on Viper inferring
one. The predicate is the permission, and #vi[`p_i32_snap`] bridges the two,
reading the field out from under the predicate with an #vi[`unfolding`]. The
encoding can therefore speak of a value wherever it holds the permission. A
companion method #vi[`p_i32_assign`] is bodyless, and its postcondition grants
the predicate at a given value. The encoding writes a local by calling it.

Arithmetic is a function over snapshots rather than an operation in a method
body. Prusti emits one per operator and operand type, and an operator that can
overflow returns the result paired with a flag. So #ru[`a + b`] becomes an
application of #vi[`add_ovf_i32`], which wraps the sum into range and reports
whether the wrap changed it.

#para[Structs and enums] A struct becomes an algebraic data type for its values
and a predicate for its permissions. The predicate holds one permission per
field, reached through a function from the struct's reference to the field's.
An enum adds a discriminant.

#lowering(
  caption: [An enum becomes one constructor per variant, a predicate over the
    discriminant, and one predicate per variant carrying that variant's
    payload.],
  label: "lst:prusti-enum",
  source-lang: "rust",
  target-lang: "viper",
  stacked: true,
  placement: auto,
)[```rust
enum Shape {
  Circle(i32),
  Rect(i32, i32),
}
```][```viper
adt Shape {
  Shape_0_cons(f0: i32)
  Shape_1_cons(f0: i32, f1: i32)
}

predicate p_Shape(self: Ref) {
  acc(p_isize(Shape_discr(self)), write) &&
  (let d == (p_isize_snap(Shape_discr(self))) in
    (d == isize_cons(0) || d == isize_cons(1)) &&
    (d == isize_cons(0) ==>
      acc(p_Shape_0(self), write)) &&
    (d == isize_cons(1) ==>
      acc(p_Shape_1(self), write)))
}
```]

One #vi[`p_Shape_N`] predicate per variant holds that variant's payload. The
disjunction states that the two variants exhaust the type, and each payload
permission is guarded by the discriminant that selects it. A program holding
#vi[`p_Shape`] therefore holds the payload of exactly one variant. Reading a value back
out reverses that structure: the snapshot function tests the discriminant, and
under each test unfolds the matching variant's predicate and applies that
variant's constructor.

#block(breakable: false, no-numbers[```viper
function p_Shape_snap(self: Ref): Shape
  requires acc(p_Shape(self), write)
{ unfolding acc(p_Shape(self), write) in
    d == isize_cons(1)
      ? unfolding acc(p_Shape_1(self), write) in Shape_1_cons(...)
  : d == isize_cons(0) ? ...
  : Shape_unreachable() }
```])

The chain ends in a bodyless function declared #vi[`ensures false`]. Viper
admits that postcondition without proof, so the terminator is sound only because
the predicate's disjunction makes the final branch dead wherever the predicate
is held.

#para[Rust functions] A function becomes a method whose return value is an
output parameter. The parameters are references, the precondition holds the
predicates of the arguments, and the postcondition holds the predicate of the
result.

#lowering(
  caption: [The signature Prusti emits for a two-argument function. Prusti names
    the parameters after the MIR locals, which are renamed here to match the
    Rust.],
  label: "lst:prusti-signature",
  source-lang: "rust",
  target-lang: "viper",
  placement: auto,
)[```rust
fn add(a: i32,
       b: i32) -> i32
```][```viper
method add(res: Ref, a: Ref, b: Ref)
  requires acc(p_i32(a), write)
  requires acc(p_i32(b), write)
  ensures acc(p_i32(res), write)
```]

The body is a flat graph: one #vi[`label`] per basic block, reached by
#vi[`goto`], and one Boolean per edge of that graph, set to #vi[`false`] at
entry and to #vi[`true`] on the edge taken. A block reachable from several
predecessors reads those Booleans back to recover which way control arrived, so
its heap operations are guarded by the path reaching it. A block Prusti knows to
be unreachable, such as the one a panic would enter, ends in
#vi[`assert false`].

#para[Branching] An #ru[`if`] and a #ru[`match`] are expressions in Rust, and
one written for its effect rather than its value is an expression of type
#ru[`()`]. The encoding keeps
that view: both forms produce the same shape, and they differ only in what the
arms assign.

#lowering(
  caption: [A conditional used for its effect. Each arm assigns the unit value
    to the result, and the second arm guards its heap operations with the edge
    it arrived on.],
  label: "lst:prusti-if",
  source-lang: "rust",
  target-lang: "viper",
  stacked: true,
  placement: auto,
)[```rust
fn maybe(b: bool, p: &mut i32) {
  if b { *p = 1; }
}
```][```viper
label bb_0
if (bool_value(b_val) == false) {
  from_bb0_to_bb2 := true
  goto bb_2
} else {
  from_bb0_to_bb1 := true
  goto bb_1
}

label bb_2
p_Unit_assign(res, Unit_cons())
goto bb_3

label bb_1
if (from_bb0_to_bb1) { make_concrete_i32(deref_p) }
p_i32_assign(deref_p, i32_cons(1))
p_Unit_assign(res, Unit_cons())
goto bb_3
```]

The method carries #vi[`ensures acc(p_Unit(res), write)`], so the unit a Rust
conditional evaluates to is a heap value it has to produce. Both arms produce
it. A conditional used for its value differs only in assigning an
#vi[`i32`] instead. A #ru[`match`] dispatches the same way, on the discriminant
it has read out of the enum.

That makes exhaustiveness an obligation about producing a value. Every arm the
compiler considers live constructs the result. The arm that no variant selects
constructs nothing and does #vi[`exhale false`] instead, discharging its
obligation by proving the path unreachable rather than by building the value it
would owe.

#no-numbers[```viper
label bb_1
exhale false
inhale false
```]

The enum predicate's disjunction makes that #vi[`exhale`] succeed, and the same
disjunction makes the snapshot function's terminator sound. A verifier therefore
has to carry a disjunction over a discriminant through a branch and spend it in
two places.

#para[Generics] The encoding reifies Rust's types into values and erases every
generic position to a single opaque type, so no Viper type parameter appears
anywhere.

#lowering(
  caption: [A generic struct. The type parameter becomes an ordinary value
    argument of type #vi[`Type`], and the field holds the erased snapshot
    #vi[`Param`].],
  label: "lst:prusti-generic",
  source-lang: "rust",
  target-lang: "viper",
  stacked: true,
)[```rust
struct Wrap<T> { inner: T }

fn unwrap_it<T>(w: Wrap<T>) -> T {
  w.inner
}
```][```viper
adt Type { i32_type() bool_type() }
domain Param { }

predicate p_Param(self: Ref, T: Type)

predicate p_Wrap(self: Ref, T: Type) {
  acc(p_Param(Wrap_field_0(self, T), T), write)
}

method unwrap_it(res: Ref, w: Ref, T: Type)
  requires acc(p_Wrap(w, T), write)
  ensures acc(p_Param(res, T), write)
```]

A value whose type is a parameter has the snapshot type #vi[`Param`], a domain
without functions or axioms. Its permission is #vi[`p_Param`], an abstract
predicate taking the reified type beside the reference. Crossing
between a concrete type and its erased form takes a cast, and the encoding
provides one at each level. On values, a pair of bodyless functions converts a
snapshot in each direction, each naming the other in its postcondition.

#no-numbers[```viper
function generic_i32(self: i32): Param
  ensures typeof(result) == i32_type()
  ensures concrete_i32(result) == self

function concrete_i32(snap: Param): i32
  ensures generic_i32(result) == snap
```]

On permissions, a pair of bodyless methods exchanges #vi[`p_i32`] for
#vi[`p_Param`] and back, relating the two snapshots through #vi[`old`]. These
pairs are the only cycles anywhere in the generated program. Neither function has
a body, so the cycle runs through their contracts.

#para[Loops] A loop is a back edge in the block graph rather than a
#vi[`while`]. The label heading the loop carries the invariant, written as one
#vi[`invariant`] clause per permission. For an unannotated program that
invariant states the permissions the loop holds on to and nothing about the
values in them.

#para[Borrows] A borrow that outlives the statement creating it becomes a magic
wand. Prusti reads the borrow checker's record of where each borrow ends, and
emits a wand giving the permission back at that point. A function returning a
mutable reference into its argument states the wand in its postcondition.

#no-numbers[```viper
ensures acc(p_Param(res.target, i32_type()), write) --*
        acc(p_Param(old(arg).target, Point_type()), write)
```]

The caller receives permission to the returned reference together with the wand.
Applying the wand trades that permission back for permission to the whole
structure, which is how the encoding models the borrow ending. The method proves
the wand in a #vi[`package`] block that folds the structure back up and runs the
casts above. A labelled #vi[`old`] names the state each borrow was taken in.

These constructs delimit the fragment of Viper that a spec-less Rust program
needs, and that this work sets out to support:

- *Methods:* goto-based control flow over flat basic-block graphs, with
  conditional jumps, back edges, invariants on a loop head, and bodyless methods
  carrying contracts. #vi[`old`] appears in postconditions, and only there.
- *Functions:* abstract and heap-dependent, with permission preconditions and
  #vi[`unfolding`] in their bodies, and mutually recursive definitions relating
  concrete and erased snapshots.
- *Predicates:* #vi[`fold`], #vi[`unfold`], abstract predicates, and bodies
  whose permissions are guarded by conditions on the heap.
- *Domains and ADTs:* non-generic domains whose axioms use #vi[`forall`], every
  one with an encoder-supplied trigger, and algebraic data types with
  constructors, destructors and discriminants, among them the type reifying the
  crate's types.
- *Base Viper:* full and wildcard permission amounts, amounts that are
  conditional expressions rather than literals, the arithmetic operators, and
  #vi[`exhale`] of #vi[`false`] to discharge an unreachable block.

Quantified permissions never appear,
since ownership of an unbounded structure is expressed by a recursive predicate
rather than by a quantifier over locations. Nor do the existential quantifier,
fractional permission literals, or the sequence, set, map and multiset types.
Magic wands appear only in the borrow-returning shape above, and a program
returning no references out of its arguments needs none.


== Equality Reasoning and E-Graphs <sec:bg-equality>

A core proof asks one question over and over, whether two syntactically
different terms denote the same location. A location is identified by the terms
naming its receiver, and Prusti's encoding reaches a field through a function
applied to that receiver, so one location acquires many spellings
over an execution. Establishing that a permission is held where the program
reads memory means establishing that two such spellings agree.
Permission amounts behave the same way. A caller passing a fraction $p$ to a
callee retains $1 - p$, and when the callee returns the fraction the caller must
establish full permission again, $(1 - p) + p = 1$. Both questions are equalities
between applications of uninterpreted symbols, and equality reasoning alone
settles them.

Equality is reflexive, symmetric and transitive, so a set of assumed equalities
partitions terms into equivalence classes, and two terms are equal exactly when
they share a class. _Congruence_ carries that partition into the structure of
terms: if $x = y$ then $f(x) = f(y)$. From $x = y$ and $f(y) = z$ it therefore
follows that $f(x) = z$. Congruence also propagates. Merging two classes can
make other terms congruent and force further merges, so from $f(x) = z$ and
$f(y) = w$, merging the classes of $x$ and $y$ merges the classes of $z$ and $w$
as well. Repeating until no further merge is possible gives a fixpoint, the
_congruence closure_ of the assumptions.

An _e-graph_ computes that closure. It holds _e-classes_, each an equivalence
class of terms known to be equal, and each e-class holds one or more _e-nodes_.
An e-node applies an operator to e-classes rather than to terms, so one e-node
stands for every term formed by choosing a member of each argument class, and a
graph of modest size represents a large set of terms. Adding a term is a lookup:
an e-node with the same operator over the same argument classes is either
already present or created. Two terms are then equal exactly when the lookup
returns the same class for both, which reduces an equality query to a comparison
of two class identifiers.

After a merge, e-nodes that were distinct may have become congruent, because
their arguments now name the same classes, and every such pair has to be merged
in turn. @fig:egraph-congruence shows one step.
Restoring the invariant until no congruent pair is left is the fixpoint above,
so an e-graph with its invariant restored is a congruence closure.

#figure(
  egraph-congruence,
  caption: [Congruence in an e-graph. A solid box is an e-node, a dashed box is
    the e-class holding it, and an arrow runs from a node to the class of each
    of its arguments. Merging the classes of $x$ and $y$ leaves the two #vm[`f`]
    nodes applied to the same class, so they are congruent and their classes
    merge as well.],
) <fig:egraph-congruence>

Congruence derives only the equalities that follow from the assumptions. A
_rewrite rule_ adds the rest. A rule is a pattern paired with a replacement, and
finding where it applies means matching the pattern against the graph: the match
walks e-nodes from the operator at the pattern's root, binding each pattern
variable to an e-class, and yields one substitution per way the pattern fits.
Applying the rule builds the replacement under that substitution and merges the
result with the class that matched. Because an e-node ranges over classes rather
than terms, a single match covers every term those classes contain, and a single
application speaks for all of them.

_Equality saturation_ applies every rule everywhere it matches, repeatedly,
until no rule produces anything new or a limit is reached. The result extends
the closure with equalities congruence alone does not give, and reaches them
without an explicit proof search over the rules.

Proving two terms equal and proving them different are not symmetric tasks. A
merge proves an equality, and congruence carries it upward at no cost, since
equal arguments make equal applications. Two terms in different classes prove
nothing, because a class records the equalities the assumptions force rather
than the distinctions they permit. A disequality therefore has to be derived.

Arithmetic meets the same boundary from the other side. The laws of arithmetic
are rewrite rules like any other, so saturating over them derives their
consequences, but the rules that make arithmetic useful are also the ones that
enlarge the graph fastest. Commutativity and associativity together generate an
e-node for every permutation of a term's arguments, and distributivity turns a
product of sums into a sum of products. A rule set rich enough for general
arithmetic therefore exhausts the representation long before saturation reaches
the goal, which confines a verifier built on an e-graph to a rule set that
saturates quickly.

None of this machinery is unusual in a prover. An SMT solver maintains an
e-graph of its own, holding the equalities it has derived, and matches a
quantifier's triggers against it, which is e-matching.
The structure is the same one described here. A solver layers theory solvers
and a case-splitting search over that graph, and those layers separate a solver
from the bare congruence closure underneath.

We adopt _egg_ @egg, a Rust library implementing e-graphs and equality
saturation, as the engine for the equality reasoning this work rests on. Its
rules and analyses are written as types in the host language rather than as
patterns in a rule language of its own, so a rule may consult state outside the
graph, memoise its work, or construct a term
conditionally, none of which a pattern expresses. Its one limitation worth
naming is the absence of an undo: an e-graph can be cloned but not rolled back,
so assuming a condition for the duration of a proof means copying the whole
graph.

Egg introduced two techniques of its own. _Rebuilding_ addresses the cost of
restoring congruence after every merge, which repeats work the next merge may
undo. Egg defers the restoration and runs it in batches, which amortises the
cost over a run of merges, so a rebuild stands for the whole congruence closure:
after one, the graph holds every equality the assumptions entail.

An _e-class analysis_ attaches a value drawn from a lattice to each class and
maintains it across merges, so a fact about every term in a class is computed
once and held in one place. The mechanism is abstract interpretation lifted to
the e-graph. Merging two classes joins their values, and a value that changes
propagates to the classes built on top of it, again to a fixpoint.


== Related Work <sec:bg-related>

#para[Verification condition generation] Carbon @carbon is Viper's other
backend, and it discharges a program without executing it. It translates a whole
method into a single formula whose validity implies the method's correctness,
emits that formula as a Boogie program @boogie, and lets Boogie resolve it. A
verification condition generator therefore raises one large query, which gives
the solver the whole method at once but makes attributing a failure to a
particular statement harder. A symbolic executor raises many small queries and
records which statement raised each, and pays for that by exploring every path
separately.

#para[Joining symbolic execution branches] The path explosion of @sec:bg-silicon has
been attacked inside Silicon before. Bösiger @perf-impr added join points to
Silicon for #vi[`if`] statements and for the impure conditional expressions and
implications Silicon branches over, so that the two states are merged back into
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

#para[Equality saturation libraries] _egg_ is not the only implementation of
e-graphs and equality saturation. Its successor egglog @egglog unifies
Datalog with equality saturation, and states its rules and queries in a
specialised language of its own rather than as types in the host language. That
language is the primary way of driving the library, which makes it the more
rigid of the two to interact with directly from a Rust program.

#para[Other Rust verifiers] Prusti is not the only tool that derives obligations
from Rust's ownership discipline. Creusot @creusot translates Rust to WhyML and
discharges the result through Why3, Verus @verus verifies Rust against a
specialised SMT encoding, Aeneas @aeneas translates borrow-checked Rust into a
pure functional model and so avoids separation logic altogether, and RefinedRust
@refinedrust targets a foundational proof in Iris. Each of them ends at an SMT
solver or at a proof assistant. Our contribution is not another encoding of
Rust, but a cheaper way to discharge one that already exists.
