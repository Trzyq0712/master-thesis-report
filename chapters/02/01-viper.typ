#import "../../macros.typ": *

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
  acc(this.val, write) && this.val >= 0 &&
  acc(this.next, write) &&
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

A function may read the heap, in which case it states the permissions needed in its precondition, so its result depends on the heap as well as on its arguments. The function below sums a linked list. The expression #vi[`unfolding`] is the counterpart of the #vi[`unfold`] statement: it exchanges the predicate instance for its body within the expression that follows.

#no-numbers[```viper
function sum(this: Ref): Int
  requires acc(LinkedList(this), write)
{
  unfolding acc(LinkedList(this), write) in
    this.val + (this.next == null ? 0 : sum(this.next))
}
```]


#para[Magic wands] A magic wand #vi[`A --* B`], for assertions #vi[`A`] and
#vi[`B`], is a resource that can be exchanged for the resources of #vi[`B`] once
combined with the resources of #vi[`A`]. Two statements relate a wand to the resources around
it.

The #vi[`package`] statement creates an instance, proving from the resources
currently held that giving up #vi[`A`] would yield #vi[`B`], and it takes a block
in which that proof is carried out. The #vi[`apply`] statement is the inverse: it
consumes the instance together with #vi[`A`] and produces #vi[`B`].

The statements below package a wand exchanging permission to #vi[`x.val`] for an
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



