#import "../../macros.typ": *

== Functions <sec:impl-functions>

Every function the preceding sections have used is uninterpreted. A field
declaration becomes a location function, a predicate gains one for its
instances, and a domain declares a family of them. In each case an application
is an opaque token that does not relate to any computation or value, which is all
those three constructs ask for. A Viper #vi[`function`]s can do more: it may have a
contract and a body that the definition should unfold to.

Of everything in this chapter, this is where we stayed closest to Silicon.
Silicon axiomatises a function with a small family of symbols, among them the
function itself, an uninterpreted precondition token, and a limited twin for
the recursive case @silicon. The section reaches those symbols one at a time: it
starts from a function with a body and no contract, adds a precondition and then
a postcondition, lets the function read the heap, and closes with how recursion
is handled.

=== Function bodies

A function declaration on its own contributes a signature, so an application of
it builds a term of the return type and stands unrelated to anything else.
@lst:fn-opaque declares one and applies it. Every earlier occurrence of the
shape was derived by the translator, and this one is written in the program.

#lowering(
  caption: [A function with no body. The application is an opaque term, so the
    assertion fails.],
  label: "lst:fn-opaque",
)[```viper
function div(s: Int, n: Int): Int

method client()
{
  assert div(10, 2) == 5
  // ^-- fails
}
```][```vmir
function div(
  e0: Int, e1: Int): Int

method client {
  e0: Int := div(10, 2)
  e1: Bool := e0 == 5
  assert e1   // fails
}
```]

The application builds a term and states nothing about it. Nothing relates
#vm[`div(10, 2)`] to #vm[`5`], so the assertion stands unproven. This could
be remedied by stating an axiom (@sec:impl-domains) that relates the function
to its interpretation. Viper, however, has a more targeted solution to express
this relation via a function body. @lst:fn-body gives the function one.

#lowering(
  caption: [A body makes the declaration a definition. The equation it yields
    is what the call site of @lst:fn-opaque needs, and the body's own division
    is unproven.],
  label: "lst:fn-body",
)[```viper
function div(s: Int, n: Int): Int
{
  s / n
  // ^-- fails
}
```][```vmir
function div(
  e0: Int, e1: Int): Int
{
  e2: Int := e0 / e1 // fails
  result: e2
}
```]

A function body lowers to the same pure instructions an expression in a method
body does, terminated by a #vm[`result`] naming the temporary the function
returns. Helium walks that body once, and the walk yields two things. The parameters
enter as fresh values, so the walk knows their types and nothing else about
them. It then takes the instructions in order. Each raises whatever obligations
it carries, which the walk proves under that instruction's own path condition,
and each contributes its term to the state the walk carries forward. Alongside that
state the walk carries a second term per temporary, built from the terms of the
instruction's operands, and that is the _recipe_. The verdict and the
certificate come out of one pass over the body.

The recipe is the construct of
#pararef(<para:impl-slot-recipes>, [Slots and recipes]), seeded here by the
parameters rather than by footprint slots. The parameters take the first
temporaries and a step names only earlier ones, so the two lines of the listing
above are already the recipe:
the term #vm[`e0 / e1`] over the parameters, with #vm[`result`] naming the
temporary that carries the value.

At each occurrence of #vm[`div(a, b)`] Helium instantiates the recipe with the
parameters bound to the arguments, and equates the result with the function
token. An instantiation builds terms and proves nothing, since the declaration
already discharged the obligations. That is the definitional
equation #vm[`div(a, b) == a / b`] driven by a rewrite rule.

The call site now has the equation it needs. However, the function declaration itself does not pass.
The division raises the obligation that #vm[`e1`] is non-zero, the parameters
arrived fresh, and nothing rules out #vm[`e1`] being zero. To make #vm[`div`] well-defined,
it needs to have an appropriate precondition.

=== Preconditions

A precondition is the clause that constrains the parameters of a function. What
it lowers to depends on whether it reads the heap. For a heap-free function the
translator lowers it to a boolean #vm[`#requires`] function (@lst:fn-pre), and
the heap-dependent case waits until the section admits the heap.

#lowering(
  caption: [A heap-free precondition becomes a boolean function. The body
    assumes it and the call site asserts it.],
  label: "lst:fn-pre",
)[```viper
function div(s: Int, n: Int): Int
  requires n != 0
{
  s / n
}
//@
method client(k: Int)
{
  assert div(10, k) == 5  // fails
}
```][```vmir
function div#requires(
  e0: Int, e1: Int): Bool
{
  e2: Bool := e1 != 0
  result: e2
}

function div(
  e0: Int, e1: Int): Int
{
  e2: Bool := div#requires(e0, e1)
  assume e2
  e3: Int := e0 / e1
  result: e3
}
//@
method client {
  e0: Int := fresh        // k
  e1: Bool :=
      div#requires(10, e0)
  assert e1               // fails
  e2: Int := div(10, e0)
  e3: Bool := e2 == 5
  assert e3
}
```]

The #vi[`requires`] clause becomes a #vm[`div#requires`] function. The function's
own body opens by assuming that application holds at the parameters, and that
assumption discharges the division obligation: #vm[`div#requires`] has a body of its own,
so the assumed application unfolds to #vm[`e1 != 0`].

The call site asserts the same application at the arguments before the actual
call.
Nothing in VMIR forces this: an instruction stream is free to apply
#vi[`div`] without ever asserting #vm[`div#requires`] first, and the verifier
raises no obligation of its own that would stop it. What makes the check
happen is the translator's own discipline, not a rule VMIR enforces --- it
never emits a call site without the matching assertion. Naturally, for
functions with no precondition the translator emits nothing.

#para[Precondition tokens] <para:impl-fn-tokens> A call also mints a term the
translator never writes. Helium allocates one uninterpreted symbol per
function, #vm[`div%pre`].
At each syntactic call to #vi[`div`] in the body it is checking, the verifier
mints the token at that call's arguments and assumes it true under the call's
path condition.
@lst:pre-token calls #vi[`div`] in one arm of a conditional, so that path
condition is the arm's guard.

#lowering(
  caption: [A call under a branch. The application carries the guard #vm[`e0`],
    and the verifier assumes the token it mints under that guard alone.],
  label: "lst:pre-token",
)[```viper
k != 0 ? div(10, k) : 0
```][```vmir
e0: Bool := k != 0
...
e2: Int  := <e0> div(10, k)
...
```]

Concretely, Helium assumes that the function #vm[`div(10, k)`] is well-defined
by assuming the precondition token holds when #vm[`e0`] holds. This gives the general
formula for the token's truth at a call site:

$ "PC" => f"%pre"(overline(x)) $

That guard is what keeps a fact released at one call from reaching a sibling
branch that never made it. The token plays two roles. Its presence triggers the rule that equates the body
instantiation to the opaque function node, which keeps a function from unfolding
where that would not be sound. Below gives the actual definitional axiom:

$ f"%pre"(overline(x)) => f(overline(x)) = "body"_f (overline(x)) $

The same mechanism governs the unfolding of the functions called indirectly.
Every call in a body carries a mark, written #vm[`export`], that says whether
instantiating the body at a client re-releases that callee's token there. A
marked call releases its token under two guards, the token that licensed the
instantiation and the path condition the call sits under inside the body:

$ f"%pre"(overline(x)) and "PC"_g(overline(y)) => g"%pre"(overline(y)) $

Here $g(overline(y))$ is the call the body makes, and $overline(y)$ its
arguments, built from $overline(x)$ by the steps of the recipe that precede it.
Setting the mark is the translator's decision, recorded on the instruction,
because the translator is what knows why it emitted the call. @lst:fn-half
lowers a caller for #vi[`div`] whose one expression makes both kinds of call.

#lowering(
  caption: [A caller for #vi[`div`]. The precondition check is an obligation and
    stays bare, and the application whose value #vi[`half`] returns is marked.],
  label: "lst:fn-half",
)[```viper
function half(s: Int): Int
{
  div(s, 2)
}
```][```vmir
function half(e0: Int): Int
{
  e1: Bool := div#requires(e0, 2)
  assert e1
  e2: Int := export div(e0, 2)
  result: e2
}
```]

The call to #vm[`div`] is marked because its value is what #vi[`half`] returns,
so a client's instantiation produces that application and needs the token to
open it. The #vm[`div#requires`] check beside it is an obligation: it unfolds to
#vi[`2 != 0`], the verifier discharges it while checking #vi[`half`], and the
recipe a client instantiates records none of it. A caller that applies #vi[`half(k)`] mints
#vm[`half%pre(k)`], the one token written at that call site. The token releases
#vi[`half`]'s definitional equation,

$ "half%pre"(s) => "half"(s) = "div"(s, 2), $

and the instantiation that produces #vm[`div(k, 2)`] mints that call's own token
alongside it meaning that the #vm[`div`] inside was applied safely:

$ "half%pre"(s) => "div%pre"(s, 2). $

With #vm[`div%pre(k, 2)`] present, #vi[`div`]'s equation fires at those
arguments,

$ "div%pre"(s, 2) => "div"(s, 2) = s \/ 2, $

so the caller eventually gets #vm[`half(k) == k / 2`]. Three rules fired in
sequence, each licensed by a token the one before it minted, and the caller
never proved #vi[`2 != 0`] for itself.

=== Postconditions

A function may want to attach an #vi[`ensures`] clause for a couple of reasons.
- A function with no body
  releases no definitional equation, so the clause is the whole of what a caller
  reads.
- A function might want to state a property of its return value that is not immediately
  obvious from the body, but is a useful fact for a caller to know.
- A (mutually) recursive function cannot unfold its own body, so the ensures clause
  serves as the induction hypothesis to verify the function's own body.

An #vi[`ensures`] clause lowers to VMIR the way a #vi[`requires`] clause does,
as a boolean function over the parameters followed by the result. The VMIR
declaration still carries a link to that function.
@lst:fn-post has no body, so its clause is all it offers.

#lowering(
  caption: [A function with no body. The clause becomes #vm[`abs#ensures`],
    which takes the parameters and the result, and the declaration links to it.],
  label: "lst:fn-post",
)[```viper
function abs(x: Int): Int
  ensures result >= 0
```][```vmir
function abs#ensures(
    e0: Int, e1: Int): Bool
{
  e2: Bool := e1 >= 0
  result: e2
}

function abs(e0: Int): Int
  ensures abs#ensures(e0, result)
```]

#vm[`abs#ensures`] takes the parameters and one more for the result, which is
what #vi[`result`] in the clause lowers to. Where there is a precondition the
member assumes it first, so a clause whose well-definedness rests on the
precondition is checked in the state that precondition describes. A function with
a body closes it by asserting the same application at the value it returns, and
the verifier discharges that assertion where it stands and keeps nothing from it.

Helium builds what a caller reads from the declaration's link, so the same
construction serves a function with a body and one without. Write $p$ for the
member that link names, which @lst:fn-post lowers to #vm[`abs#ensures`]. At
an occurrence the token releases the link alongside the definitional equation:

$ f"%pre"(overline(x)) => p(overline(y)) and p"%pre"(overline(y)) $

Here $overline(y)$ is the argument list the link records, built from the
parameters $overline(x)$ and carrying the application $f(overline(x))$ in the
result position.
The first conjunct states that `p` holds when the precondition token is present.
The second is what enables the caller to release `p`'s body, which is how
the caller receives the actual information. A contract definition is an ordinary
function body, so the calls in it are value positions and carry the
#vm[export] mark. @lst:fn-post-callee names a second function in its clause.

#lowering(
  caption: [A clause that names a second function. The call to #vi[`g`] inside
    #vm[`f#ensures`] is a value position, so it carries the mark.],
  label: "lst:fn-post-callee",
)[```viper
function g(a: Int): Int
{ a + 1 }

function f(x: Int): Int
  ensures result == g(x)
```][```vmir
function f#ensures(
    e0: Int, e1: Int): Bool
{
  e2: Int := export g(e0)
  e3: Bool := e1 == e2
  result: e3
}

function f(e0: Int): Int
  ensures f#ensures(e0, result)
```]

A caller of #vi[`f(3)`] reads #vm[`f(3) == g(3)`] from the first conjunct, and
the marked call releases #vm[`g%pre(3)`], which opens #vi[`g`] to #vm[`3 + 1`].
The chain runs #vm[`f%pre`] to #vm[`f#ensures%pre`] to #vm[`g%pre`], one link for
each member the contract names.

=== Heap-dependent functions

A precondition that grants permission cannot be a boolean function, because it
describes a heap fragment together with an assertion about it. That is a resource, and
@sec:impl-predicates already lowers one. When the translator is presented with a
heap dependent function, it lowers the precondition to a resource and the function itself
now takes the resource's snapshot as a trailing argument. Every permission amount
in that resource becomes a #vm[`wildcard`] where it is positive and zero where it
is not, matching Silicon's default. A heap-dependent postcondition takes the
snapshot as a trailing parameter of its own, so that it can read the pre-state the
precondition describes. @lst:fn-heapdep serves as an example of what the
translator does to a heap-dependent function.


#lowering(
  caption: [The precondition becomes a resource, the function takes that
    resource's snapshot as a trailing parameter, and the call site produces the
    snapshot by exhaling the resource. That exhale discards its heap into
    #vm[`_`], and the call itself takes no heap operand.],
  label: "lst:fn-heapdep",
)[```viper
field val: Int

function get(c: Ref): Int
  requires acc(c.val)
{
  c.val
}
//@
method client(x: Ref)
  requires acc(x.val)
{
  var v: Int := get(x)
}
```][```vmir
resource get#requires(e0: Ref) {
  e1: &[val] Int @ 1/1
     := val(e0)
  h0 := empty + e1 @ wildcard
        with self
  result: (h0, true)
}

function get(e0: Ref,
    e1: get#requires@snap): Int
{
  h0 := empty inhale
        get#requires(e0) @ wildcard
        with e1
  e2: &[val] Int @ 1/1
     := val(e0)
  e3: Int := *[h0] e2
  result: e3
}
//@
method client {
  ...
  _, e2 := h0 exhale
        get#requires(e0) @ wildcard
  e3: Int := get(e0, e2)
}
```]

The body's opening instruction widens the snapshot parameter back into a heap,
which is what a method postcondition does with its own snapshot parameter
(@sec:impl-methods). The read that follows raises the sufficiency obligation any
dereference raises against the heap the inhale built. A precondition naming a
predicate instance lowers to a resource the same way, and the body opens the
instance with the unfold pair of @sec:impl-predicates before it reaches a
field.

The call site pays for that snapshot with an exhale of the resource. The exhale
is frame-only: it proves the footprint is held and yields the snapshot, and the
heap it would otherwise produce is never built. Nothing consumes that heap, so
the caller goes on with the one it already had, and the call takes no permission
away.

VMIR therefore has no heap-dependent function form. #vi[`get`] takes parameters
and returns a value, the snapshot is one of those parameters, and
#vm[`get(e0, e2)`] is the instruction any other call emits. What makes the
function heap-dependent is the exhale standing beside that call. Once the body is
verified even that is behind it: what remains is a term over #vi[`get`]'s two
parameters, instantiated at each occurrence on the caller's arguments and the
snapshot it exhaled, with no heap consulted anywhere. The heap the body reasoned
about survives as the snapshot it was summarised into.

Two shapes are out of reach. A postcondition justified only on one branch does
not discharge, because the token is released under the path condition of the
precondition check while the exit assertion sits under none, and the verifier
does not case-split to bridge them. A heap-dependent application inside a
#vi[`forall`] body is rejected by the translator: the snapshot would have to be
taken per instance, over a footprint that may mention the binders, and a
footprint described by the binders is a quantified permission. A binder-free
footprint is rejected with it, since #vm[`f#requires`] is parameterised by the
whole argument list and its boolean has to be checked under the quantifier's
antecedent, which taking the exhale outside the binder does not preserve.

=== Recursive functions

Instantiating the recipe of a function that calls itself produces the recursive
application, which triggers the rule again at smaller arguments, and the
repetition continues indefinitely.
@lst:fn-recursive is the length of a list.

#lowering(
  caption: [The length of a list. The recursive application inside the body is
    where the encoding bounds the unfolding.],
  label: "lst:fn-recursive",
)[```viper
adt List {
  Nil()
  Cons(head: Int, tail: List)
}

function length(l: List): Int
  ensures result >= 0
{
  l.isNil
    ? 0
    : 1 + length(l.tail)
}
```][```vmir
adt List {
  Nil() | Cons(Int, List)
}

function length(e0: List): Int
  ensures length#ensures(
      e0, result)
{
  e1: Int  := List@tag(e0)
  e2: Bool := e1 == 0
  e3: List := List::Cons.1(e0)
  e4: Int  := <!e2>
      export length(e3)
  e5: Int  := 1 + e4
  e6: Int  := e2 ? 0 : e5
  e7: Bool := length#ensures(
      e0, e6)
  assert e7
  result: e6
}
```]

Helium bounds the unfolding with a _limited twin_, exactly as Silicon would.
Every recursive function gains a second symbol, displayed #vm[`length%lim`],
which carries a signature and stays uninterpreted. While building the recipe,
Helium retargets the calls that close the cycle to the twin, so an instantiation
lands on #vm[`length%lim`] and stops there. One rewrite relates the twin to the
function:

$ f(overline(x)) ~> f"%lim"(overline(x)) $

The rewrite above is directional. That means Helium matches on the left-hand
side, mints the twin at the same arguments, and merges the two e-classes. Had
this been a bidirectional rule, the solver would immediately run into a matching
loop, infinitely unfolding the recursive application again. The merge carries
every fact the caller establishes of #vm[`length`] at those arguments to the
#vm[`length%lim`] a sibling unfold produced.

That rewrite is the whole of what the twin needs. The recursive call carries
the #vm[`export`] mark, so it releases its own precondition token wherever the
recipe is instantiated, and the postcondition release fires at that application
exactly as it does at any other call. The declaration's promise therefore
reaches the twin by the ordinary route: the recursive call contributes
#vm[`length%lim(e3) >= 0`], the fact the exit assertion needs of the recursive
arm. What the twin bounds is the definitional equation, which stays keyed
on the full application and so never fires on the twin the recipe produced.

Currently, Helium cannot verify the #vm[length] function shown in
@lst:fn-recursive. This stems not from a limitation in the encoding, but from
the verifier's restricted reasoning capabilities. Because this example
involves a functional specification, which falls outside Helium's core objectives,
successful verification would require case analysis, a feature Helium lacks.
However, if the functional ensures clause is removed, the verification succeeds.

=== Comparison with Silicon

The correspondence between the two backends is nearly one-to-one. Silicon's definitional axiom, limited axiom, and two propagation axioms each have a direct counterpart in this encoding, and the precondition token is utilized in a similar manner.

However, four notable differences exist. First, Silicon consumes a function's precondition during the evaluation of the application; thus, establishing it is the responsibility of the verifier. In contrast, this approach delegates that responsibility to the caller, and VMIR imposes no internal proof obligations of its own. Consequently, the translator must emit a check alongside every generated call, meaning a manually crafted instruction stream could potentially apply a function without satisfying its preconditions.

Second, while Silicon applies propagation uniformly across all nested calls within a body, the translator evaluates propagation on a per-call basis and records this decision directly on the instruction. As a result, a client can only act upon the tokens of explicitly marked calls. This selective propagation restricts the client's term graph to relevant applications, though it introduces the burden of ensuring absolute accuracy in the marking process.

Third, Silicon translates function contracts directly into stated axioms. In the proposed encoding, however, each clause is an independent declaration, such as #vm[`f#requires`] or #vm[`f#ensures`], to which the function links. An axiom subsequently identifies a single opaque application, and the caller opens it using that member's specific token. Consequently, the facts of a contract are introduced through the same mechanism as any ordinary function call.

Finally, Silicon does not distinguish heap-independent functions; every function accepts a snapshot parameter, and every precondition is evaluated against the heap state. Conversely, the translator differentiates the two based on the syntactic presence of an #vi[acc] expression. Therefore, a heap-free function omits the snapshot parameter, and its precondition is treated as a boolean function.
