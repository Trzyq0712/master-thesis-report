#import "../../macros.typ": *

== Functions <sec:impl-functions>

Every function the preceding sections have used is uninterpreted. A field
declaration becomes a location function, a predicate gains one for its
instances, and a domain declares a family of them. In each case an application
is an opaque token that does not relate to any computation or value, which is all
those three constructs ask for. A Viper #vi[`function`] can do more: it may have a
contract and a body that the definition should unfold to.

@sec:bg-silicon describes how Silicon axiomatises such a function. VMIR reaches
the same end by a different route, and this section covers where the two part.
@lst:fn-contract lowers a function carrying a precondition, a postcondition and
a body, and the section works from it.

#lowering(
  caption: [Both clauses become functions of their own, and the declaration links to #vm[`div#ensures`].],
  label: "lst:fn-contract",
  placement: auto,
  stacked: true,
)[```viper
function div(s: Int, n: Int): Int
  requires n != 0
  ensures s == 0 ==> result == 0
{
  s \ n
}
```][```vmir
function div#requires(e0: Int, e1: Int): Bool
{
  e2: Bool := e1 != 0
  result: e2
}

function div#ensures(e0: Int, e1: Int, e2: Int): Bool
{
  e3: Bool := e0 == 0
  e4: Bool := e2 == 0
  e5: Bool := e3 ? e4 : true
  result: e5
}

function div(e0: Int, e1: Int): Int
  ensures div#ensures(e0, e1, result)
{
  e2: Bool := div#requires(e0, e1)
  assume e2
  e3: Int  := e0 /i e1
  e4: Bool := div#ensures(e0, e1, e3)
  assert e4
  result: e3
}
```]

#para[Preconditions] A precondition constrains the parameters of a function, and
for a heap-free function the translator lowers it to a boolean #vm[`#requires`]
function. The clause of #vi[`div`] becomes #vm[`div#requires`], a declaration
of its own rather than a part of the function, and the lowering below applies it
at a call, where the precondition check is an instruction standing on its own.

#lowering(
)[```viper
method client(k: Int)
{
  var v: Int := div(10, k)
}
```][```vmir
method client {
  e0: Int  := fresh      // k
  e1: Bool := div#requires(10, e0)
  assert e1              // fails
  e2: Int  := div(10, e0)
}
```]

The call site asserts an application of #vm[`div#requires`] at the arguments,
and that assertion is a separate instruction standing ahead of the call. VMIR
raises no obligation at an application itself, so an instruction stream could
apply #vi[`div`] without the assertion; the translator guarantees the check by
emitting one before every call it writes, and for a function with no
precondition it emits nothing.

A call also mints a term the translator never writes, a _precondition token_.
One uninterpreted symbol per function, #vm[`div%pre`], is minted at each
syntactic call on that call's arguments and assumed true under the call's path
condition:

$ "PC" => f"%pre"(overline(x)) $

A call in one arm of a conditional therefore lowers to
#no-numbers[```vmir
e2: Int := <e0> div(10, k)
```]
and its token is assumed under #vm[`e0`] alone, which keeps a fact released at
one call from reaching a sibling branch that never made it. The token licenses
the definitional equation, so a function unfolds only where that would be sound:

$ {f"%pre"(overline(x))} f"%pre"(overline(x)) => f(overline(x)) = "body"_f (overline(x)) $

#para[Postconditions] An #vi[`ensures`] clause lowers to a boolean function the
way a #vi[`requires`] clause does, over the parameters and one more for the
result, which is what #vi[`result`] in the clause lowers to. Unlike the
precondition it stays attached to the declaration: #vi[`div`] carries a link to
#vm[`div#ensures`], and a caller reads what the function promises from that link
rather than from an instruction the translator emitted beside the call. The same
construction serves a function with a body and one without.

Write $p$ for the member the link names. At an occurrence the token releases the
link alongside the definitional equation:

$ {f"%pre"(overline(x))} f"%pre"(overline(x)) => p(overline(y)) and p"%pre"(overline(y)) $

Here $overline(y)$ is the argument list the link records, built from the
parameters $overline(x)$ and carrying the application $f(overline(x))$ in the
result position. The first conjunct states that $p$ holds where the token is
present, and the second releases $p$'s own token, which is what lets the caller
open $p$'s body.

#para[Choosing what propagates] Silicon propagates the preconditions of every
call a body makes (@sec:bg-silicon). VMIR records that decision per call
instead. Every call in a body carries a mark, written #vm[`export`], saying
whether instantiating the body at a client re-releases that callee's token
there. A marked call releases its token under two guards, the token that
licensed the instantiation and the path condition the call sits under inside the
body:

$ {f"%pre"(overline(x))} f"%pre"(overline(x)) and "PC"_g(overline(y)) => g"%pre"(overline(y)) $

Here $g(overline(y))$ is the call the body makes, and $overline(y)$ its
arguments, built from $overline(x)$ by the steps of the recipe that precede it.
Setting the mark is the translator's decision, recorded on the instruction,
because the translator knows why it emitted the call. Marking selectively
confines a client's term graph to the applications that matter, at the cost of
having to mark accurately. The lowering below takes a caller for #vi[`div`]
whose one expression makes both kinds of call: the precondition check is an
obligation and stays bare, and the application whose value #vi[`half`] returns is
marked.

#lowering(
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

The call to #vm[`div`] is marked because #vi[`half`] returns its value, so a
client's instantiation produces that application and needs the token to open
it. The #vm[`div#requires`] check beside it is an obligation: it unfolds to
#vi[`2 != 0`], the verifier discharges it while checking #vi[`half`], and the
recipe a client instantiates omits it entirely. A caller that applies #vi[`half(k)`] mints
#vm[`half%pre(k)`], the one token written at that call site. The token releases
#vi[`half`]'s definitional equation,

$ "half%pre"(s) => "half"(s) = "div"(s, 2), $

and the instantiation that produces #vm[`div(k, 2)`] mints that call's own token
alongside it, meaning that the #vm[`div`] inside was applied safely:

$ "half%pre"(s) => "div%pre"(s, 2). $

With #vm[`div%pre(k, 2)`] present, #vi[`div`]'s equation fires at those
arguments,

$ "div%pre"(s, 2) => "div"(s, 2) = s \/ 2, $

so the caller eventually gets #vm[`half(k) == k /i 2`]. Three rules fired in
sequence, each licensed by a token the one before it minted, and the caller
never proved #vi[`2 != 0`] for itself.

#para[Contracts inside the body] Where a function has a body, the translation
puts both clauses inside it. The body of #vi[`div`] opens by assuming
#vm[`div#requires`] at the parameters, and that assumption discharges
the division obligation: #vm[`div#requires`] has a body of its own, so the
assumed application unfolds to #vm[`e1 != 0`]. The body closes by asserting
#vm[`div#ensures`] at the value it returns, which the verifier discharges
locally without retaining it. Where there is a precondition the postcondition
member assumes it first, so a clause whose well-definedness rests on the
precondition is checked in the state that precondition describes.

#para[Recursive functions] A function that calls itself would instantiate its
own recipe without end. The translation removes the recursion before the
verifier sees it, using the _limited twin_ @sec:bg-silicon describes for
Silicon: it detects the cycle and emits a second function #vm[`length#lim`]
carrying the same #vi[`ensures`] and no body, a body whose recursive call is
retargeted to that twin, and an axiom relating the two. Because the twin has no
body, an instantiation of #vm[`length`]'s recipe lands on #vm[`length#lim`] and
stops there.

#lowering(
  caption: [The length of a list. The translation emits a bodyless twin,
    retargets the recursive call to it, and states one axiom relating the two.],
  label: "lst:fn-recursive",
  placement: auto,
  stacked: true,
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
function length#lim(e0: List): Int
  ensures length#ensures(e0, result)

function length(e0: List): Int
  ensures length#ensures(e0, result)
{
  e1: Int  := List@tag(e0)
  e2: Bool := e1 == 0
  e3: List := List::Cons.1(e0)
  e4: Int  := <!e2> export length#lim(e3)
  e5: Int  := 1 +i e4
  e6: Int  := e2 ? 0 : e5
  e7: Bool := length#ensures(e0, e6)
  assert e7
  result: e6
}

axiom length#lim {
  e0: Bool := forall e0: List :: {length(e0)} {
    e1: Int  := length(e0)
    e2: Int  := length#lim(e0)
    e3: Bool := e1 == e2
    result: e3
  }
  result: e0
}
```]

The axiom is an ordinary quantifier of the kind @sec:impl-data describes, and
its trigger is the full application. A match at #vm[`length(l)`] mints the twin
at the same arguments and merges the two e-classes, while the #vm[`length#lim`]
an instantiation produced matches nothing and unfolds no further. An untriggered
equality would let the twin unfold back into the function, and the matching loop
would return. The merge carries every fact a caller establishes of
#vm[`length`] at those arguments to the #vm[`length#lim`] a sibling
instantiation produced. Recursion therefore needs no mechanism of its own, since
the same rule that instantiates every other quantifier instantiates this axiom
too.

The twin needs nothing else. It is a bodyless function carrying an
#vi[`ensures`], so it leaves a guarded axiom over its result, and the recursive
call carries the #vm[`export`] mark, which releases the token that opens it
wherever the recipe is instantiated. The declaration's promise therefore reaches
the twin by the ordinary route: the recursive call contributes
#vm[`length#lim(e3) >=i 0`], the fact the exit assertion needs of the recursive
arm. The definitional equation stays keyed on the full application, so it never
fires on the twin the recipe produced.

Complete support for recursion does not imply full functional support. We cannot
verify the #vm[`length`] function of @lst:fn-recursive, because its functional
specification would need a case analysis, which we deliberately lack. Removing
that #vi[`ensures`] clause makes the verification succeed.

#para[Heap-dependent functions] A precondition that grants permission cannot be
a boolean function, because it describes a heap fragment together with an
assertion about it. Such a precondition is a resource, and
@sec:impl-predicates already lowers one. The function itself then takes the
resource's snapshot as a trailing argument. Every permission amount in that
resource becomes a #vm[`wildcard`] where it is positive and zero where it is
not, matching Silicon's default. A heap-dependent postcondition takes the
snapshot as a trailing parameter of its own, so that it can read the pre-state
the precondition describes, as @lst:fn-heapdep shows.

#lowering(
  caption: [The precondition becomes a resource, the function takes that resource's snapshot as a trailing parameter, and the call site produces the snapshot by exhaling the resource. That exhale discards its heap into #vm[`_`], and the call itself takes no heap operand.],
  label: "lst:fn-heapdep",
  placement: auto,
  target-lang: "lvmir",
  stacked: true,
)[```viper
field val: Int

function get(c: Ref): Int
  requires acc(c.val)
{
  c.val
}
//@
var v: Int := get(x)
```][```lvmir
resource get#requires(e0: Ref) {
  h0 := empty + val(e0) @ wildcard with self
  result: (h0, true)
}

function get(e0: Ref, e1: get#requires@snap): Int
{
  h0 := empty inhale get#requires(e0) @ wildcard with e1
  e2: Int := *[h0] val(e0)
  result: e2
}
//@
_, e2 := h0 exhale get#requires(e0) @ wildcard
e3: Int := get(e0, e2)
```]

The body's opening instruction widens the snapshot parameter back into a heap,
as a method postcondition does with its own snapshot parameter
(@sec:impl-methods). The read that follows raises the sufficiency obligation any
dereference raises against the heap the inhale built. A precondition naming a
predicate instance lowers to a resource the same way, and the body opens the
instance with the unfold pair of @sec:impl-predicates before it reaches a field.

The call site pays for that snapshot with an exhale of the resource. The exhale
is frame-only: it proves the footprint is held and yields the snapshot, and the
heap it would otherwise produce is never built. Nothing consumes that heap, so
the caller goes on with the one it already had, and the call takes no permission
away.

VMIR therefore has no heap-dependent function form. #vi[`get`] takes parameters
and returns a value, the snapshot is one of those parameters, and
#vm[`get(e0, e2)`] is the instruction any other call emits. The exhale standing
beside that call makes the function heap-dependent. Once the body is
verified even that is behind it: a term over #vi[`get`]'s two parameters
remains, instantiated at each occurrence on the caller's arguments and the
snapshot it exhaled, with no heap consulted anywhere. The heap the body reasoned
about survives as the snapshot it was summarised into. Silicon gives every
function a snapshot parameter and evaluates every precondition against the heap
(@sec:bg-silicon); the translator distinguishes the two cases on the syntactic
presence of an #vi[`acc`] expression, so a heap-free function carries no
snapshot and its precondition is a boolean function.

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

#para[Comparison with Silicon] Silicon unfolds a recursive heap-dependent
definition one level at each unfold of the surrounding predicate
(@sec:bg-silicon). Helium has no counterpart: a recipe is instantiated where its
trigger matches, and an unfold produces no term the definitional equation is
keyed on. Silicon also states a function's contract as axioms it asserts
directly, whereas each clause here is an independent declaration the function
links to, so the facts of a contract arrive through the mechanism that carries
any other call.
