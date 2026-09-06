#import "../../macros.typ": *

== Symbolic Execution with Silicon <sec:bg-silicon>

Silicon @silicon is one of Viper's verification backends, and it operates by
symbolic execution. Silicon executes a program on symbolic values, each of
which stands for every concrete input at once, in the Smallfoot style
@smallfoot. The state it carries as it goes has three parts: a store mapping
each local variable to a symbolic value, a symbolic heap holding one chunk per
location the state has permission to, and a path condition recording every
assumption made to reach the current point.

#para[Execution model] Silicon encodes the questions it asks into SMT-LIB and
discharges them with the SMT solver Z3 @z3. The solver runs as a separate
process. Proving a goal means
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
subtracts it.

A lookup filters the sequence by the chunk's field or predicate, matches the
argument terms of the remaining chunks syntactically, and falls back to a solver
query against each candidate still standing. Two chunks whose argument terms
differ may still name the same location, since the equality of two terms is a
question for the solver. Silicon therefore consolidates the heap. It merges the
chunks whose arguments are known to be equal, summing their permission amounts
and equating the values they hold.

A merge of this kind runs whenever a chunk is added, and compares the new chunk
against those already held. A full consolidation compares every chunk against
every other potentially matching and repeats until no new equality is derived.
The filter by declaration confines every
comparison to chunks of the same field or predicate, but a full pass remains
cubic in the number of chunks in the worst case @silicon[Section 3.4.2].

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
it once, into the preamble it assembles after verifying a function. An application
supplies both of the axiom's
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


