#import "../../macros.typ": *
#import "../../figures/egraph-assume.typ": egraph-saturate
#import "../../figures/egraph-first.typ": egraph-first
#import "../../figures/term-language.typ": term-language
#import "../../figures/prove-ladder.typ": prove-ladder

== Execution Model <sec:impl-execution>

We show how Helium verifies a Viper program. We start from the simplest case a
verifier can process, a stream of heap-independent statements, and build up
through a sequence of small programs to the full mechanism by which an
obligation is discharged. The program in @lst:ex-v1 assumes a fact about an
integer and then trivially asserts it.

#lowering(
  caption: [A Viper program that assumes a fact and then asserts it, with its
    VMIR translation.],
  label: "lst:ex-v1",
)[```viper
var a: Int
assume a == 42
assert a == 42
```][```vmir
e0: Int := fresh
e1: Bool := e0 == 42
assume e1
e2: Bool := e0 == 42
assert e2
```]

A VMIR body is a sequence of instructions. An instruction either binds a
temporary, as the three #vm[`eN: TYPE :=`] lines above do, or acts without binding one, as
#vm[`assume`] and #vm[`assert`] do. VMIR has no nested expressions: the
right-hand side of a binding names one operator over its arguments, and each
argument is either a temporary bound earlier or a literal. The translation
flattens Viper's nested expressions into one instruction per operator.
Executing a binding (#vm[`:=`]) adds one e-node to the e-graph, recording the
e-class where the e-node lands, as a handle to refer to later.

The variable declaration (#vi[`var a: Int`]) in @lst:ex-v1 has no initialiser, so it is translated
to #vm[`fresh`]. Executing the line creates an unrelated e-node, which means
that #vm[e0] will now name a class that holds that node only.

The Viper #vi[`assume`] becomes two instructions. The first binds #vm[e1] to the
equality, adding an #vm[==] node over the class of #vm[e0] and the class of the
literal #vm[`42`]. The second (#vm[`assume e1`]) merges the class of #vm[e1] with the class of
#vm[`true`], which is what makes #vi[a == 42] hold. We draw the graph either side
of that merge in @fig:egraph-first.

#figure(
  egraph-first,
  caption: [The e-graph of @lst:ex-v1 either side of the #vm[`assume`]
    instruction. A solid box is an e-node, a dashed box is the e-class grouping
    equivalent e-nodes. An arrow from a node points to the e-classes of its arguments.
    A #vm[`fresh`] node is labelled with the type it produces and an index
    distinguishing it from every other #vm[`fresh`]. ],
) <fig:egraph-first>

The Viper #vi[`assert`] becomes two instructions in the same way. Binding #vm[e2] to
the equality finds the #vm[==] node the graph already holds over the same two
classes, so #vm[e1] and #vm[e2] name one class. #vm[`assert e2`] then asks
whether #vm[e2] names the class of #vm[`true`]. The #vm[`assume`] merged the
two, so it does, and the check passes.

We now slightly alter the program to make the assertion non-trivial. The
program below declares #vi[a] to be #vi[10], adds #vi[32] to it, and then asserts
that the result is #vi[42]. Because the asserted equality is never explicitly stated
prior, the verifier cannot discharge it merely by finding a pre-existing node,
as it did in the previous example.

#lowering(
)[```viper
var a: Int := 10
a := a + 32
assert a == 42
```][```vmir
e0: Int := 10 +i 32 // a
e1: Bool := e0 == 42
assert e1
```]

A declaration with an initialiser produces no instruction of its own. Translation
instead substitutes every occurrence of the variable with the temporary or
literal on the right-hand side of the assignment, here the literal
#vi[10]. The addition is therefore the body's first instruction, and both of its
operands are literals. The assertion
cannot be discharged by comparing e-classes and needs some reasoning.

Helium constant-folds with an _egg_ analysis over the e-graph. When #vm[e0] is
executed, both children of the #vm[+] node are constant e-classes, #vm[10] and
#vm[32], which fold the addition to #vm[42]. When #vm[e1] is executed, both children of the
#vm[==] node point to the same constant value's e-class. It means that this
is a comparison between two constants, and thus can be folded to its result, #vm[`true`], closing the obligation.

@lst:ex-v3 needs more than structure and constant folding. It declares two
unconstrained integers #vi[a] and #vi[b], binds the #vi[goal] to
#vi[`a * 2 == b * 2`], and only then assumes #vi[`a == b`]. Neither side of the
goal is a constant, so the analysis of the previous example computes nothing
here, and the goal is a different node from the equality the assumption proved.

#lowering(
  caption: [A program whose obligation needs an assumed equality carried through
    congruence, and the corresponding VMIR translation.],
  label: "lst:ex-v3",
)[```viper
var a: Int, b: Int
var goal: Bool := a * 2 == b * 2
assume a == b
assert goal
```][```vmir
e0: Int := fresh     // a
e1: Int := fresh     // b
e2: Int := e0 *i 2   // a * 2
e3: Int := e1 *i 2   // b * 2
e4: Bool := e2 == e3 // goal
e5: Bool := e0 == e1
assume e5
assert e4
```]

Helium discharges the assertion of @lst:ex-v3 with two rewrite rules of
different shapes. Both match a pattern in the graph, and $x equiv y$ states that
the two terms share an e-class. The first rule is conditional, and its effect is
a merge, so it is written as an implication between e-class memberships:

$ "IF" (x = y) equiv "true" "THEN" x equiv y $

The premise holds because #vm[`assume e5`] put the equality in the class of
#vm[`true`], so the rule merges the e-classes of #vm[e0] and #vm[e1] and the two
#vm[`fresh`] now belong to one e-class. Through congruence, an invariant of the
e-graph, #vm[e2] and #vm[e3] then point to the same e-class.
The second rule is an ordinary term rewrite, reflexivity of equality: an
equality between a term and itself is #vm[`true`].

$ x = x -> "true" $

Its pattern demands one term on both sides, which the goal #vm[`e2 == e3`] now
satisfies because congruence merged the two multiplications. The goal therefore
joins the class of #vm[`true`] and the assertion is discharged.

@fig:egraph-saturate draws the two states either side of the saturation. On the
left the assumed equality sits in the class of #vm[`true`] and every other class
holds a single node. On the right the two #vm[`fresh`] share a class, the two
multiplications share another, and the goal has joined #vm[`true`]. Every node
on the right is one the instructions had already inserted: the rewriting merely merged
classes without constructing new nodes.

#figure(
  egraph-saturate,
  caption: [How the e-graph of @lst:ex-v3 evolves as the representation is
    saturated via rewrite rules. Both panels hold the same nodes, and differ
    only in how the classes group them.],
) <fig:egraph-saturate>

One aspect of verification omitted so far is that some operations are partial,
and a verifier has to check that each is applied only where it is well-defined.
The program below divides by an unconstrained variable #vi[a], under a guard
that rules out the one value the division cannot take.

#no-numbers[```viper
var a: Int
var b: Int := a != 0 ? 1 / a : 0
```]

The division introduces an obligation requiring #vi[a] to be non-zero. If translated
naively, there would be nothing constraining #vi[a], so Helium would reject
this program. VMIR addresses this with path conditions (PC for short), extra assumptions
that can be made when processing an instruction. The lowering below guards the
division, emitted as #vm[e3], with such a path condition.

#no-numbers[```vmir
e0: Int := fresh              // a
e1: Bool := e0 == 0
e2: Bool := e1 ? false : true // a != 0
e3: Int := <e2> 1 /i e0
e4: Int := e2 ? e3 : 0        // b
```]

An obligation raised under a path condition is discharged as an implication.
Helium first asks whether the goal is unconditionally true. This fails here, so
instead it tries checking the weakened obligation
$"PC" => "goal"$ in its place.

The obligation of #vm[e3] is that #vm[e0] is non-zero, which is exactly what
#vm[e2] states. The weakened goal in this case becomes $"e2" ==> "e0" != 0$. With
$"e0" != 0$ being exactly the definition of #vm[e2], the implication becomes
$"e2" ==> "e2"$, which
is trivially rewritten to simply #vm[`true`], discharging the obligation.

Finally, sometimes facts that are required to discharge the obligation are not
immediately available. In the program below, over an uninterpreted #vi[`f`], the
fact that #vi[`f(x) == f(y)`] can only be learned once #vi[`x == y`] is.

#no-numbers[```viper
var b: Bool, x: Int, y: Int
assume b ==> x == y
assert b ==> f(x) == f(y)
```]

Helium's last resort is to decompose such a goal. The verifier searches the
goal's e-class for an implication $c ==> "goal"'$. Once found, we make a fresh clone
of the e-graph and assume $c$. The idea here is that this will unblock more facts to
propagate, which would then allow to prove the new $"goal"'$.

The goal of that program is the implication #vi[`b ==> f(x) == f(y)`],
so #vi[b] is the condition assumed in the clone and #vi[`f(x) == f(y)`] is the
new goal. Assuming #vi[b] unblocks the assumption
#vi[`b ==> x == y`], whose conclusion #vi[`x == y`] now holds outright. That
equality merges the e-classes of #vi[x] and #vi[y], congruence merges
#vi[`f(x)`] with #vi[`f(y)`], and reflexivity of equality puts the new goal in
the class of #vm[`true`].

#para[Formalising the mechanism] The examples above introduced the mechanism one
capability at a time. We now state the language the e-graph holds, the analysis
it carries, and the order in which Helium applies its proof tiers.

Every node in @fig:egraph-first and @fig:egraph-saturate is a term of one small
language, and the e-graph holds terms of that language alone. A variable enters
it as #vm[`fresh`], a constant as a literal, and #vm[`==`] and #vm[`*i`] as
binary operators. @fig:term-language gives the grammar in full: those three
forms, the ternary, and three more that later sections need, namely a function
applied to its arguments, the cast that lifts an integer into the rationals, and
a quantifier. Later listings keep the surface operator
wherever spelling out its ternary would only introduce unnecessary clutter.

#figure(
  term-language,
  kind: image,
  caption: [The language of terms an e-graph holds. An arithmetic or ordering
    operator carries its operand sort as a subscript, and #vm[`mod`] and
    equality need none.],
) <fig:term-language>

The ternary is the only boolean connective, so every other one is spelled with
it: #vi[`!a`] reaches the verifier as $ternary(a, "false", "true")$ and
#vi[`a ==> b`] as $ternary(a, b, "true")$. The comparisons collapse the same
way, onto the one ordering the grammar names: #vi[`a <= b`] arrives as
$ternary(b < a, "false", "true")$. Unary minus is the remaining operator Viper
has and VMIR does not, and it lowers to $0 - a$, which leaves the
integer-to-rational cast as the only unary form. Later listings keep the surface
operator wherever spelling out its ternary would only lengthen the line.
The types a term can have are
#vi[`Int`], #vi[`Bool`], #vi[`Real`], #vi[`Ref`], and the location types, ADTs
and domains that arrive with the sections introducing those constructs.

The e-graph carries an _egg_ analysis that performs constant folding. Each e-class records
the literal it evaluates to, when it has one: a literal node gives its own
value, and a node whose operands all record literals is evaluated. Merging two
classes merges their records, and two different literals make the class
inconsistent. A class that records a literal is merged with that literal, and
one inconsistent class makes the whole e-graph inconsistent, from which anything
is provable.

Helium is a tiered prover: it attempts an obligation with the cheapest mechanism
first and commits more resources only when that one fails. The tiers are the
capabilities the examples introduced, in the same order, preceded by one more.
@fig:prove-ladder gives the ladder, and the list below describes what each tier
does before handing the work to the next.

#figure(
  prove-ladder,
  caption: [Helium uses a tiered prover to discharge obligations, with each tier
    progressively being more expensive to run than the last.],
) <fig:prove-ladder>

- *`inconsistent`:* The cheapest tier. The analysis has already recorded whether
  the e-graph is inconsistent, so the check costs a lookup rather than a search.
  A block whose path condition is itself contradictory is closed here too, on a
  verdict reached once when the block was entered rather than rediscovered per
  obligation.
- *`goal_true`:* The verifier rebuilds the e-graph, which runs congruence
  closure over it and propagates the constant-folding analysis to a fixpoint,
  and then checks whether the goal e-class has been merged with #vm[`true`].
- *`implication_true`:* A tier that fires only for goals carrying a path
  condition. It replaces the obligation with the weakened
  $"PC" => "goal"$ and checks that instead. An earlier obligation may already
  have recorded that implication as true, in which case this tier answers from
  the record.
- *`saturate`:* The e-graph is saturated with rewrite rules until the goal is
  met, or the representation is saturated. Running a saturation is a relatively
  expensive operation, so it runs only once the cheaper tiers have failed.
- *`implication_decompose`:* The most resource-intensive tier by far. It
  decomposes the goal into an implication chain, clones the e-graph, and assumes
  the antecedent in the clone, where the obligation is retried by the tiers
  above. Any work done in the clone is then thrown away, and the original
  e-graph records the discharged obligation alone.

The four cheaper tiers read the e-graph the verifier already holds, so each is a
lookup or a rewrite over the facts that hold on every path. Only
#vm[`implication_decompose`] reads a graph with the path condition assumed, and
the ladder exists for that separation: assuming a condition costs a copy of the
whole e-graph, so the copy is reserved for the obligations the other four leave
open.

When no tier discharges the obligation, Helium reports it as unproven. We chose to stop at this point, rather than
search harder, as a deliberate design choice: Helium is a lightweight verifier for
highly structured proof obligations, such as the ones raised by Prusti, rather
than a complete theorem prover.

The mechanism has two limits. First, Helium has no decision
procedure for arithmetic: an obligation like #vi[`a + b == b + a`] is reported
unproven, because rewriting only closes the identities Helium includes. Second,
Helium does not case split. A goal that needs reasoning by cases, beyond the
implication decomposition above, is now reported unproven.

Neither limit is inherent to the design.
An obligation Helium reports unproven is an ordinary first-order goal over the
facts the e-graph holds, so it can be handed to a heavyweight prover such as Z3,
leaving the ladder as a cheap filter that answers the bulk of the stream ahead of
it. @sec:future-work develops that hybrid.

#para[Performance considerations] The tiers above only help if each one stays cheap, and each stays cheap only
while the e-graph stays small. Keeping it small drove two design choices, both
about booleans, since most of what a verifier reasons about is which facts hold
under which conditions.

First, the single boolean connective: writing $or$, $and$, $not$ and $=>$ as
ternaries gives them one canonical representation, so Helium never needs a rule
relating two spellings of the same proposition, such as
$p => q equiv not p or q$.

Second, when picking which rewrite rules to include, we favoured ones that add
no new e-nodes. A rule like $ternary(x, x, "false") -> x$ or
$ternary("true", x, y) -> x$ only uses nodes its left-hand side already binds,
so applying it merely unions existing e-classes. This ruled out distributivity,
associativity, and commutativity: a rule such as
$(ternary(x, y, z)) > w -> (ternary(x, y > w, z > w))$ would be useful, but its
right-hand side names a term the left-hand side does not already contain, and
applying it repeatedly blows up the e-graph exponentially in the
depth of the ternary tower. The cost is completeness: Helium is often unable
to prove obligations that look trivial to the human eye.
@sec:appendix-rewrites lists every rewrite rule Helium includes.

#para[Comparison with Silicon] Silicon also verifies by symbolic execution, but it hands almost every
obligation to Z3, one round trip to an external process each. The tiers above
exist to avoid that trip: Helium answers from its own e-graph and, for now,
never calls a solver at all.

The two differ more deeply in how they assume something. Z3 has push and pop, so
Silicon assumes a branch condition by pushing it, verifies the obligations under
it, and pops it on the way out, and a nested guard is one more push on the
stack. That trail is a feature of Z3's role as a backtracking SMT solver, not
something every e-graph library provides: egglog's own push and pop clone the
database underneath, and _egg_, the library Helium builds on, offers no undo at
all, only `Clone`. Helium therefore assumes a condition by cloning the whole
graph, merging in the clone and discarding it afterwards, and a nested guard
means a second clone from the same base rather than a clone built on the first.

A clone copies the whole e-graph where a push records a scope marker, which is why Helium reserves it for the
#vm[`implication_decompose`] tier instead of handling every path condition that
way. A push also enables reuse that a clone does not: what Silicon derives under
one stays there for the obligations that follow, while each of Helium's clones
starts from the same state and nothing it derives outlives it. A method body
recovers part of that, since one clone per block serves every obligation of the
block (@sec:impl-cfg), and what is left costs only where obligations nest
deeply, which is rare.
