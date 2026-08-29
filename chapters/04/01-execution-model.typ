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
e0: Int := fresh // a
e1: Bool := e0 == 42
assume e1
e2: Bool := e0 == 42
assert e2
```]

The variable #vi[a] corresponds to the temporary #vm[e0]. Since its declaration
lacks an initialiser, it translates to a #vm[`fresh`] instruction. Executing
this instruction establishes a new e-class for #vm[e0].

The #vi[`assume`] translates to two instructions: the equality #vm[e1] over
#vm[e0] and the literal #vm[`42`], and then the #vm[`assume`] itself. Executing
the equality introduces an #vm[==] node with those two e-classes as its
children, and the #vm[`assume`] merges #vm[e1] with #vm[`true`], which
consequently enforces #vi[a == 42]. We draw the graph either side of that merge
in @fig:egraph-first.

#figure(
  egraph-first,
  caption: [The e-graph of @lst:ex-v1 either side of the #vm[`assume`]
    instruction. A solid box is an e-node, a dashed box is the e-class holding
    it, and an arrow runs from a node to the class of each of its arguments. The
    #vm[`assume`] merges the class of the #vm[==] node with the class of
    #vm[`true`], drawn in orange. Re-stating the equality as #vm[e2] finds that
    node already in the graph, so #vm[e1] and #vm[e2] name the same class.],
) <fig:egraph-first>

The #vi[`assert`] similarly translates to two instructions. Restating the
equality as #vm[e2] locates the existing #vm[==] node in the graph, ensuring
#vm[e1] and #vm[e2] denote the same e-class. The #vm[`assert e2`] then compares
the e-classes of #vm[e2] and #vm[`true`], which the #vm[`assume`] previously merged.

We alter the program slightly to make the assertion non-trivial. @lst:ex-v2
declares #vi[a] to be #vi[10], adds #vi[32] to it, and then asserts that the
result is #vi[42]. Because the asserted equality is never explicitly stated
prior, the verifier cannot discharge it merely by finding a pre-existing node,
as it did in the previous example.

#lowering(
  caption: [A program expressing an obligation that `10 + 32 = 42`, and the
    corresponding VMIR translation.],
  label: "lst:ex-v2",
)[```viper
var a: Int := 10
a := a + 32
assert a == 42
```][```vmir
e0: Int := 10 // a
e1: Int := e0 + 32
e2: Bool := e1 == 42
assert e2
```]

The assertion #vm[assert e2] cannot establish equivalence to #vm[true] strictly
by comparing e-classes; it requires lightweight reasoning. We rely on Helium to
perform constant-folding via an _egg_ analysis over the e-graph. When #vm[e1] is
constructed, the children of the #vm[+] node are constant e-classes, #vm[10] and
#vm[32], which fold into #vm[42]. Consequently, when #vm[e2] is formed, both
children of the #vm[==] node share the same constant value, folding to #vm[true]
and successfully discharging the obligation.

@lst:ex-v3 needs more than structure and constant folding. It declares #vi[a]
and #vi[b], states the #vi[goal] #vi[`a * 2 == b * 2`], and then assumes
#vi[`a == b`], which effectively satisfies the goal. However, since neither side
of the goal is a constant, constant-folding alone is insufficient.

#lowering(
  caption: [A program whose obligation needs an assumed equality carried through
    congruence, and the corresponding VMIR translation.],
  label: "lst:ex-v3",
)[```viper
var a: Int
var b: Int
var goal: Bool := a * 2 == b * 2
assume a == b
assert goal
```][```vmir
e0: Int := fresh     // a
e1: Int := fresh     // b
e2: Int := e0 * 2    // a * 2
e3: Int := e1 * 2    // b * 2
e4: Bool := e2 == e3 // goal
e5: Bool := e0 == e1
assume e5
assert e4
```]

Helium discharges the assertion of @lst:ex-v3 with rewrite rules. The one that
fires first merges the e-classes of an equality's arguments once the equality
itself is proven:

$ (x = y) equiv "true" -> x equiv y $

This means that the e-classes of #vm[e0] and #vm[e1] are merged, so the two
#vm[`fresh`] now belong to the same e-class. Through congruence, an invariant of
the e-graph, #vm[e2] and #vm[e3] then point to the same e-class. Finally, the
goal #vm[`e2 == e3`] is discharged by another rewrite rule, reflexivity of
equality, stated as

$ x = x -> "true" $

@fig:egraph-saturate draws the two states either side of the saturation. On the
left the assumed equality sits in the class of #vm[`true`] and every other class
holds a single node. On the right the two #vm[`fresh`] share a class, the two
multiplications share another, and the goal has joined #vm[`true`]. Every node
on the right is one the instructions had already inserted: the rewriting merely merged
classes without constructing new nodes.

#figure(
  egraph-saturate,
  caption: [How the e-graph of @lst:ex-v3 evolves as the representation is
    saturated via rewrite rules. Nodes touched by rewrite rules are
    highlighted in orange.],
) <fig:egraph-saturate>

One aspect of verification omitted so far is that some operations are partial,
and a verifier has to check that each is applied only where it is well-defined.
@lst:safe-div divides by an unconstrained variable #vi[a], under a guard that
rules out the one value the division cannot take.

#viper(
  caption: [A division guarded by the test that makes it well-defined.],
  label: "lst:safe-div",
)[```viper
var a: Int
var b: Int := a != 0 ? 1 / a : 0
```]

The division introduces an obligation requiring #vi[a] to be non-zero. Since the
global fact-base lacks this guarantee---because the guard resides within the
expression itself rather than preceding it---Helium would normally reject the
program. VMIR addresses this with path conditions (PC for short). @lst:safe-div-vmir
lowering when an obligation is raised under a guard.

#vmir(
  caption: [The division is emitted as #vm[e3], guarded by the path condition
    #vm[`<e2>`] that states #vm[e0] is non-zero.],
  label: "lst:safe-div-vmir",
)[```vmir
e0: Int := fresh              // a
e1: Bool := e0 == 0           // e0 == 0
e2: Bool := e1 ? false : true // e0 != 0
e3: Int := <e2> 1 / e0
e4: Int := e2 ? e3 : 0        // b
```]

By default, Helium attempts to discharge obligations directly, by the
mechanisms described above. When unable to do so, it retries under the path
condition: when the obligation raised by #vm[e3] fails, Helium tries to prove
the implication $"e0" != 0 => "e0" != 0$ ($"PC" => "goal"$) instead. The
the implication enters the e-graph as the ternary $ternary(c, c, "true")$ with
$"e0" != 0$ for $c$, and the rewrite rule for that shape resolves it to
#vm[`true`]. The graph is not saturated immediately when the implication is added: an
earlier obligation might already have recorded the same implication as true, in which
case the proof succeeds instantly.

Finally, sometimes facts that are required to discharge the obligation are not
immediately available. Looking at @lst:ex-ite-decompose, the fact that
#vi[`f(x) == f(y)`] can only be learned once #vi[`x == y`] is.

#viper(
  caption: [The equality #vi[`f(x) == f(y)`], over an uninterpreted #vi[`f`], is
    reachable only after assuming #vi[b].],
  label: "lst:ex-ite-decompose",
)[```viper
var b: Bool
var x: Int
var y: Int
assume b ==> x == y
assert b ==> f(x) == f(y)
```]

Helium's last resort is to decompose the goal into an implication. The verifier
inspects the goal e-class for a ternary with a
constant #vm[`true`] arm, of which there are two shapes. In
$ternary(c, e, "true")$ the goal holds once $e$ holds under $c$, and in
$ternary(c, "true", e)$ it holds once $e$ holds under $not c$. The verifier
clones the e-graph, merges $c$ with #vm[`true`] or with #vm[`false`] as the
shape requires, and retries the goal $e$ in the clone, saturating it if the
cheaper checks leave the goal open. The surviving arm can hold another such
ternary, so the decomposition chains.

=== Formalising the mechanism

The examples above introduced the mechanism one capability at a time. This
subsection states the language the e-graph holds, the analysis it carries, and
the order in which Helium applies its proof tiers.

Every node in @fig:egraph-first and @fig:egraph-saturate is a term of one small
language, and the e-graph holds terms of that language alone. A variable enters
it as #vm[`fresh`], a constant as a literal, and #vm[`==`] and #vm[`*`] as
binary operators. @fig:term-language gives the grammar in full: those three
forms, the ternary, and three more that later sections need, namely a function
applied to its arguments, the cast that lifts an integer into the rationals, and
a quantifier.

#figure(
  term-language,
  kind: image,
  caption: [The language of terms an e-graph holds.],
) <fig:term-language>

The ternary is the only boolean connective, so every other one is spelled with
it: #vi[`a <= b`] reaches the verifier as $ternary(b < a, "false", "true")$ and
#vi[`a ==> b`] as $ternary(a, b, "true")$. A term has one of four types:
#vi[`Int`], #vi[`Bool`], #vi[`Real`] and #vi[`Ref`]. The types that describe a
heap location, a predicate's snapshot and a user-declared datatype arrive with
the sections that introduce those constructs.

The e-graph carries an _egg_ analysis that constant-folds. Each e-class records
the literal it evaluates to, when it has one: a literal node gives its own
value, and a node whose operands all record literals is evaluated. Merging two
classes merges their records, and two different literals make the class
_inconsistent_. A class that records a literal is merged with that literal, and
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
- *`goal_true`:* The verifier rebuilds the e-graph, which runs congruence
  closure over it and propagates the constant-folding analysis to a fixpoint,
  and then checks whether the goal e-class has been merged with #vm[`true`].
- *`implication_true`:* A tier that fires only for goals carrying a path
  condition. It replaces the obligation with the weakened
  $"PC" => "goal"$ and checks that instead.
- *`saturate`:* The e-graph is saturated with rewrite rules until the goal is
  met, or the representation is saturated. Running a saturation is a relatively
  expensive operation, so it runs only once the cheaper tiers have failed.
- *`implication_decompose`:* The most resource-intensive tier by far. It
  decomposes the goal into an implication chain, clones the e-graph, and assumes
  the antecedent in the clone, where the obligation is retried by the tiers
  above. Any work done in the clone is then thrown away, and the original
  e-graph records the discharged obligation alone. Inside a method body this
  tier clones once per basic block rather than once per obligation, which
  @sec:impl-cfg describes.

That is the whole of the mechanism. When no tier discharges the obligation,
Helium reports it as unproven. We chose to stop at this point, rather than
search harder, as a deliberate design choice: Helium is a lightweight verifier for
highly structured proof obligations, such as the ones raised by Prusti, rather
than a complete theorem prover.

This mechanism has real and obvious limits. First, Helium has no decision
procedure for arithmetic: an obligation like #vi[`a + b == b + a`] is reported
unproven, because rewriting only closes the identities Helium includes. Second,
Helium does not case split. A goal that needs reasoning by cases, beyond the
implication decomposition above, is reported unproven rather than forked on,
because even the cheapest case split would probe the graph once per branch on
every obligation that reaches it.

=== Performance considerations

The tiers above only help if each one stays cheap, and each stays cheap only
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

=== Comparison with Silicon

Silicon also verifies by symbolic execution, but it hands almost every
obligation to Z3, one round trip to an external process each. The tiers above
exist to avoid that trip: Helium answers from its own e-graph and, for now,
never calls a solver at all.

The deeper difference is how the two assume something. Z3 has push and pop, so
Silicon assumes a branch condition by pushing it, verifies the obligations under
it, and pops it on the way out, and a nested guard is one more push on the
stack. An e-graph has no such operation, because a merge cannot be undone.
Helium therefore assumes a condition by cloning the whole graph, merging in the
clone and discarding it afterwards, and a nested guard means a second clone from
the same base rather than a clone built on the first.

A clone costs far more than a push, which is why Helium reserves it for the
#vm[`implication_decompose`] tier instead of handling every path condition that
way. A push also buys reuse that a clone does not: what Silicon derives under
one stays there for the obligations that follow, while each of Helium's clones
starts from the same state and nothing it derives outlives it. A method body
recovers part of that, since one clone per block serves every obligation of the
block (@sec:impl-cfg), and what is left costs only where obligations nest
deeply, which is rare.
