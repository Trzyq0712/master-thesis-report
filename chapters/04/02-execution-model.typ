#import "../../macros.typ": *
#import "../../figures/egraph-assume.typ": egraph-saturate
#import "../../figures/prove-ladder.typ": prove-ladder

== Verifying Client Code with VMIR and Helium <sec:impl-execution>

We will show how Helium verifies a Viper program, starting from the simplest
case a verifier can process, a stream of heap-independent statements, and
building up, through a single running example, to the full mechanism by which
obligations are discharged.

The program in @lst:ex_v1 assumes a fact about an integer and then trivially
asserts it.

#lowering(
  caption: [Viper program that assumes a fact, asserts it; and the VMIR
    translation.],
  label: "lst:ex_v1",
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

The variable #vi[a] becomes a temporary #vm[e0] in VMIR. As the declaration of
#vi[a] has no explicit initialiser, it is lowered to a #vm[`fresh`] instruction.
When the verifier executes the instruction, it creates a new e-class in the
e-graph, and #vm[e0] becomes a handle for it.

Following that, the #vi[`assume`] is translated to two VMIR instructions: first
the equality check #vm[e1], using the #vm[e0] temporary and a constant
#vm[`42`], and then the #vm[`assume`] instruction. The equality check is
executed by inserting a new #vm[==] node into the e-graph with the #vm[e0] and
#vm[42] e-classes as its children. The #vm[assume] instruction then merges
#vm[e1] with #vm[true], which means that #vi[a == 42] now holds.

Finally, #vi[assert a == 42] is lowered to two instructions. First the equality
#vm[e0 == 42] is restated as #vm[e2]. The verifier executes it the same way as
#vm[e1] above. This time, however, the e-graph already contained the same
e-node, making the #vm[e1] and #vm[e2] handles point to the same e-class.
Second, the #vm[assert e2] is executed by checking whether the e-classes of
#vm[e2] and #vm[true] match, which they do due to #vm[assume e1] above.

We will slightly alter the program to make the assertion non-trivial. @lst:ex_v2
lists a program that declares #vi[a] to be equal to #vi[10], and then asserts
that #vi[a + 32] is equal to #vi[42].

#lowering(
  caption: [A program expressing an obligation that `10 + 32 = 42`, and the
    corresponding VMIR translation.],
  label: "lst:ex_v2",
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

The #vm[assert e2] cannot directly prove that #vm[e2] is equivalent to
#vm[true]; this requires some lightweight reasoning. Concretely, Helium employs
constant folding enabled by _egg_'s analyses. When #vm[e1] is built, the two
children of the #vm[+] node are e-classes with constant values, #vm[10] and
#vm[32], which constant-fold to #vm[42]. Afterwards, when #vm[e2] is built, the
two children of #vm[==] carry the same constant value, which folds to #vm[true],
allowing the verifier to discharge the obligation.

@lst:ex_v3 expresses an obligation that cannot be closed by structure and
constant folding alone. It declares two variables #vi[a] and #vi[b] and states a
#vi[goal] of #vi[`a * 2 == b * 2`]. The fact holds if #vi[a] and #vi[b] are
equal, which is assumed in the next line. We expect the verifier to be able to
prove the goal.

#lowering(
  caption: [],
  label: "lst:ex_v3",
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

Helium discharges the assertion from @lst:ex_v3 by employing rewrite rules. The
rule used here states that a proven equality (#vm[`e0 == e1`]) merges the
e-classes of the arguments. It can be formally expressed as:

$ (x = y) equiv "true" -> x equiv y $

This means that the e-classes of #vi[`e0`] and #vi[e1] are merged (the two
#vi[fresh] now belong to the same e-class). Through congruence, an invariant of
the e-graph, #vi[e2] and #vi[e3] then point to the same e-class. Finally, the
goal #vm[`e2 == e3`] is discharged by another rewrite rule, reflexivity of
equality, stated as

$ x = x -> "true" $

To complete the picture, @fig:egraph-saturate visualises how the e-graph changes
after saturating the representation using the rewrite rules.

#figure(
  egraph-saturate,
  caption: [How the e-graph of @lst:ex_v3 evolves as the representation is
    saturated via rewrite rules. Nodes touched by rewrite rules are
    highlighted in orange.],
) <fig:egraph-saturate>

One important aspect of verification that has been omitted thus far is that some
operations are partial. The verifier must ensure they are only ever applied in a
state where they are well-defined. Take the example from @lst:safe-div below,
which attempts to divide by an unconstrained variable #vi[a].

#viper(
  caption: [Safe division implementation, #vi[a] is ensured non-zero before
    division.],
  label: "lst:safe-div",
)[```viper
var a: Int
var b: Int := a != 0 ? 1 / a : 0
```]

As expected, Helium would raise a non-zero division obligation when reaching the
#vi[`1 / a`] instruction. However, there would be nothing in the global
fact-base that would rule out #vi[a] equaling zero, so Helium would reject the
program and the obligation would remain unproven. To avoid this, VMIR employs a
notion of path conditions (PC for short). @lst:safe-div-vmir shows how Viper is
lowered to VMIR, when an obligation is raised under a guard.

#vmir(
  caption: [The division #vm[`1 / e0`] is released under the guard PC
    #vm[`<e2>`]],
  label: "lst:safe-div-vmir",
)[```vmir
e0: Int := fresh              // a
e1: Bool := e0 == 0           // e0 == 0
e2: Bool := e1 ? false : true // e0 != 0
e3: Int := <e2> 1 / e0
e4: Int := e1 ? e2 : 0        // b
```]

By default, Helium attempts to discharge obligations directly -- by the
mechanisms described above. When unable to do so, it retries under the path
condition: when the obligation raised by the division on line 3 fails, Helium
tries to prove the implication $"e0" != 0 => "e0" != 0$ ($"PC" => "goal"$)
instead. The implication is thus added to the e-graph (via a ternary chain). The
implication will collapse to $x ? x : "false"$ with $"e0" != 0$ for $x$, which
will then simply identity-rewrite to $"true"$. Notably, after adding the
implication to the e-graph, it is not saturated immediately. It might happen
that the implication has already been proven and recorded true in the e-graph,
short-circuiting the proof.

Finally, sometimes facts that are required to discharge the obligation are not
immediately available. Looking at @lst:ex-ite-decompose, the fact that
#vi[`f(x) == f(y)`] can only be learned once #vi[`x == y`] is.

#viper(
  caption: [Equality #vi[`f(x) == f(y)`] is reachable only after assuming
    #vi[b].],
  label: "lst:ex-ite-decompose",
)[```viper
var b: Bool, x: Int, y: Int
assume b ==> x == y
assert b ==> f(x) == f(y)
```]

For such cases, Helium employs a last-resort mechanism, which is to decompose
the goal into an implication. This is done by inspecting the goal e-class and
looking for two kinds of nodes: $x ? "false" : y$ or $x ? y : "false"$. The
verifier follows this chain, decomposing the goal into an implication. The
e-graph state is then cloned, and the antecedent is assumed in the clone with
matching polarity ($x$ from above merged with #vm[`true`] or #vm[`false`]
depending on $y$ 's position). If necessary, the clone is rewrite-saturated to
check if the goal is provable.

#para[Formalising the mechanism] The examples above show how one would discharge
an obligation; we now state precisely how Helium does it. The proof strategy is
summarized by the diagram in @fig:prove-ladder: our verifier is a tiered prover,
where each tier progressively commits more resources to discharge the
obligation.

#figure(
  prove-ladder,
  caption: [Helium uses a tiered prover to discharge obligations, with each tier
    progressively being more expensive to run than the last.],
) <fig:prove-ladder>

We describe in more detail what each verification tier does, before handing off
the work to the next one.

- *`inconsistent`:* This tier has not yet been shown above; it is the simplest
  and cheapest one. It checks whether the e-graph has reached an inconsistent
  state. This is not explicitly searched for, but recorded as it happens -- for
  example, when an e-class holds two different constants, the simplest case
  being #vm[`true`] equated with #vm[`false`]. It is logically sound: if the
  premise, the e-graph's truth state, is inconsistent, any obligation follows.
- *`goal_true`:* Here the verifier checks if the goal e-class has been unioned
  with #vm[`true`]. It also rebuilds the e-graph, which runs the
  constant-folding analysis and can discharge the goal that way.
- *`implication_true`:* This is a tier that only fires for goals with an
  explicit path condition. It replaces the original obligation with the weakened
  one -- $"PC" => "goal"$.
- *`saturate`:* The e-graph is saturated with rewrite rules until the goal is
  met, or the representation is saturated. Running a saturation is a relatively
  expensive operation, so we deliberately run it once the cheaper tiers have
  been insufficient.
- *`implication_decompose`:* This is the most resource-intensive tier by far. It
  proves the goal by decomposing it into an implication chain, cloning the
  e-graph and assuming the antecedent of the implication in the clone. The
  obligation is then retried using the tiers above -- checking for
  inconsistency, checking if the goal is true, and finally saturating the
  representation. Any work that has been done in the clone e-graph is then
  thrown away, and in the original e-graph we only record successfully
  discharging the original obligation by assuming it true.

This concludes the mechanism by which Helium attempts to discharge obligations.
If unsuccessful, the verifier reports the obligation as unproven. Stopping at
this point, rather than searching harder, is a deliberate design choice: Helium
is not a complete theorem prover, but a lightweight verifier for highly
structured proof obligations, such as the ones raised by Prusti.

This mechanism has real and obvious limits. First, Helium has no decision
procedure for arithmetic: an obligation like #vi[`a + b == b + a`] is
reported unproven,
because rewriting only closes the identities Helium includes. Second, Helium
does not case split. A goal that needs reasoning by cases, beyond the simple
implication decomposition, is reported unproven rather than forked on, because
even the cheapest case split would probe the graph once per branch on every
obligation that reaches it.

#para[Performance considerations] The tiers above only help if each one
stays cheap. A principled ordering does not save a verifier whose own rules
make the e-graph blow up: it just reaches the same explosion in a more
orderly way. Keeping the e-graph size under control has been the main
concern throughout, and it drove two design choices. Most of what
a verifier reasons about is boolean: which facts hold, under which conditions.
So how that reasoning is represented in the e-graph matters disproportionately.

First, VMIR keeps only a single boolean connective, the ternary operator, which
concisely represents $or$, $and$, $not$, and $=>$ under one canonical
representation: Helium no longer needs to know, for example, that
$p => q equiv not p or q$.

Second, when picking which rewrite rules to include, we favoured ones that add
no new e-nodes. A rule like $x ? x : "false" -> x$ or $"true" ? x : y -> x$ only
uses nodes its left-hand side already binds, so applying it merely unions
existing e-classes. This ruled out distributivity, associativity, and
commutativity: a rule such as $(x ? y : z) > w -> (x ? y > w : z > w)$ would be
useful, but its right-hand side names a term the left-hand side does not already
contain, and applying it repeatedly blows up the e-graph exponentially in the
depth of the ternary tower. The cost is completeness -- Helium is often unable
to prove obligations that look trivial to the human eye.

For the complete list of rewrite rules included in Helium, please refer to
@sec:appendix-rewrites.

#para[Comparison with Silicon] Silicon shows what the alternative costs. It
also verifies by symbolic execution, but beyond a handful truly trivial
cases, every obligation is discharged to Z3, a round trip to an external
process. This is exactly the cost the tiers above are built to avoid: Helium
checks the goal against its own e-graph first, and only reports an
obligation unproven once none of them close it, never handing it to a
solver at all (at least for now).

Avoiding the round trip is not the whole story: the two also differ in how
they carry assumptions forward as verification goes deeper. Silicon builds
up its assumptions continuously: a nested guard is one more push on top of
the stack already there, not a rebuild from scratch. Helium fits its own
tooling instead: egg has no scoped push and pop, so cloning the whole graph
and assuming in the clone is the natural operation to reach for. A further,
nested guard means cloning again from the same base, not building on the
first clone, which is why cloning, at the #vm[`implication_decompose`]
tier, is reserved for the one case that actually needs it, rather than how
every path condition is handled.

The cost does not disappear, it moves. If two obligations need the same
case split, each still starts from a fresh clone: nothing carries what an
earlier clone derived into the next one. Silicon pays for a push once and
builds on it; Helium pays again each time an obligation needs the same
ground revisited. In practice this is a narrow cost: obligations nested
deep enough for it to matter are rare.

#pagebreak()

