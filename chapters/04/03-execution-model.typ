#import "../../macros.typ": *

== Execution Model <sec:impl-execution>

The execution model of the new verifier is strongly based off of the symbolic
execution model of Silicon. The main difference is that in this new verifier, it
is us who is responsible for managing the symbolic state, rather than Z3. On one
hand this means that there is a lot more bookkeeping we have to do, but on the
other hand, it means we have a lot more control over the symbolic state, giving us
the opportunity to optimize the process for the common case.

What that state is, and what executing an instruction does to it, is best seen on
a fragment small enough to walk end to end. @lst:exec-source is heapless, four
statements long, and carries one obligation.

#viper(
  caption: [The fragment this section walks: an equality assumed, and an equality over it asserted.],
  label: "lst:exec-source",
)[```viper
var a: Int
var b: Int
assume a == b
assert a * 2 == b * 2
```]

The obligation is an equality between two terms the program built, following from
an equality it was given. @lst:exec-vmir is what the verifier is given. Each
declaration becomes a value
about which nothing is assumed, and each comparison an instruction of its own, so
that what the #vi[`assume`] and the #vi[`assert`] name is a temporary rather than
an expression.

#vmir(
  caption: [Viper @lst:exec-source lowered. Original variable names in the comments.],
  label: "lst:exec-vmir",
)[```vmir
e0: Int := fresh // a
e1: Int := fresh // b
e2: Bool := e0 == e1
assume e2
e3: Int := e0 * 2
e4: Int := e1 * 2
e5: Bool := e3 == e4
assert e5
```]

The verifier executes this line by line, updating the symbolic state at each step,
and when it reaches the assertion it checks whether the obligation is satisfied.

#para[Symbolic state] There is no separate store of what the verifier knows. The
e-graph _is_ the symbolic state, and a VMIR temporary is nothing more than a
handle into it: executing an instruction builds the term it names and yields the
e-class that term landed in. The walk is forward and single-pass — instructions
are executed in order and none is revisited — so the state at any point is the
graph as it then stands, and everything learned up to that point is in it.

Each kind of instruction in @lst:exec-vmir does one thing to that graph, and the
four kinds it uses are most of the language.

A #vm[`fresh`] inserts a new e-node into a new e-class. Nothing is said about it
and nothing is equal to it, and the temporary being defined becomes the handle on
that class — so after the first two lines, #vm[`e0`] and #vm[`e1`] name two
distinct classes about which the verifier knows nothing at all.

An operation resolves the classes its operands name, and inserts a node over
them. #vm[`e2`] is an #vm[`==`] node whose two children are the classes of
#vm[`e0`] and #vm[`e1`], and #vm[`e2`] becomes the handle on the class that node
landed in. Insertion is hash-consed: a node with the same operator over the same
child classes is not a second node but the one already there, so building a term
twice costs a lookup and yields the same class.

An #vm[`assume`] is a union. #vm[`assume e2`] merges the class of #vm[`e2`] with
the class of #vm[`true`], and that is the whole of how a fact enters the state.
One rewrite then fires on what it produced: an #vm[`==`] node whose class is known
#vm[`true`] unions its two arguments, so #vm[`e0`] and #vm[`e1`] become one class.

Lines five and six are operations again, and the merge is what they run into.
Inserting #vm[`e1 * 2`] means inserting a #vm[`*`] node over the class of
#vm[`e1`] and the class of #vm[`2`] — but that is the node line five already
built, since #vm[`e0`] and #vm[`e1`] are by now the same class, so the insertion
finds it and #vm[`e4`] is a handle on #vm[`e3`]'s class. Had the two been built
_before_ the assume instead, they would have been merged by it: congruence closure
propagates a union to every application over the classes it merged, without either
application being revisited. Which order the program happens to use is therefore
not something the verifier has to care about.

#vm[`e5`] is then an #vm[`==`] node whose two children are one class, and the
assertion on the last line is the question of whether #vm[`e5`]'s class is the
class of #vm[`true`]. Here it is, because an equality between a class and itself
folds to #vm[`true`] on insertion. What the verifier does when the answer is not
immediate is @sec:impl-proving.

#para[Well-definedness] Building a term is not always free of obligations. Some
operations are partial, and an instruction applying one raises a side condition
saying that it was applied where it denotes something. Division is the case in
this fragment: #vi[`x / d`] means nothing where #vi[`d`] is zero, so
#vm[`e2: Int := e0 / e1`] raises #vm[`e1 != 0`] as an obligation, at the point the
term is built and whatever the surrounding expression goes on to do with the
result.

#para[Path conditions] The obligation is not always raised flatly, and a division
is the smallest thing that shows why. A program guards one by writing the check
into the expression, as in #vi[`var y: Int := d != 0 ? x / d : 0`] — the divisor
is only ever divided by where the guard says it is safe, and a verifier that
ignored that would reject a correct program.

The lowering is what carries the guard to the division. An instruction may hold a
_path condition_, written in angle brackets before it: a _cube_, meaning a
conjunction of boolean values already in the graph, each taken with a polarity. It
is attached at lowering time and is exact, so the verifier reads off what is in
force rather than working it out.

#vmir(
  caption: [A guarded division. The obligation the division raises is carried under the guard the program wrote.],
  label: "lst:exec-guard",
)[```vmir
e0: Int := fresh // x
e1: Int := fresh // d
e2: Bool := e1 != 0
e3: Int := <e2> e0 / e1
e4: Int := e2 ? e3 : 0 // y
```]

The #vm[`<e2>`] on line four is the path condition, and it is one literal: the
class of #vm[`e2`], taken positively. Without it the division would raise
#vm[`e1 != 0`] outright, which is not provable here and would reject the program
for a division it never performs.

The translator maintains that cube as a stack of literals while it walks. Lowering
the then-arm of a ternary pushes the condition positively and lowering the else-arm
pushes it negatively, each around the lowering of that arm and popped after it, so
the stack always holds exactly the literals in force and an instruction takes its
cube by snapshotting it.

Not every instruction takes one. An instruction that only builds a term needs no
cube, since a term is the same term wherever it was built: the arithmetic, the
comparisons and the ternary itself are emitted flat however deeply nested in
conditions they stand, and one temporary stands for the term across all of them.
An instruction with an obligation is the case that needs the cube, and in the
heapless pure fragment that is division and modulo alone. Heap instructions and
calls fall on the same line and are taken up where those constructs are
(@sec:impl-heap-interaction, @sec:impl-functions).

What the cube then does is weaken the obligation. One raised under a cube need
only hold where the cube does, so what has to be proven is not the goal but the
implication $"pc" => "goal"$ — here $e_2 => e_1 != 0$, whose consequent is the
literal the cube already contains.

#para[One state, not two] Carrying the condition on the instruction is what lets
the verifier keep a single graph where a forking symbolic execution keeps one
state per path. Silicon takes that other route, its #vi[`branch`] rule taking one
continuation per outcome:

#quote(block: true, attribution: [@silicon[Section 3.2]])[
  #vi[`branch`] enables splitting the symbolic execution into two paths: one path
  ($Q_v$) is taken under the assumption that $v$ is true, the second path
  ($Q_(not v)$) is taken under the assumption that $v$ is false.
]

Forking gives each path a state of its own. A fact obtained on one path is simply
not present on the other, and every fact a path does hold is unconditional:
nothing proven there has to mention the condition the path was taken under. Two
paths that share nothing can moreover be explored on two verifiers at once, which
Silicon can be asked to do.

A single graph gives sharing instead. Every term built before the condition serves
both readings of it, and nothing is copied when the condition arises. The price is
that a fact holding on one side only cannot be stated outright, and that an
obligation raised under a cube is an implication rather than a goal.

Which of the two pays depends on the obligations. This design bets, on the
evidence of @sec:prusti-needs, that most of them follow from the structure the
program has already built, and so are discharged without the cube being assumed at
all. What becomes of the ones that are not is @sec:impl-proving.
