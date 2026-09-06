#import "../../macros.typ": *

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
