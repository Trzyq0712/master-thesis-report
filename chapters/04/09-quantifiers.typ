#import "../../macros.typ": *

== Quantifiers <sec:impl-quantifiers>

Quantification appears in this fragment in exactly one place: a triggered
#vi[`forall`] inside a domain axiom, relating a domain's uninterpreted functions
to each other. @lst:example-viper's #vi[`bool`] is the whole of the shape — a
round-trip law between a constructor and its accessor, stated in both directions —
and #vi[`i32`] adds one more axiom of the same form bounding the integer's
range. Every quantifier a Prusti encoding raises is of this shape: it carries a
written trigger, and there are no quantified permissions and no #vi[`exists`]
at all. The verifier's obligation is therefore narrower than Viper's grammar
suggests: instantiate pure, triggered, universally quantified facts.

A trigger is a pattern the author writes, and it is never
inferred. A #vi[`forall`] arriving without one that covers its binders is
rejected as a type error rather than being given a guess, on the grounds that a
quantifier silently instantiated on a pattern nobody wrote is a performance cliff
whose cause is invisible from the source.

A quantifier may carry several trigger groups, and they are alternatives: a match
of any one instantiates. A group may name several terms, and those are conjunctive
— every term of the group must match, under one consistent binding, before the
group fires.

What is unusual is where a quantifier lives. It is not a rule.
A #vi[`forall`] is an ordinary value in the instruction stream — an e-node whose
payload names its compiled body and whose children are the e-classes of the
enclosing values the body mentions. Capture is thereby implicit: the body shares
the enclosing temporary space, so a free occurrence of an outer value is just that
value, and nesting needs no extra mechanism at all, since an inner quantifier's
binders are numbered above the outer's and the same rule separates them.

Making a quantifier data rather than a rule is what allows a single instantiation
rule to serve the entire program. That rule scans the e-classes holding a
#vm[`forall`] node — one bucket of the operator index, so the scan is proportional
to the quantifiers actually present rather than to the ones the program contains
— and for each, matches its trigger groups against the graph.

Matching is e-matching in the ordinary sense: a pattern's head function selects a
bucket of candidate classes, the pattern is matched against the nodes of each, and
the bindings are extended term by term across the group. Two properties of the
e-graph are doing work here. Matching is up to congruence, so a trigger fires
against any term equal to the pattern rather than only against the one that was
written; and it is _not_ up to reductive normal form, so a trigger must not be
expected to fire because the graph could be normalised into the right shape. The
second is a contract with the rest of the design: a rewrite that happens to
canonicalise terms is not permitted to be load-bearing for a trigger.

An instance is the body rebuilt at the captures and the
matched binding: the compiled body's steps are re-run with the binders bound to
the matched classes, add-only and importing no e-class from anywhere. The same
mechanism installs a function's body at an occurrence of the function, and it is
described in full there (@sec:impl-functions); a quantifier body and a function
body are compiled to the same thing.

What is then asserted is not the instance but a guarded form of it: the instance
is released only once the quantifier's own class is known #vm[`true`]. That is
what makes instantiating sound regardless of whether the quantifier has been
established. A #vi[`forall`] appearing in a position that is merely _assumed_ on
some path, or one being checked rather than used, can be matched and instantiated
freely; nothing it says enters the state until the quantifier itself does. The
guard is an ordinary conditional, so when the quantifier _is_ true it collapses by
the same reduction that simplifies any other, and the instance costs nothing to
release.

Because a quantifier is a value, an instantiation can materialise a new
quantifier: an outer instance builds its inner #vi[`forall`] with the outer
binding baked into the children. The instantiation rule then picks that node up on
the next saturation iteration, since it is data the rule scans rather than a rule
that would have to be injected mid-run.

Left alone, the loop of match–instantiate–match is where a solver
diverges, and the verifier's defences are structural rather than budgeted.

Instances are memoised by the quantifier and the binding that produced them, so a
pattern matching again on a later iteration costs a lookup. Deduplication happens
one level up as well: two syntactically identical quantifiers at two program
points are compiled to one recipe, keyed by the canonicalised body _and_ its
triggers — alpha-equivalence and program-point independence come free from the
canonicalisation, and keying on the triggers as well as the body is deliberate, so
that two quantifiers stating the same proposition with different patterns are
never pooled into one.

Well-definedness is checked once, where the quantifier is encountered, and never
inside the rule. The check runs in a throwaway copy of the live state with the
binders replaced by fresh values, so the body's side conditions — a division by a
bound variable, say — are discharged for an arbitrary binding, with every ambient
fact available and no possibility of the fresh values polluting the real state. Body-local path conditions come along, so a guard proves its own
consequent's well-definedness. The point of doing it here is that instantiation
happens inside a rewrite rule, where nothing can be proven at all: by the time a
recipe is replayed, every obligation it might have carried has already been
discharged.

A quantifier that never triggers is not an error and not a
loss. Its node is in the state with its captures resolved and its body compiled,
which is a complete description of the fact it stands for; what is missing is only
that no term the program built matched its pattern. An obligation that would have
needed it fails as an ordinary unproven goal, and the quantifier is still there,
in the same state, for a procedure that instantiates differently.
