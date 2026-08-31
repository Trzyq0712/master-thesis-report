# Plan — §5.2 Feature Completeness

Not part of the thesis. Delete when §5.2 is finished.

## Scope

The section is scoped to the Viper tutorial (`viper.ethz.ch/tutorial`), not to
an exhaustive enumeration of Silver's abstract syntax, and within the tutorial
to five areas: the built-in containers, `decreases`, inhale-exhale expressions,
magic wands and quantified permissions. The tutorial is what a
Viper user is taught the language is, so a construct it presents is one a reader
will expect an answer about, and a construct it does not present needs no
defence.

Within that scope, the reference for a construct's *meaning* is Silver, not
Helium's parser. Two rules follow, and both were paid for already:

1. **Silicon's verdict gates every probe.** A probe Silicon rejects is a bad
   probe, not a Helium gap. Two of my own probes failed this test today: an
   `unfolding` postcondition that was not well-defined, and a domain carrying an
   `interpretation` clause that Silicon also rejects.
2. **Frequency is counted with Silver's parser, never with grep.** A trial
   regex count over Silver's corpus reported zero magic wands.

## The pin was wrong, and every §5.2 claim depended on it

`helium-eval` pinned `vendor/silver-oxide` at `8e31c8c`. The commit that reports
unsupported constructs per declaration, `b43026e`, is the very next one on
`backend-blocks`. Everything recorded about how Helium names a refusal was
therefore describing a build the harness was not running.

The pin is now at `b43026e` and Helium is rebuilt. The difference is not
cosmetic — it is §5.2.1's entire claim:

| probe | at `8e31c8c` | at `b43026e` |
|---|---|---|
| `Seq`, `Set`, `Map`, `Multiset` | whole-file parse error | `[UNSUPPORTED] m: unsupported construct: Seq` |
| magic wand, `package` | `typecheck: WrongReturnCount { expected: 1, found: 0 }` | `[UNSUPPORTED] m: unsupported construct: package` |
| quantified permission | `unsupported pure expression: Acc(AccExp { loc: … })` | `[UNSUPPORTED] m: unsupported construct: quantified permission` |
| inhale-exhale `[A, B]` | **verified** | `[UNSUPPORTED] m: unsupported construct: inhale-exhale expression [A, B]` |

Every number in the 30 August sweep is at the old pin and has to be re-taken.

## The five areas, with Helium's measured behaviour

Each row is a probe already run at `b43026e`. Silicon's column is confirmed
where marked, and is the next thing to fill in where it is not.

### 1. Built-in containers

`Seq[T]`, `Set[T]`, `Multiset[T]`, `Map[T,V]` are the tutorial's built-in
collection types, alongside `Int`, `Bool`, `Perm`, `Ref` and the deprecated
`Rational`. Helium implements none of the four.

The type, the literal and the constructor are each reported by name. One gap
remains: the multiset cardinality operator `#` is not in the grammar, so
`(s # 1)` is a whole-file parse error while `Multiset(1, 1)` is a named
refusal. Probe both, and report the split rather than rounding it away.

Needed: one probe per type covering the literal, the constructor and the
operators the tutorial gives — for sequences that is `Seq[T]()`, `Seq(x)`,
`|s|`, `s[i]`, `s[i..]`, `s[..i]` and `s ++ t`, and the corresponding sets for
the other three.

### 2. `decreases`

Accepted and dropped. Helium runs no termination check anywhere, so
`function bad(n: Int): Int decreases n { bad(n) + 1 }` is admitted. `decreases *`
is likewise dropped.

Silicon **rejects** the same function: *"Function might not terminate.
Termination measure might not decrease."* So this is not a construct Helium
refuses, and not one it merely ignores — dropping the clause silently skips a
check Silicon performs. It belongs in the table as a missing check, named as
one, and it is the one place in §5.2.1 where the difference is invisible in the
output.

Reassuring, and worth one sentence: admitting a non-terminating function does
not collapse the proof state. `assert false` after `bad` is still rejected.

### 3. Inhale-exhale expressions `[A, B]`

Now `[UNSUPPORTED]`, naming the construct. At the old pin it **verified**, and
what it verified was unsound: `[true, acc(x.f)]` was folded into a conjunction,
handing a body a permission Viper never granted.

This is the strongest evidence §5.2.1 has for its own claim, so it should be
written up as the worked example: the same program, the same verifier, one
change to the reporting, and a wrong answer becomes a refusal to answer. It is
**not** written up as an unsoundness in Helium's terms — inhale-exhale is out of
scope, and the defect was the missing rejection.

### 4. Magic wands

`--*`, `package`, `apply`, `applying` and `lhs`. Reported by name at the new
pin. Confirm each of the five separately: `--*` is in the grammar (it appears in
the parser's expected-token set) while `package` is caught later, so they may
not all take the same path.

### 5. Quantified permissions

`[UNSUPPORTED] … quantified permission`, which is the right message. One caveat
to report honestly: the tutorial's own idiom writes the receiver set as
`forall x: Ref :: x in xs ==> acc(x.f)`, and on that program Helium names `Set`
rather than the quantified permission, because the container is reached first. A
reader who writes the tutorial's version is told the wrong thing about their
program. Probe both shapes.

The tutorial's *Receiver Expressions and Injectivity* section belongs here too —
it is the part of quantified permissions that most affects what a frontend can
encode.

### Out of scope

Two constructs from the tutorial's *Annotations* chapter are out of scope, and
the section neither probes nor mentions them: backend `interpretation` clauses,
which map a Viper symbol onto an SMT-LIB one, and `@opaque()`. Direct SMT
interaction is not something Helium sets out to support, and annotations are
not what Prusti's encoder relies on.

Recorded here so the decision is not rediscovered: `@opaque()` is accepted and
ignored, so Helium verifies `assert f(1) == 2` for an opaque `f` where Silicon
rejects it. By the same reasoning applied to inhale-exhale, the defect is a
missing rejection in a construct that is out of scope, not an unsoundness in
Helium's terms.

## What §5.2.1 says

Three classes, and every construct in the tutorial lands in exactly one:

1. **Supported.**
2. **Refused by design**, which splits into constructs absent from Prusti's
   output per chapter 3, and deliberate semantic divergences. Well-founded
   resource declarations are the divergence in hand: Helium requires the
   predicate and function dependency graph to be acyclic and Viper does not.
   Silicon verifies both probes in `suites/viper/divergence/`, and the cost over
   Silver's own 1430-file test suite is three files, none of which models
   anything — one is a predicate its authors named `strange`, two are regression
   tests against Silicon issue numbers.
3. **Accepted with a changed meaning**, which within the scope above is
   `decreases` alone: it is dropped, so no termination check runs where Silicon
   rejects the function. This class is the one a reader should care most about,
   and it must not be folded into the other two.

Orthogonally, how a refusal reads: it names the construct, or it is a whole-file
parse error. At the new pin, and with backend interpretations out of scope, the
second is down to the multiset `#` operator alone, which should be stated rather
than rounded away.

## What §5.2.2 says

Verification incompletenesses, grouped by cause, with a minimal reproducing
program each: the arithmetic gap, the datatype inverses, and the variant-count
limit measured in §5.3.

Two things still missing: `suites/viper/fail/` is empty, so the differential
suite has no rejection side; and the corpus can give an incompleteness figure
with no cherry-picking, because Silver's test files carry `//:: ExpectedOutput`
annotations. Of the files Helium translates in full, how many does it decide the
way the annotation says? That separates a correctly rejected negative test from
a wrongly rejected good program, which the raw failing-declaration share of the
E8 run does not.

## Order of work

1. Re-run E8 at `b43026e` — the corpus classification is at the old pin.
2. Rewrite the probe set around the six areas, Silicon first, one probe per
   construct the tutorial names.
3. Populate `suites/viper/fail/`.
4. Run E1 and E3 clean; extend E8 with the `ExpectedOutput` comparison.
5. Generate the table, write §5.2.1 and §5.2.2.
