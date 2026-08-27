#import "../macros.typ": *

#note[
  *How this chapter is organised.* This chapter is design; the next is
  mechanism. It opens with the program the rest of the thesis refers back to,
  generalises it into a measurement of what the target language actually
  contains, and only then states principles — so that they read as derived from
  evidence rather than declared, and the non-goals read as scoping rather than
  apology.
]

== A Guiding Example <sec:example>

Everything the next two chapters do refers back to one place: a Viper program
Prusti actually emitted. This section presents that program. Nothing in
it is a simplification, and every construct it contains is given a lowering in
@sec:implementation.

The Rust is unannotated. There is no precondition, no
postcondition, and nothing a user wrote to help a verifier along;#footnote[The
file as it is fed to Prusti carries #ru[`use prusti_contracts::*`] and one
#ru[`body_invariant!(true)`] per loop body, because Prusti refuses a loop without
an invariant. Both are elided from every listing in this thesis. #ru[`true`]
claims nothing, so no obligation below depends on them — what they cost is six
members of the encoding, a closure datatype and its predicate per
loop.] every obligation in what follows comes from
Prusti's encoding of Rust's own guarantees.

#rust(caption: [The Rust the user wrote. Four of the eight functions; the four
  elided branch and assign like #ru[`account_deposit`].], label: "lst:example-rust")[```rust
pub struct Account {
    pub balance: i32,
    pub limit: i32,
}

pub enum Transaction {
    Deposit(i32),
    Withdrawal(i32),
}

pub enum AccountList {
    Empty,
    Cons(Account, Box<AccountList>),
}

pub fn account_deposit(a: &mut Account, amount: i32) {
    if 0 < amount {
        a.balance = a.balance + amount;
    }
}

pub fn account_apply(a: &mut Account, t: &Transaction) {
    match t {
        Transaction::Deposit(amount) => {
            a.balance = a.balance + *amount;
        }
        Transaction::Withdrawal(amount) => {
            a.balance = a.balance - *amount;
        }
    }
}

pub fn sum_up_to(n: i32) -> i32 {
    let mut i = 0;
    let mut total = 0;
    while i < n {
        total = total + i;
        i = i + 1;
    }
    total
}

pub fn sum_balances(list: &AccountList) -> i32 {
    let mut total = 0;
    let mut cur = list;
    while let AccountList::Cons(a, rest) = cur {
        total = total + a.balance;
        cur = rest;
    }
    total
}
```]

Eight functions over one struct and two enums, and each of the four above is
there for a construct it forces the encoder to emit.

#ru[`account_deposit`] takes a #ru[`&mut`] and writes through it under a
condition. That is the shape @sec:impl-cfg and @sec:impl-calls are about: the
write to #ru[`a.balance`] happens on one path and not the other, so the permission
to it is taken apart on one branch and has to be reconciled with the branch that
left it alone before the function returns. A #ru[`&mut`] parameter produces that
shape almost every time.

#ru[`account_apply`] adds a #ru[`match`] on a shared borrow of an enum. An enum's
predicate does not have a fixed footprint the way a struct's does: Prusti puts
each variant's payload under that variant's discriminant, so what the caller holds
is conditional, and reading the payload means establishing which variant it is
first. That drives @sec:impl-adts's discriminator rules and the gate split of
@sec:impl-predicates, and no struct-only program shows it.

#ru[`sum_up_to`] and #ru[`sum_balances`] are the two loops, and they are two
different loops. The first is driven by a counter and its obligations are
arithmetic; the second is driven by a discriminator test on a recursive datatype
and its obligations are structural — the list is walked by unfolding, and
#ru[`Box`] puts a generic type parameter between the node and its tail.
Both matter, because the mechanism is the same for the two and only
one of them survives the arithmetic of the tiered prover.

The three functions not shown — #ru[`account_over_limit`], #ru[`account_classify`]
and #ru[`account_adjust`] — read a field, nest two conditionals, and assign twice
under separate guards. They add volume rather than shapes.

Prusti's output for this crate is 3371 lines of Viper
declaring 151 members. Almost all of it is machinery repeated per type: the same
half-dozen shapes instantiated at #ru[`i32`], at #ru[`bool`], at #ru[`isize`], at
the unit and two-element tuples, at #ru[`&Account`] and #ru[`&mut Account`], at
#ru[`Box`], and at the struct and the two enums themselves. Abridged to one
instance of each shape, it reads:#footnote[Prusti's generated identifiers are
mangled — #vi[`s_Int_i32`] for the #ru[`i32`] snapshot type, #vi[`p_Account`] for
the #ru[`Account`] predicate, #vi[`mir_binop_Lt_Int_i32_Int_i32`] for a
comparison. Every listing in this thesis shortens them uniformly and injectively:
the snapshot type keeps the Rust name (#vi[`i32`], #vi[`Account`]), the predicate
gets an #vi[`own_`] prefix (#vi[`own_i32`], #vi[`own_Account`]), the
heap-dependent snapshot function and the assignment method get #vi[`snap_`] and
#vi[`assign_`], and the arithmetic becomes #vi[`lt_i32_i32`]. Nothing else is
changed.]

#viper(caption: [Prusti's encoding, abridged to one instance of each shape it repeats.], label: "lst:example-viper")[```viper
domain bool {
  function bool_cons(arg0: Bool): bool
  function bool_value(arg0: bool): Bool

  axiom bool_ax_cons {
    (forall s: bool :: { bool_value(s) }
      bool_cons(bool_value(s)) == s)
  }
  axiom bool_ax_value {
    (forall value: Bool :: { bool_cons(value) }
      bool_value(bool_cons(value)) == value)
  }
}

domain Param { }

adt Account {
  Account_cons(Account_0: i32,
                 Account_1: i32)
}

adt Transaction {
  Transaction_0_cons(Transaction_0_0: i32)
  Transaction_1_cons(Transaction_1_0: i32)
}

field val_i32: i32

function Account_field_1(self: Ref): Ref
  ensures (self == null) == (result == null)

function Transaction_discr(self: Transaction): isize
{
  (self.isTransaction_1_cons ? isize_cons(1)
                               : isize_cons(0))
}

function generic_Account(self: Account): Param
  ensures Param_typeof(result) == Account_type()
  ensures concrete_Account(result) == self

function concrete_Account(snap: Param): Account
  ensures generic_Account(result) == snap

predicate own_i32(self: Ref) { acc(self.val_i32, write) }

predicate own_Account(self: Ref) {
  acc(own_i32(Account_field_0(self)), write) &&
  acc(own_i32(Account_field_1(self)), write)
}

predicate own_Transaction_0(self: Ref) {
  acc(own_i32(Transaction_0_field_0(self)), write)
}

predicate own_Transaction(self: Ref) {
  acc(own_isize(Transaction_field_discr(self)), write) &&
  ((snap_isize(Transaction_field_discr(self)) == isize_cons(0) ||
    snap_isize(Transaction_field_discr(self)) == isize_cons(1)) &&
   ((snap_isize(Transaction_field_discr(self)) == isize_cons(0) ==>
     acc(own_Transaction_0(self), write)) &&
    (snap_isize(Transaction_field_discr(self)) == isize_cons(1) ==>
     acc(own_Transaction_1(self), write))))
}

predicate own_Param(self: Ref, T$0: Type)

function snap_Account(self: Ref): Account
  requires acc(own_Account(self), write)
{
  (unfolding acc(own_Account(self), write) in
    Account_cons(snap_i32(Account_field_0(self)),
                   snap_i32(Account_field_1(self))))
}

method assign_Account(self: Ref, value: Account)
  ensures acc(own_Account(self), write)
  ensures snap_Account(self) == value
```]

Thirteen declarations, and between them they exercise most of the language.

#vi[`bool`] is a domain: uninterpreted functions plus triggered axioms
(@sec:impl-domains, @sec:impl-quantifiers). It is the pattern every Rust scalar
gets, and the reason to show this one rather than #vi[`i32`] is that the two
differ by a single axiom bounding the integer's range. #vi[`Param`] is the
degenerate case: a domain declaring nothing at all, whose only role is to be a
type that values of an unknown Rust type can be given — which is what
#ru[`Box<AccountList>`] needs, since #ru[`Box`]'s payload is generic.

#vi[`Account`] is an #vi[`adt`] with one constructor and one field per Rust
field, and it is the type a folded #vi[`own_Account`] remembers.
#vi[`Transaction`] is the enum case: one constructor per variant, so a value of
it is a datatype term whose head is not known until something establishes it, and
#vi[`Transaction_discr`] is how that is asked. Its body is a ternary over
Viper's #vi[`.isC`] test, and @sec:impl-adts encodes both by one integer-valued
discriminator rather than by a predicate per variant.

#vi[`val_i32`] is the one field declaration a Prusti program needs per
primitive type; every heap location in the encoding bottoms out at one of these
(@sec:impl-heap-interaction), and #vi[`Account_field_1`] is how a struct's second field is
addressed — an uninterpreted function from the struct's reference to the field's,
with a postcondition relating the two only at #vi[`null`].

#vi[`own_i32`] and #vi[`own_Account`] are predicates, the second nesting two
instances of the first, which is how Prusti encodes a struct's ownership
(@sec:impl-predicates). #vi[`own_Transaction`] is the same idea with a conditional
footprint: it holds the discriminant outright, constrains it to the two variant
indices, and then holds one variant's payload predicate _under an implication_ on
which index it is. What a holder of #vi[`own_Transaction`] can unfold to therefore
depends on a value in the heap, and @sec:impl-predicates is where a footprint gets
to be conditional at all. #vi[`own_Param`] is the one predicate declared _without_ a
body: a value of a generic type parameter, whose representation is not known where
the encoding was generated.

#vi[`snap_Account`] is a heap-dependent function: it demands permission in its
precondition and its body opens the predicate with an #vi[`unfolding`] to read
what is inside. It connects the two sides — permission on one,
a pure snapshot value on the other — and the verifier does that
without re-proving the function at every occurrence. Its enum sibling
#vi[`snap_Transaction`] is the same shape with the conditional footprint showing
through: a ternary on the discriminant with one #vi[`unfolding`] per arm, falling
through to #vi[`Transaction_unreachable()`].
#vi[`generic_Account`] and #vi[`concrete_Account`] are the opposite
shape: no body at all, and postconditions stating that the two are inverse. Their
entire content is a contract, and what they ask for is equality reasoning.

#vi[`assign_Account`] is a method: no body, a two-clause postcondition, and
every call to it is a permission transaction rather than a jump (@sec:impl-calls).
Prusti routes every assignment to a place of struct type through one of these.

The bodies are where the rest of the volume is. They are
basic-block graphs, and @lst:example-body is #vi[`bb_2`] of
#vi[`account_deposit`] — the block that runs when the condition held, so the
write goes through.

#viper(caption: [#vi[`bb_2`] of #vi[`account_deposit`], unabridged, with Prusti's
  per-statement #vi[`label`]s and MIR comments removed.], label: "lst:example-body")[```viper
label bb_2
if (_from_bb0_to_bb1) {
  make_concrete_Account(snap_RefMut(_1p,
    Account_type()).RefMut_0)
}
if (_from_bb0_to_bb1) {
  unfold acc(own_Account(snap_RefMut(_1p,
    Account_type()).RefMut_0), write)
}
exhale acc(own_i32(Account_field_0(snap_RefMut(_1p,
  Account_type()).RefMut_0)), write)
_tmp3 := snap_i32(Pair_field_0(_7p,
  i32_type(), bool_type()))
exhale acc(own_i32(Pair_field_0(_7p,
  i32_type(), bool_type())), write)
assign_i32(Account_field_0(snap_RefMut(_1p,
  Account_type()).RefMut_0), _tmp3)
if (_from_bb0_to_bb1) {
  fold acc(own_Account(snap_RefMut(_1p,
    Account_type()).RefMut_0), write)
}
if (_from_bb0_to_bb1) {
  make_generic_Account(snap_RefMut(_1p,
    Account_type()).RefMut_0)
}
assign_Unit(_0p, Unit_cons())
_from_bb2_to_bb4 := true
goto bb_4
```]

Four features of that block set the shape of @sec:impl-cfg. Control flow is
#vi[`goto`] between labelled blocks, and Prusti emits #vi[`if`] statements of
exactly two kinds: the one shown here, guarding a run of statements by a
conjunction of _reach flags_ — #vi[`_from_bb0_to_bb1`], an ordinary boolean
variable the encoder sets on each edge taken — and, at the end of a branching
block, one whose arms are nothing but a flag assignment and a #vi[`goto`]. The
block condition is therefore in the program's own data rather than in its
structure. The address written through,
#vi[`snap_RefMut(_1p, ..).RefMut_0`], is recovered from a snapshot
of the #ru[`&mut`] rather than named directly, so whether it is the location the
block already holds permission for is a question about terms. And the
#vi[`make_generic`] / #vi[`make_concrete`] pair brackets the unfold, which is how
Prusti moves a value in and out of the opaque #vi[`Param`] representation across
a call boundary.

A loop arrives at the Viper level as a labelled block with
#vi[`invariant`] clauses on it and a #vi[`goto`] reaching it from two places: the
block before the loop and the block at the end of the body. There is no
#vi[`while`] anywhere in the file. @lst:example-loop is the head of
#ru[`sum_up_to`]'s loop.

#viper(caption: [The loop head of #vi[`sum_up_to`]. The fourth invariant is the
  elided #ru[`body_invariant!`], abridged further — Prusti routes it through a
  closure snapshot and a chain of #vi[`let`]s that reduces to #vi[`true`].],
  label: "lst:example-loop")[```viper
label bb_3
  invariant acc(own_i32(_2p), write)
  invariant acc(own_i32(_1p), write)
  invariant acc(own_i32(_3p), write)
  invariant bool_value((let _0_23s_bb4_s3_i1 == (...) in
    (let _0_11s_bb4_s6_i2 == (bool_cons(bool_value(
      (let _1_0s_bb0_s0_i1 == (bool_cons(true)) in
        _1_0s_bb0_s0_i1)))) in _0_11s_bb4_s6_i2)))
assign_bool(_10p, bool_cons(false))
_tmp3 := snap_bool(_10p)
exhale acc(own_bool(_10p), write)
if (bool_value(_tmp3) == false) {
  _from_bb3_to_bb6 := true
  goto bb_6
} else {
  _from_bb3_to_bb4 := true
  goto bb_4
}
```]

Two things there matter to how a loop is verified. The invariant is three permission
clauses and one pure clause, so cutting the back edge is an exchange of
permission and not just a havoc of variables — what the invariant does not name
has to survive the loop, and what it does name is re-established at the head. And
the loop is a back edge rather than a syntactic construct: #vi[`bb_3`] is reached
from #vi[`bb_2_pre0`] before the loop and from #vi[`bb_9`] at the bottom of the
body, and the verifier finds the loop by dominance rather than by reading a
keyword.

Two families were cut from @lst:example-viper and add no
mechanism. The arithmetic family — #vi[`lt_i32_i32`], #vi[`le_i32_i32`],
#vi[`add_ovf_i32_i32`] and #vi[`sub_ovf_i32_i32`] — is four bodyless
functions with #vi[`ensures`] clauses, exactly the #vi[`generic_Account`] shape at
greater length. And each method body carries a #vi[`label`] before every
statement, which the encoder emits so that #vi[`old`] can name any intermediate
state; a label costs the verifier a named heap (@sec:impl-calls) and nothing else.

One thing survives into the encoding that the source listings do not show.
#ru[`body_invariant!`] is a macro, and Prusti compiles it through a closure —
hence the #vi[`Closure_sum_up_to`] datatype, its predicate, and the
#vi[`let`]-chain above. It contributes six members and no mechanism: the datatype
has one nullary constructor, the predicate's body is #vi[`true`], and the chain
reduces by the same projection rule any other snapshot does.

This program is not one of the 22 encodings measured in
@sec:prusti-needs. That corpus is loop-free by construction — Prusti's users
write loops, but a benchmark whose cost is dominated by an arithmetic invariant
measures the arithmetic and not the backend — and the example is here to be
_read_ rather than to be timed. What it shares with the corpus is every construct
in it; @sec:prusti-needs is the argument that the constructs generalise, and
@sec:results is where the cost is measured.

The commitment, then. By the end of @sec:implementation every construct in
@lst:example-viper, @lst:example-body and @lst:example-loop has a lowering, an
execution rule, and a section that owns it.

== What Prusti Demands of a Verifier <sec:prusti-needs>

One program is an anecdote. This section is the measurement it generalises to,
and it is the evidence base for every scoping decision after it: which constructs
a Prusti backend has to execute, which it never sees, and in what proportion the
ones it does see arrive.

Twenty-two Prusti encodings, committed under
#raw("benchmarks/rust/vpr/") in the implementation's tree: 216,833 lines of Viper,
2886 verifying members. Ten are encodings of hand-written Rust — vector and matrix
arithmetic, a bank transfer, a state machine, an inventory, a physics step, a
tuple classifier, a shape-area calculator over payload enums. The remaining twelve
are the #raw("depth_dD_mM") family, generated with two knobs so that
control-flow-nesting depth and block length can be varied independently;
@sec:results uses that separation and this section does not.

Every source obeys one rule: no #ru[`prusti_contracts`]. There is not a single
hand-written specification anywhere in the corpus. The obligations are the ones
Prusti's own type encoding generates — framing, fold and unfold, discriminant
well-formedness, and the accounting that moves permission in and out of a
#ru[`&mut`] — which is the set of obligations every Prusti user pays whether or
not they write specifications. That is precisely the class an equality-reasoning
core is aimed at, and it is what makes the non-goals below a scoping decision
rather than an admission of weakness.

The counts below are over the 22 files. Declarations are
counted per declaration and statements per occurrence.

#figure(
  caption: [What a Prusti encoding contains, over the 22-file corpus.],
  {
    set text(size: 0.9em)
    let hd(it) = text(size: 0.85em, weight: "bold")[#it]
    table(
      columns: (auto, auto, 1fr),
      stroke: (x, y) => (
        top: if y == 1 { 1pt + luma(40%) } else if y > 1 { 0.5pt + luma(85%) } else { none },
        rest: none,
      ),
      inset: (x: 0.5em, y: 0.4em),
      align: (left + top, right + top, left + top),
      table.header(hd[Construct], hd[Count], hd[Notes]),

      vi[`domain`], [126], [Uninterpreted functions and axioms; one per primitive
        Rust type, plus the type-tag and trait domains.],
      vi[`axiom`], [138], [All at the top level of a domain. 132 contain a
        #vi[`forall`], and every one of those carries a written trigger.],
      vi[`adt`], [161], [Snapshots. One constructor per struct, one per enum
        variant.],
      vi[`field`], [92], [One per primitive type, never per Rust field.],
      vi[`function`], [1264], [209 heap-dependent #vi[`_snap`] functions with
        bodies; the rest bodyless, carrying #vi[`ensures`] clauses alone.],
      vi[`predicate`], [232], [22 of them abstract — declared with no body at
        all.],
      vi[`method`], [623], [217 encode a Rust function and have bodies; the other
        406 are bodyless assignment and representation-change methods.],

      vi[`exhale`], [4947], [The most frequent statement, and so the hot path.],
      vi[`unfold`] + vi[`fold`], [3069 + 1620], [Second and third.],
      vi[`inhale`], [1511], [],
      vi[`unfolding`], [234], [In heap-dependent function bodies, and in 24 places
        at a #vi[`wildcard`] share.],
      vi[`acc(..)`], [11648], [11624 of them at #vi[`write`]#[;] the remaining 24 at
        #vi[`wildcard`]. No fractional literal appears anywhere.],
      vi[`goto`], [4427], [A flat block graph. The 4642 #vi[`if`] statements
        either wrap a pair of #vi[`goto`]s or guard a run of statements by reach
        flags.],
      vi[`label`], [24518], [One before every statement, so that #vi[`old`] can
        name any state.],
      vi[`old`], [256 + 104], [Unlabelled, and labelled #vi[`old[L]`] — the latter
        in 10 of the 22 files.],
      vi[`let .. in`], [128], [],
      vi[`assert`], [165], [Almost all of them #vi[`assert false`] in a block
        Prusti has proven unreachable.],
    )
  },
) <tbl:corpus>

The absences are as load-bearing as the counts, because
they are what license a verifier not to implement half of Viper. Across all
216,833 lines there is no #vi[`while`], no magic wand and no #vi[`applying`], no
quantified permission, no #vi[`perm`] and no #vi[`forperm`], no #vi[`exists`], no
#vi[`Seq`], #vi[`Set`], #vi[`Multiset`] or #vi[`Map`], no #vi[`new(*)`], no
#vi[`decreases`], no fractional permission literal, and no #vi[`assume`]
statement. Prusti's snapshots are #vi[`adt`]s rather than sequences, which is what
removes the collection types; its loop-free source rule is what removes
#vi[`while`]#[;] and its uniform #vi[`write`] discipline is what removes fractional
literals and #vi[`perm`].

Together those two lists name the target fragment. The verifier this
thesis builds has to execute a flat block graph over a heap partitioned into
predicates and primitive fields, held at #vi[`write`] or at a wildcard, moved by
#vi[`inhale`], #vi[`exhale`], #vi[`fold`] and #vi[`unfold`], read through
heap-dependent functions and bodyless contracts, over values that are datatype
snapshots and uninterpreted domain applications related by triggered universal
axioms. @sec:implementation is organised against exactly that sentence.

== Guiding Principles <sec:principles>

The corpus of @sec:prusti-needs is not a hard verification problem. It is a large
one. The obligations it raises are overwhelmingly bookkeeping — this read is
framed by permission the block already holds; this fold and the unfold before it
cancel; this value is the one the postcondition just named — and there are
millions of them. That observation is the whole design, and the four principles
below are what follows from it.

#para[Performance first] The goal is throughput on core proofs, and every other
decision is subordinate to it. Where a mechanism can be made structural — true by
how the state is represented rather than by a query — it is, even where that costs
generality. Where it cannot, the cost is paid on the obligations that need it and
not on the ones that do not; the prove ladder of @fig:prove-ladder is that
principle in its most literal form, a ladder of tiers ordered so that an
obligation costs what it takes to answer it.

#para[Only support the core] The fragment of @sec:prusti-needs is the whole
target. Constructs outside it are not approximated, not partially handled, and not
silently ignored: they are rejected by name, by the type-checker or the
translator. That is what makes the scoping a refusal to answer rather than a wrong
answer.

#para[Fewer concepts, uniformly treated] Viper distinguishes fields from
predicates, predicate bodies from method contracts from function preconditions,
and statements from expressions that read the heap. Each distinction costs a
verifier a separate rule, and each separate rule is a place for the two to
disagree. The design collapses them: fields and predicates are both _locations_
(@sec:impl-heap), predicate bodies and contracts are both _resources_
(@sec:impl-predicates), and a heap is a value like any other, so scoping an effect
is a matter of which temporary an instruction names (@sec:impl-calls). One rule
per concept, written once.

#para[Complete state, incomplete procedure] The decision procedure is deliberately
weak. The symbolic state is not. When an obligation cannot be discharged, nothing
is widened, dropped, or replaced by a symbol standing for what could not be
represented — the chunk is in its partition with its permission as a term, the
path condition is the exact cube, and the goal is an e-class in that same state.
A failed obligation is therefore a failure to prove and not a loss of information,
and it could be handed to a stronger procedure. @sec:implementation marks each
place this applies.

#para[Forced, and right anyway] Some of what follows is dictated by Prusti's
encoding and some would be right for any frontend, and Future Work depends on
telling them apart. Forced by the corpus: the scoping above, #vi[`write`]-only
permissions on the fast path, executing a #vi[`goto`] graph rather than a syntax
tree, and snapshots being first-class datatypes rather than an uninterpreted sort.
Right regardless of frontend: locations as types, so that fields and predicates
collapse into one concept; a heap partitioned by location kind; the e-graph as the
symbolic state rather than as a cache in front of a solver; exact rational
permissions; and VMIR being in static single assignment form at all. The second
group is what survives a different frontend.

== Non-Goals <sec:non-goals>

The verifier does not discharge functional specification proofs, and this is a
scoping decision justified by @sec:prusti-needs rather than a limitation being
admitted. The corpus contains no hand-written specification at all: what it asks
of a backend is framing, fold and unfold accounting, and discriminant
well-formedness, and those are obligations about the _structure_ a program has
already built rather than about what it computes.

Concretely, three shapes are out of scope to prove. An inequality between
symbolic arithmetic terms — the standard counting-loop invariant
$i < n tack.r i + 1 <= n$ is the canonical one — is not discharged, because the
core closes arithmetic _identities_ and identities do not decide an inequality. A
goal needing genuine reasoning by cases over a condition the goal itself does not
name is not discharged, because there is no case split. And a fact requiring a
disequality to be stored rather than derived is not discharged, because an e-graph
records equalities and has nowhere to put their negation.

Out of scope to _prove_ is not out of scope to _record_. Each of the three arrives
at the prover as an e-class in a state that is a faithful description of the
program point, and is reported as an unproven obligation naming exactly that
goal — never as a widened state, an approximation, or a silent pass. Falling back
to an SMT solver for such an obligation is left to Future Work; what this design
owes it is a handover point, and that is what the recording principle above
guarantees.
