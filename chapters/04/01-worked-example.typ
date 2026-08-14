#import "../../macros.typ": *

== A Worked Example <sec:impl-example>

Everything in this chapter is answerable in one place: a Viper program Prusti
actually emitted. This section puts that program on the table and states what the
rest of the chapter owes it. The program is small enough to read and complete
enough that nothing in it is a simplification — it is committed in the corpus of
@sec:prusti-needs, and @sec:impl-together returns to it verifying.

#para[The source program] The Rust is unannotated. There is no specification to
speak of and nothing a user wrote to help the verifier along; every obligation in
what follows comes from Prusti's encoding of Rust's own guarantees.

#rust(caption: [The Rust the user wrote. No specifications.], label: "lst:example-rust")[```rust
pub struct Account {
    pub id: i32,
    pub balance: i32,
    pub limit: i32,
}

pub fn account_deposit(a: &mut Account, amount: i32) {
    if 0 < amount {
        a.balance = a.balance + amount;
    }
}
```]

A struct with three fields and one method taking it by mutable reference. What
makes it worth following is that the assignment sits under a condition: the
permission to #ru[`a.balance`] is taken apart on one branch and not the other, and
the two states have to be reconciled before the function returns. That is the
shape @sec:impl-cfg is about, and it is the shape a `&mut` parameter produces
almost every time.

#para[The encoding] Prusti's output for this crate is 6347 lines of Viper. Almost
all of it is machinery repeated per type; the mechanisms are few. Abridged to the
declarations this chapter has to account for, it reads:

#viper(caption: [Prusti's encoding, abridged to the constructs the chapter covers.], label: "lst:example-viper")[```viper
domain s_Int_i32 {
  function s_Int_i32_cons(arg0: Int): s_Int_i32
  function s_Int_i32_value(arg0: s_Int_i32): Int
  axiom s_Int_i32_ax_cons {
    (forall s: s_Int_i32 :: { s_Int_i32_value(s) }
      s_Int_i32_cons(s_Int_i32_value(s)) == s)
  }
}

domain s_Param { }

field p_Int_i32_val: s_Int_i32

function s_Account_field_1(self: Ref): Ref
  ensures (self == null) == (result == null)

function make_generic_s_Account(self: s_Account): s_Param
  ensures s_Param_typeof(result) == s_Account_type()
  ensures make_concrete_s_Account(result) == self

function make_concrete_s_Account(snap: s_Param): s_Account
  ensures make_generic_s_Account(result) == snap

predicate p_Int_i32(self: Ref) { acc(self.p_Int_i32_val, write) }

predicate p_Account(self: Ref) {
  acc(p_Int_i32(s_Account_field_0(self)), write) &&
  (acc(p_Int_i32(s_Account_field_1(self)), write) &&
   acc(p_Int_i32(s_Account_field_2(self)), write))
}

predicate p_Param(self: Ref, T$0: Type)

function p_Account_snap(self: Ref): s_Account
  requires acc(p_Account(self), write)
{
  (unfolding acc(p_Account(self), write) in
    s_Account_cons(p_Int_i32_snap(s_Account_field_0(self)),
                   p_Int_i32_snap(s_Account_field_1(self)),
                   p_Int_i32_snap(s_Account_field_2(self))))
}

method p_Account_assign(self: Ref, value: s_Account)
  ensures acc(p_Account(self), write)
  ensures p_Account_snap(self) == value
```]

Nine declarations, and between them they exercise most of the language. #vi[`s_Int_i32`]
is a domain: uninterpreted functions plus triggered axioms, and the pattern every
Rust scalar is given (@sec:impl-adts). #vi[`p_Int_i32_val`] is the one field
declaration a Prusti program needs per primitive type — every heap location in the
encoding bottoms out at one of these (@sec:impl-fields). #vi[`p_Int_i32`] and
#vi[`p_Account`] are predicates, the second nesting three instances of the first,
which is how Prusti encodes a struct's ownership (@sec:impl-predicates).
#vi[`p_Param`] is the one predicate declared _without_ a body: a value of a generic
type parameter, whose representation is not known where the encoding was generated.

#vi[`p_Account_snap`] is a heap-dependent function: it demands permission in its
precondition and its body opens the predicate with an #vi[`unfolding`] to read
what is inside. It is the bridge between the two worlds — permission on one side, a
pure snapshot value on the other — and @sec:impl-functions is about how a verifier
can cross that bridge without re-proving the function at every occurrence.
#vi[`make_generic_s_Account`] and #vi[`make_concrete_s_Account`] are the opposite
shape: no body at all, and a postcondition stating that the two are inverse. They
are the only members whose entire content is a contract, and what they ask for is
pure equality reasoning.

Finally #vi[`p_Account_assign`] is a method: no body, a two-clause postcondition,
and every call to it is a permission transaction rather than a jump
(@sec:impl-calls). The method bodies Prusti emits are flat #vi[`goto`] graphs, and
#ru[`account_deposit`]'s is the branch this chapter's control-flow section works
through.

#para[What we left out] Three families were cut from the listing, none of them a
new mechanism. The #vi[`TypeOf`] and trait domains are more of #vi[`s_Int_i32`]:
uninterpreted functions and axioms, in bulk. The
#vi[`mir_binop_AddWithOverflow_Int_i32_Int_i32`] family — Prusti's overflow-checking
arithmetic — is a dozen bodyless functions with #vi[`ensures`] clauses, exactly
the #vi[`make_generic`] shape at greater length. And each method body carries a
#vi[`label`] per statement, which the encoder emits so that #vi[`old`] can name any
intermediate state; a label costs the verifier a named heap (@sec:impl-cfg) and
nothing else.

The contract, then. By the end of this chapter every construct in
@lst:example-viper has a lowering, an execution rule, and a section that owns it.
@sec:impl-together comes back with the unabridged program and checks that claim
construct by construct.
