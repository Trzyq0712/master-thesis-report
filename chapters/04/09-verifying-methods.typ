#import "../../macros.typ": *

== Verifying Methods <sec:impl-methods>

A call site is one end of a contract; a method body is the other. Verifying one is
walking it once against a heap its _own_ precondition built rather than one a
caller supplied, and checking the postcondition where the walk stops. Both ends
are the resource operations of @sec:impl-predicates applied to the contracts
@sec:impl-calls lowered, so almost nothing here is new — what the section adds is
the frame a method puts around them.

The body below is straight-line, and that is the whole of the restriction. A
method whose body branches has two heaps to reconcile where the arms meet, which
is @sec:impl-cfg.

A method body starts from #vm[`empty`]. Nothing is inherited,
because a method may assume only what its contract grants it, so the state the
body works in is built by its first instructions: a fresh value per parameter and
per return variable, a fresh snapshot handle, and an inhale of the precondition
resource bound to that handle.

#lowering(
  caption: [A method with one block: the prologue builds the entry heap, the exit
    checks the contract against it.],
  label: "lst:method-simple",
  target-lang: "lvmir",
)[```viper
method m(x: Ref) returns (v: i32)
  requires acc(x.val_i32)
  ensures acc(x.val_i32)
{
  v := x.val_i32
  x.val_i32 := i32_cons(0)
}
```][```lvmir
e0: Ref := fresh                 // x
e1: i32 := fresh           // v
e2: m#requires@snap := fresh
h0 := empty inhale m#requires(e0)
      @ 1/1 with e2

e3: &[val_i32] i32 @ 1/1
   := val_i32(e0)
e4: i32 := *[h0] e3        // v
e5: i32 := i32_cons(0)
h1 := h0 assign(e3, e5)

h2, _ := h1 exhale m#ensures(e0, e4, e2)
         @ 1/1
```]

The two middle lines are @sec:impl-heap-interaction unchanged: a read out of
#vm[`h0`], then an assignment producing #vm[`h1`]. The read goes through because
the prologue's inhale put a chunk at #vm[`val_i32(e0)`], and the write goes
through because that chunk is at the bound — both obligations are the ordinary
ones, raised against a heap the contract happens to have built.

The prologue binds its inhale to #vm[`e2`] rather than writing
#vm[`with fresh`], and the difference is that the handle is needed twice. The exit
exhales the postcondition against the state the precondition described, and a
two-state postcondition resource takes that snapshot as an argument
(@sec:impl-calls), so the two mentions have to be the same value. Binding is what
makes them one; the slots underneath are no less arbitrary for it, since nothing
constrains the handle either.

Each exit block exhales the postcondition against the final values
of the return variables — #vm[`e4`] above, the value #vi[`v`] ended up naming,
rather than the #vm[`e1`] the prologue created for it. The exhale is the one of
#pararef(<para:impl-subtract>, [Giving permission back]): it walks the
postcondition's footprint raising a sufficiency obligation at each slot, and
asserts the resource's boolean. A method that cannot give back what it promised
fails there, at a named slot, exactly as a caller failing a precondition does.

Its two results go nowhere, and @lst:method-simple shows both: the heap
#vm[`h2`] is never mentioned again, since the walk is over and nothing reads the
state a method leaves behind, and the snapshot is blanked, since a
postcondition's slot values are what the _caller_ receives rather than anything
the callee has a use for.

A method that fails does so at one instruction, with the
walk up to it intact: the entry heap is the one the precondition built, every
chunk since is where the body put it, and the obligation naming the failure is an
e-class in that state.
