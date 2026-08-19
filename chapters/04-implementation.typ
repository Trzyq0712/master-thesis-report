#import "../macros.typ": *

// The chapter is split one file per section, under `chapters/04/`.

#note[
  *How this chapter is organised.* Every section follows the same three beats:
  the Viper construct, the VMIR it lowers to (a lowering table), and how the
  verifier executes that VMIR.

  Some design decisions are forced by Prusti's encoding and some are right for
  any frontend. Where the difference matters, say so in the sentence itself —
  Future Work depends on the reader being able to tell them apart. An earlier
  draft carried inline P/G markers for this; they read as unfilled gaps rather
  than as annotations, so the distinction is prose now or nothing.

  Where we deliberately stop short of a proof, the section ends with a
  #emph[what we record] paragraph: the symbolic state stays complete even
  though the decision procedure is not, so a failed obligation is a failure to
  prove rather than a loss of information. Beyond the Fragment collects these.

  Structure below `==` uses run-in `#para[..]` headings, never a third
  heading level.
]

This chapter builds the new backend one construct at a time. It opens with a real
Prusti encoding — the program the whole chapter is answerable to — and with a
short look at VMIR itself, enough that the listings which follow read without a
preamble. It then starts from the smallest thing a verifier can do: execute a heapless method and discharge
an obligation about it. The symbolic heap arrives next, first without any
conditional structure at all, so that the operations on it can be stated on their
own; then fields and predicates, which are the two things a program can hold
permission to; then control flow, which is what forces two heaps to be reconciled
and where the representation earns or loses its keep. Methods, functions,
datatypes, quantifiers and loops follow, each needing the ones before it and
nothing after.

The order is deliberate in one further respect. Each section says what its
construct costs the verifier and, where the answer differs from Silicon's, why.
The claim the chapter is accumulating is not that any single mechanism is novel,
but that a particular set of them composes into a verifier on which the great
majority of a Prusti program's obligations are true by construction rather than by
proof — and @sec:impl-together is where that claim is cashed out on the program
@sec:impl-example put on the table.

One convention about the listings. VMIR is an explicit representation and its
real form is correspondingly verbose: a postcondition, for instance, is not
syntax attached to a declaration but a function of its own. Where that verbosity
would bury the point a listing is making, the listing is written in
_pseudo-VMIR_ — the same language with the mechanical parts elided — and tagged
as such. Anything tagged VMIR is what the verifier would actually be given.

#include "04/01-worked-example.typ"
#include "04/02-vmir.typ"
#include "04/03-execution-model.typ"
#include "04/04-discharging.typ"
#include "04/05-symbolic-heap.typ"
#include "04/06-fields.typ"
#include "04/07-heap-interaction.typ"
#include "04/08-predicates.typ"
#include "04/09-verifying-methods.typ"
#include "04/10-calling-methods.typ"
#include "04/11-domains-adts.typ"
#include "04/12-wildcards.typ"
#include "04/13-functions.typ"
#include "04/14-quantifiers.typ"
#include "04/15-loops.typ"
#include "04/16-putting-together.typ"
#include "04/17-beyond-fragment.typ"
