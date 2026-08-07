#import "../macros.typ": *

// The chapter is split one file per section, under `chapters/04/`.

#note[
  *How this chapter is organised.* Every section follows the same three beats:
  the Viper construct, the VMIR it lowers to (a lowering table), and how the
  verifier executes that VMIR. The third beat is the one still missing in most
  sections.

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

// Go with a guiding example
In this chapter we progressively build up a new backend for Viper,
describing how each of the core features that are necessary to discharge
proofs. We will start out by describing the general execution model and
how it differs from that of Silicon, TODO

To start simply we will look at how a simple heapless program is executed, and then we
will progressively add more complexity, such that it eventually matches the features
required to verify a full Prusti program.

#include "04/01-worked-example.typ"
#include "04/02-execution-model.typ"
#include "04/03-symbolic-heap.typ"
#include "04/04-fields.typ"
#include "04/05-predicates.typ"
#include "04/06-heap-interaction.typ"
#include "04/07-verifying-methods.typ"
#include "04/08-calling-methods.typ"
#include "04/09-domains-adts.typ"
#include "04/10-functions.typ"
#include "04/11-quantifiers.typ"
#include "04/12-loops.typ"
#include "04/13-putting-together.typ"
#include "04/14-beyond-fragment.typ"
