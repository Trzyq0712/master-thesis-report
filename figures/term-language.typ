#import "../macros.typ": *

/// The language of terms an e-graph holds, as a grammar with one alternative
/// per line and what that alternative is beside it, so a reader can count the
/// seven forms off the page without reading a paragraph for them.
#let term-language = {
  // The glosses are short enough that justification only stretches them.
  set par(justify: false)
  let gloss(body) = text(size: 0.92em, fill: luma(30%), body)

  grid(
    columns: (auto, auto, auto, 1fr),
    column-gutter: (0.4em, 0.45em, 2em),
    row-gutter: 0.7em,
    align: (right + top, center + top, left + top, left + top),

    $t$, $::=$, $"fresh"_n$,
    gloss[an unconstrained value, one per instruction that mints it],

    [], $|$, $c$,
    gloss[a literal: a boolean, an integer, a rational, or #vm[`null`]],

    [], $|$, $t plus.o t$,
    gloss[arithmetic, the remainder, and #vm[`<`], each over the integers or
      over the rationals, and an equality at any type],

    [], $|$, $ternary(t, t, t)$,
    gloss[the ternary, the only boolean connective],

    [], $|$, $f(t, ..., t)$,
    gloss[a function applied to its arguments],

    [], $|$, $"real"(t)$,
    gloss[an integer used where a rational is expected],

    [], $|$, $forall_r (t, ..., t)$,
    gloss[a quantifier, carrying a compiled body $r$ over the terms it captures],
  )
}
