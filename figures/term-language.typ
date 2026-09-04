#import "../macros.typ": *

/// The language of terms an e-graph holds, as a grammar with one alternative
/// per line and what that alternative is beside it, so a reader can count the
/// seven forms off the page without reading a paragraph for them. The binary
/// operators get a production of their own rather than a gloss on the `t ⊕ t`
/// line: there are twelve of those, carrying the operand sort in a subscript,
/// and burying them in prose beside the form they belong to made the line the
/// widest on the page.
#let term-language = {
  // The glosses are short enough that justification only stretches them.
  set par(justify: false)
  let gloss(body) = text(size: 0.92em, fill: luma(30%), body)

  grid(
    columns: (auto, auto, auto, 1fr),
    column-gutter: (0.4em, 0.45em, 2em),
    row-gutter: 0.7em,
    align: (right + top, center + top, left + top, left + top),

    $t$, $::=$, $"fresh"_n$, gloss[an unconstrained value],

    [], $|$, $c$, gloss[a literal: boolean, integer, rational, or #vm[`null`]],

    [], $|$, $t plus.o t$, gloss[a binary operation],

    [], $|$, $ternary(t, t, t)$, gloss[the sole boolean connective],

    [], $|$, $f(t, ..., t)$, gloss[a function application],

    [], $|$, $"real"(t)$, gloss[an integer to real cast],

    [], $|$, $forall_r (t, ..., t)$, gloss[a quantifier with compiled body $r$ over its inputs],

    // The operator production, set off from the term production above it.
    v(0.45em), [], [], [],

    $plus.o$,
    $::=$,
    $+_i #h(0.4em) | #h(0.4em) -_i #h(0.4em) | #h(0.4em) *_i #h(0.4em) | #h(0.4em) \/_i #h(0.4em) | #h(0.4em) "mod"$,
    gloss[integer arithmetic],

    [], $|$, $+_r #h(0.4em) | #h(0.4em) -_r #h(0.4em) | #h(0.4em) *_r #h(0.4em) | #h(0.4em) \/_r$, gloss[rational arithmetic],

    [], $|$, $scripts(<)_i #h(0.4em) | #h(0.4em) scripts(<)_r$, gloss[ordering, one per numeric sort],

    [], $|$, $=$, gloss[equality, at any one type],
  )
}
