#import "../macros.typ": *
#import "@preview/cetz:0.4.2"

/// The prove ladder: a single column of tiers, cheapest
/// first, escalating on failure. `implication_decompose` looks like any other
/// row here — its internal loop (clone, assume pc, saturate, recheck) is
/// explained in the surrounding text rather than drawn.
///
/// Only the failure path is drawn: a tier that answers ends the search, so
/// every arrow here means "did not answer". Marking the exits too would put a
/// mark on every row, which distinguishes nothing.
#let prove-ladder = {
  set par(justify: false)
  set text(hyphenate: false)

  let hue = rgb("#0f766e")

  let mw = 4.6 // column width
  let row-h = 0.72

  let rows = (
    [inconsistent],
    [goal\_true],
    [implication\_true],
    [saturate],
    [implication\_decompose],
  )

  cetz.canvas({
    import cetz.draw: *

    for (i, r) in rows.enumerate() {
      let ry = -i * row-h
      rect((0, ry - row-h + 0.26), (mw, ry - 0.02), fill: hue.lighten(90%), stroke: none)
      rect((0, ry - row-h + 0.26), (0.08, ry - 0.02), fill: hue, stroke: none)
      content(
        (mw / 2, ry - row-h / 2 + 0.12),
        text(size: 0.72em, font: "DejaVu Sans Mono", fill: hue.darken(25%), r),
      )
    }
    for i in range(rows.len() - 1) {
      line(
        (mw / 2, -(i + 1) * row-h + 0.25),
        (mw / 2, -(i + 1) * row-h + 0.03),
        mark: (end: ">", scale: 0.3),
        stroke: 0.5pt + luma(60%),
      )
    }

    let bot = -rows.len() * row-h
    line(
      (mw / 2, bot + 0.25),
      (mw / 2, bot - 0.14),
      mark: (end: ">", scale: 0.3),
      stroke: 0.5pt + luma(60%),
    )
    content(
      (mw / 2, bot - 0.26),
      anchor: "north",
      text(size: 0.68em, weight: "bold", fill: hue.darken(10%))[reported unproven],
    )
  })
}
