#import "../macros.typ": *
#import "@preview/cetz:0.4.2"

/// The prove ladder of @sec:impl-proving, drawn as two panels rather than one
/// column of tiers: the ladder is not linear. Everything above `probe` asks its
/// question of the live graph; `probe` copies that graph, fixes the path
/// condition in the copy and saturates it, and the same cheap questions are then
/// put to the copy. The second panel is the first one asked again, of a
/// different graph.
///
/// The dashed edge is the bypass: with nothing to assume the `probe` tier has no
/// work to do and no cheap question of the copy can come out differently, so the
/// search drops straight to `ite_decompose`.
///
/// The tier names carry no gloss here — each has a paragraph of its own in the
/// section, and a description column made the figure wider than the text block.
/// Only the failure path is drawn. A tier that answers ends the search, so the
/// arrows between rows all mean "did not answer" — marking the exits as well
/// would put a mark on every row, which distinguishes nothing.
#let prove-ladder = {
  set par(justify: false)
  set text(hyphenate: false)

  let live = rgb("#0f766e")
  let copy-hue = rgb("#b45309")

  let pw = 4.4 // panel width
  let gap = 1.9
  let row-h = 0.98
  let head-h = 0.6
  let x-live = 0
  let x-copy = pw + gap
  let y-copy = -0.45 // the copy panel sits lower, so the two read as stages

  let rows-live = (
    ([inconsistent], [2 lookups]),
    ([goal\_true], [1 lookup]),
    ([imp\_true], [build + find]),
    ([saturate], [no copy]),
  )
  let rows-copy = (
    ([cube unsat], [2 lookups]),
    ([goal\_true], [1 lookup]),
    ([ite\_decompose], [no fork]),
  )

  let live-bot = -rows-live.len() * row-h
  let copy-bot = y-copy - rows-copy.len() * row-h

  let pill(body, hue) = box(
    fill: hue.lighten(88%),
    inset: (x: 0.34em, y: 0.18em),
    radius: 2pt,
    text(size: 0.6em, fill: hue.darken(20%), body),
  )

  cetz.canvas({
    import cetz.draw: *

    let panel(x, y0, title, rows, hue) = {
      let h = rows.len() * row-h
      rect((x, y0 - h), (x + pw, y0 + head-h), fill: hue.lighten(96%), stroke: none)
      content(
        (x + pw / 2, y0 + head-h / 2),
        text(size: 0.66em, weight: "bold", fill: hue.darken(25%), title),
      )
      for (i, r) in rows.enumerate() {
        let ry = y0 - i * row-h
        rect((x + 0.14, ry - row-h + 0.34), (x + pw - 0.14, ry - 0.02), fill: hue.lighten(90%), stroke: none)
        rect((x + 0.14, ry - row-h + 0.34), (x + 0.22, ry - 0.02), fill: hue, stroke: none)
        content(
          (x + 0.4, ry - row-h / 2 + 0.16),
          anchor: "west",
          box(
            width: (pw - 0.76) * 1cm,
            std.grid(
              columns: (1fr, auto),
              align: (left + horizon, right + horizon),
              text(size: 0.7em, font: "DejaVu Sans Mono", fill: hue.darken(25%), r.at(0)),
              pill(r.at(1), hue),
            ),
          ),
        )
      }
      // Not answered here: fall to the next row.
      for i in range(rows.len() - 1) {
        line(
          (x + pw / 2, y0 - (i + 1) * row-h + 0.33),
          (x + pw / 2, y0 - (i + 1) * row-h + 0.02),
          mark: (end: ">", scale: 0.3),
          stroke: 0.5pt + luma(60%),
        )
      }
    }

    panel(x-live, 0, [asked of the live graph], rows-live, live)
    panel(x-copy, y-copy, [asked again, of the copy], rows-copy, copy-hue)

    // `probe` is the edge between the panels, not a tier that answers: it runs
    // out of the bottom of the live panel, up the gap, and into the copy panel.
    // It climbs the *left* of the gap so the bypass below can use the right of
    // it, and the two cross exactly once.
    let mid = x-live + pw + 0.45
    line(
      (x-live + pw / 2, live-bot),
      (x-live + pw / 2, live-bot - 0.5),
      (mid, live-bot - 0.5),
      (mid, y-copy + head-h / 2),
      (x-copy - 0.04, y-copy + head-h / 2),
      mark: (end: ">", scale: 0.32),
      stroke: 0.7pt + copy-hue,
    )

    // The bypass: nothing to assume, so `probe` is skipped along with the cheap
    // questions of the copy, and only `ite_decompose` is left to try. Leaves the
    // `saturate` row on the right and enters the `ite_decompose` row on the left.
    let sat-y = -3 * row-h - row-h / 2 + 0.16
    let ite-y = y-copy - 2 * row-h - row-h / 2 + 0.16
    let x-byp = x-copy - 0.45
    line(
      (x-live + pw - 0.14, sat-y),
      (x-byp, sat-y),
      (x-byp, ite-y),
      (x-copy - 0.04, ite-y),
      mark: (end: ">", scale: 0.3),
      stroke: (paint: copy-hue, thickness: 0.6pt, dash: "dashed"),
    )
    content(
      ((mid + x-byp) / 2, sat-y - 0.08),
      anchor: "north",
      text(size: 0.55em, fill: copy-hue.darken(15%))[no pc],
    )
    content(
      (x-live + pw / 2 + 0.25, live-bot - 0.62),
      anchor: "north-west",
      std.stack(
        dir: ttb,
        spacing: 0.28em,
        text(size: 0.7em, font: "DejaVu Sans Mono", fill: copy-hue.darken(20%))[probe],
        text(size: 0.6em, fill: luma(35%))[copy, fix the cube, saturate],
      ),
    )

    line(
      (x-copy + pw / 2, copy-bot),
      (x-copy + pw / 2, copy-bot - 0.42),
      mark: (end: ">", scale: 0.3),
      stroke: 0.5pt + luma(60%),
    )
    content(
      (x-copy + pw / 2, copy-bot - 0.54),
      anchor: "north",
      text(size: 0.68em, weight: "bold", fill: copy-hue.darken(10%))[reported unproven],
    )
  })
}
