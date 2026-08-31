#import "../macros.typ": *
#import "@preview/cetz:0.4.2"

/// Consolidation (@sec:impl-heap-repr),
/// before and after. Left: one partition, two chunks at
/// distinct location e-classes. Middle: the e-classes merge — this is the
/// step that *triggers* the fold, drawn as its own arrow rather than folded
/// into the merge itself. Right: one chunk, holding the summed permission and
/// the asymmetrically picked value, with the assumed agreement written
/// beside it.
#let consolidation = {
  set par(justify: false)
  set text(hyphenate: false)

  let base = rgb("#0f766e")
  let hot = rgb("#b45309")
  let ink = rgb("#334155")

  let mono(s, size: 0.62em, fill: ink) = text(size: size, font: "DejaVu Sans Mono", fill: fill, s)

  cetz.canvas({
    import cetz.draw: *

    let pw = 3.1
    let ph = 2.5
    let y-title = 0.32
    let y-loc = -0.75
    let y-chunk = -1.5
    let y-formula = -2.15

    // The outer partition box, shared shape across all three panels.
    let partition-box(x, w, h) = rect(
      (x, 0.6), (x + w, -h),
      fill: base.lighten(95%),
      stroke: 0.6pt + base.darken(5%),
      radius: 3pt,
    )
    let title(x, w, s) = content(
      (x + w / 2, y-title), anchor: "center",
      text(size: 0.62em, weight: "bold", fill: base.darken(20%), s),
    )

    // A dashed location e-class oval around `tag`, at (x, y-loc).
    let loc-class(x, tag, w: 0.7) = {
      rect(
        (x - w / 2, y-loc - 0.18), (x + w / 2, y-loc + 0.18),
        stroke: (paint: hot, thickness: 0.5pt, dash: "dashed"),
        radius: 8pt,
      )
      content((x, y-loc), mono(tag, fill: hot.darken(15%)))
    }
    // A chunk pill at (x, y-chunk).
    let chunk(x, amt, w: 0.95) = {
      rect(
        (x - w / 2, y-chunk - 0.2), (x + w / 2, y-chunk + 0.2),
        fill: base.lighten(88%), stroke: 0.5pt + base.darken(5%), radius: 2pt,
      )
      content((x, y-chunk), mono(amt))
    }

    // Panel 1: before — two distinct location e-classes, each with its chunk.
    let x0 = 0
    partition-box(x0, pw, ph)
    title(x0, pw, [before])
    loc-class(x0 + 0.95, [ell0])
    loc-class(x0 + 2.15, [ell1])
    chunk(x0 + 0.95, "p0, v0")
    chunk(x0 + 2.15, "p1, v1")

    // Panel 2: merge — one e-class, the two chunks still hanging under it.
    let x1 = x0 + pw + 1.9
    partition-box(x1, pw, ph)
    title(x1, pw, [merge])
    loc-class(x1 + 1.55, [ell0 #sym.equiv ell1], w: 1.9)
    chunk(x1 + 0.95, "p0, v0")
    chunk(x1 + 2.15, "p1, v1")

    // Panel 3: after — one chunk, folded, agreement written below it.
    let x2 = x1 + pw + 1.9
    partition-box(x2, pw, ph)
    title(x2, pw, [after])
    loc-class(x2 + pw / 2, [ell0 #sym.equiv ell1], w: 1.9)
    chunk(x2 + pw / 2, "p0+p1, v", w: 1.35)
    content(
      (x2 + pw / 2, y-formula),
      anchor: "north",
      text(size: 0.5em, fill: ink.lighten(10%))[$p_0 > 0 and p_1 > 0 => v_0 = v_1$],
    )

    // The two arrows, each carrying the name of the step it is — the point
    // being that "merge" and "fold" are two different things, not one.
    let step-arrow(xa, xb, y, label) = {
      line(
        (xa, y), (xb, y),
        mark: (end: ">", scale: 0.3),
        stroke: 0.7pt + hot,
      )
      content(
        ((xa + xb) / 2, y + 0.12),
        anchor: "south",
        text(size: 0.55em, fill: hot.darken(15%), label),
      )
    }
    step-arrow(x0 + pw + 0.15, x1 - 0.15, y-loc, [merge (congruence)])
    step-arrow(x1 + pw + 0.15, x2 - 0.15, y-loc, [fold (lookup)])
  })
}
