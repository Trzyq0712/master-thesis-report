#import "../macros.typ": *
#import "@preview/cetz:0.4.2"

/// The symbolic heap of @sec:impl-heap, drawn as one box per partition, where a
/// partition is a location kind (group, stored type, permission bound), with its
/// chunks inside. Two field groups are enough to make the point at a glance
/// rather than argue it for a paragraph: a chunk cannot be in two boxes, and
/// `f(x)` and `g(y)` are in different boxes even though both are `Int @ 1/1`.
/// A predicate box was dropped here; the `*` bound is explained where predicates
/// are, not in a figure about partitioning.
#let heap-partitions = {
  set par(justify: false)
  set text(hyphenate: false)

  let base = rgb("#0f766e")
  let ink = rgb("#334155")

  let mono(s, size: 0.8em, fill: ink) = text(size: size, font: "DejaVu Sans Mono", fill: fill, s)

  cetz.canvas({
    import cetz.draw: *

    // A chunk: a small filled pill with its location and (perm, value).
    let chunk(x, y, w, loc, amt) = {
      rect(
        (x, y - 0.4),
        (x + w, y + 0.1),
        fill: base.lighten(90%),
        stroke: 0.5pt + base.darken(5%),
        radius: 2pt,
      )
      content((x + w / 2, y - 0.15), mono(loc + " " + $arrow$ + " " + amt, size: 0.8em))
    }

    // A partition: a titled box (solid for a bound partition, dashed for the
    // unbounded `*` one) holding its chunks, with a one-line footer noting
    // whether the location axioms apply.
    let partition(x, y, w, h, title, hue, dashed, chunks, footer) = {
      rect(
        (x, y - h),
        (x + w, y),
        fill: hue.lighten(94%),
        stroke: (paint: hue, thickness: 0.7pt, dash: if dashed { "dashed" } else { none }),
        radius: 3pt,
      )
      content(
        (x + w / 2, y - 0.22),
        text(size: 0.8em, weight: "bold", fill: hue.darken(25%), title),
      )
      for (i, c) in chunks.enumerate() {
        chunk(x + 0.16, y - 0.55 - i * 0.6, w - 0.32, c.at(0), c.at(1))
      }
    }

    let pw = 3.6
    let gap = 0.4

    partition(
      0,
      0,
      pw,
      1.1,
      [`&[f] Int @ 1/1`],
      base,
      false,
      (("f(x)", "1/1, v"),),
      [bounded: `p ≤ 1/1`],
    )
    partition(
      pw + gap,
      0,
      pw,
      1.1,
      [`&[g] Int @ 1/1`],
      base,
      false,
      (("g(y)", "1/1, w"),),
      [bounded: `p ≤ 1/1`],
    )
  })
}
