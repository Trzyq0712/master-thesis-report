#import "../macros.typ": *
#import "@preview/cetz:0.4.2"

/// The symbolic heap of @sec:impl-heap-partitioning, drawn as one box per
/// partition — location kind (group, stored type, permission bound) — with
/// its chunks inside. Two field groups and one predicate group, which is
/// enough to make three things visible at a glance rather than argued for a
/// paragraph each: a chunk cannot be in two boxes, `x.f` and `y.g` are in
/// different boxes even though both are `Int @ 1/1`, and the predicate box
/// is the `*`-bounded one — dashed, and captioned as receiving no axioms.
#let heap-partitions = {
  set par(justify: false)
  set text(hyphenate: false)

  let base = rgb("#0f766e")
  let hot = rgb("#b45309")
  let ink = rgb("#334155")

  let mono(s, size: 0.68em, fill: ink) = text(size: size, font: "DejaVu Sans Mono", fill: fill, s)

  cetz.canvas({
    import cetz.draw: *

    // A chunk: a small filled pill with its location and (perm, value).
    let chunk(x, y, w, loc, amt) = {
      rect(
        (x, y - 0.32),
        (x + w, y + 0.02),
        fill: base.lighten(90%),
        stroke: 0.5pt + base.darken(5%),
        radius: 2pt,
      )
      content((x + w / 2, y - 0.15), mono(loc + "  " + amt, size: 0.6em))
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
        text(size: 0.62em, weight: "bold", fill: hue.darken(25%), title),
      )
      for (i, c) in chunks.enumerate() {
        chunk(x + 0.16, y - 0.55 - i * 0.44, w - 0.32, c.at(0), c.at(1))
      }
      content(
        (x + w / 2, y - h + 0.16),
        anchor: "south",
        text(size: 0.52em, style: "italic", fill: hue.darken(10%), footer),
      )
    }

    let pw = 2.5
    let gap = 0.35

    partition(
      0, 0, pw, 1.55,
      [`&[f] Int @ 1/1`], base, false,
      (("x.f", "1/1, v"),),
      [bounded: `p ≤ 1/1`],
    )
    partition(
      pw + gap, 0, pw, 1.55,
      [`&[g] Int @ 1/1`], base, false,
      (("y.g", "1/1, w"),),
      [bounded: `p ≤ 1/1`],
    )
    partition(
      2 * (pw + gap), 0, pw, 1.99,
      [`&[P] SnapP @ *`], hot, true,
      (("P(x)", "1/2, s0"), ("P(y)", "1/1, s1")),
      [unbounded: no axioms],
    )
  })
}
