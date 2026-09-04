#import "../macros.typ": *
#import "@preview/cetz:0.4.2"

/// The block graph of @lst:cfg-branch, drawn as one box per block. Each box
/// carries the block's header — its number and its path condition — and the heap the
/// block leaves behind, so the two things the section argues about are visible
/// at once: a path condition is a property of a block rather than of an instruction, and
/// a heap is an ordinary named value that an edge carries.
///
/// The join block is the amber one, and it is the only box with a third line,
/// because the merge is what the figure exists to show: two heaps reach it and
/// one leaves. Instructions are deliberately left out — the listing beside the
/// figure has them, and repeating them here would make the boxes the listing
/// with boxes drawn round it.
#let cfg-blocks = {
  set par(justify: false)
  set text(hyphenate: false)

  let base = rgb("#0f766e")
  let hot = rgb("#b45309")
  let ink = rgb("#334155")

  let mono(s, size: 0.72em, fill: ink) = text(size: size, font: "DejaVu Sans Mono", fill: fill, s)

  cetz.canvas({
    import cetz.draw: *

    // cetz crops tight to the ink, which reads cramped against the caption.
    rect((-0.3, 0.9), (9.6, -5.3), stroke: none, fill: none)

    // A block: a titled box whose lines are its header and its exit heap.
    let blk(cx, cy, w, h, hue, lines) = {
      rect(
        (cx - w / 2, cy - h / 2),
        (cx + w / 2, cy + h / 2),
        fill: hue.lighten(94%),
        stroke: 0.7pt + hue,
        radius: 3pt,
      )
      for (i, l) in lines.enumerate() {
        content(
          (cx, cy + h / 2 - 0.32 - i * 0.42),
          mono(l, size: if i == 0 { 0.78em } else { 0.72em }, fill: if i == 0 {
            hue.darken(25%)
          } else { ink }),
        )
      }
    }

    // An edge, labelled with the literal it is taken under.
    let edge(from, to, label, lx, ly) = {
      line(from, to, mark: (end: ">", scale: 0.35), stroke: 0.6pt + luma(55%))
      if label != none {
        content((lx, ly), mono(label, size: 0.72em, fill: hot.darken(10%)))
      }
    }

    blk(4.6, 0.0, 3.4, 1.0, base, ("bb0  <>", "h0"))
    blk(1.7, -2.1, 3.0, 1.0, base, ("bb1  <e1>", "h1"))
    blk(7.5, -2.1, 3.0, 1.0, base, ("bb2  <!e1>", "h0"))
    blk(4.6, -4.3, 5.6, 1.45, hot, ("bb3  <>  join e1 [bb1, bb2]", "h2 := merge e1 ? h1 : h0", "body runs on h2"))

    edge((3.9, -0.5), (2.2, -1.6), "e1", 2.6, -0.85)
    edge((5.3, -0.5), (7.0, -1.6), "!e1", 6.6, -0.85)
    edge((2.2, -2.6), (3.5, -3.5), none, 0, 0)
    edge((7.0, -2.6), (5.7, -3.5), none, 0, 0)
  })
}
