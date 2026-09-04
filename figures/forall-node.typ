#import "../macros.typ": *
#import "@preview/cetz:0.4.2"
#import "egraph-draw.typ": op

/// What a `forall` puts in the e-graph, and what a firing does.
///
/// Left is the node: a payload naming its recipe, and one child per captured
/// value. Right is the recipe of @lst:quant-capture, drawn as the term graph it
/// is, with its capture and its binder left open as holes. A firing fills the two holes from
/// opposite sides, one from the node's child and one from the term the trigger
/// matched, and the root flows back into the graph gated on the quantifier's
/// own class.
///
/// E-class boxes are left out: nothing here turns on which nodes share a class,
/// and the dashed boxes only competed with the holes for the reader's eye.
/// Text is kept to node labels and three edge labels, since the shape is the
/// argument. The `forall`'s own child edge is an ordinary operand edge, so the
/// hues separate the roles rather than the elements: violet is the capture,
/// orange the binder and the boxed term the trigger matched.
#let forall-node = {
  set par(justify: false)
  set text(hyphenate: false)

  let base = rgb("#0f766e") // already in the graph
  let hot = rgb("#b45309") // the binder, and the term the trigger matched
  let cap = rgb("#7c3aed") // the capture
  let ink = rgb("#334155")

  let nh = 0.56

  let mono(s, size: 0.78em, fill: base.darken(35%)) = text(
    size: size,
    font: "DejaVu Sans Mono",
    fill: fill,
    s,
  )
  let lbl(s, fill: ink) = text(size: 0.68em, weight: "bold", fill: fill, s)
  let tag(s, fill: hot) = text(size: 0.64em, fill: fill.darken(10%), s)

  cetz.canvas({
    import cetz.draw: *

    // cetz crops to the ink, which reads cramped against a caption.
    rect((-0.6, -5.6), (10.3, 1.15), stroke: none, fill: none)

    let node(pos, label, hue, w: 1.3, name: none) = {
      rect(
        (pos.at(0) - w / 2, pos.at(1) - nh / 2),
        (pos.at(0) + w / 2, pos.at(1) + nh / 2),
        fill: hue.lighten(90%),
        stroke: 0.5pt + hue.darken(5%),
        radius: 1.5pt,
      )
      content(pos, mono(label, fill: hue.darken(35%)))
      if name != none {
        content(
          (pos.at(0) - w / 2, pos.at(1) + nh / 2 + 0.04),
          anchor: "south-west",
          mono(name, size: 0.7em, fill: hue.darken(10%)),
        )
      }
    }

    // A node-to-operand edge.
    let arg(from, to, dx: 0.0, hue: ink.lighten(30%)) = line(
      (from.at(0) + dx, from.at(1) - nh / 2),
      (to.at(0) + dx * 0.5, to.at(1) + nh / 2),
      mark: (end: ">", scale: 0.5),
      stroke: 0.5pt + hue,
    )

    // ------------------------------------------------------------------
    // Left: the e-graph.
    // ------------------------------------------------------------------
    content((-0.5, 0.78), anchor: "west", lbl("e-graph"))

    let q = (1.3, 0.0)
    let k = (0.3, -4.0)
    let bx = (2.7, -1.7)
    let three = (2.7, -2.9)

    // The term the trigger matched, boxed as a unit: the match is against
    // `f(3)`, not against either node on its own.
    rect(
      (bx.at(0) - 0.95, three.at(1) - nh / 2 - 0.28),
      (bx.at(0) + 0.95, bx.at(1) + nh / 2 + 0.28),
      stroke: (paint: hot, thickness: 0.7pt, dash: "dashed"),
      fill: hot.lighten(96%),
      radius: 3pt,
    )
    content(
      (bx.at(0) + 0.95, bx.at(1) + nh / 2 + 0.34),
      anchor: "south-east",
      tag("matched"),
    )

    node(q, "forall", base, w: 1.6)
    node(k, "k", base, w: 1.0)
    node(bx, "f", base, w: 1.0)
    node(three, "3", base, w: 1.0)
    arg(bx, three, hue: luma(55%))

    // The node's one child. Drawn like any other operand edge: orange is
    // reserved for the firing, so the reader can tell the standing graph from
    // what one instantiation does to it.
    line(
      (q.at(0) - 0.5, q.at(1) - nh / 2),
      (k.at(0), k.at(1) + nh / 2),
      mark: (end: ">", scale: 0.5),
      stroke: 0.5pt + ink.lighten(30%),
    )
    content((0.28, -2.1), anchor: "east", lbl("capture", fill: cap.darken(15%)))

    // ------------------------------------------------------------------
    // Right: the recipe, drawn as the term graph it is.
    // ------------------------------------------------------------------
    let x0 = 4.2
    rect(
      (x0, -4.6),
      (9.9, 0.6),
      stroke: 0.8pt + ink.lighten(45%),
      fill: luma(98.5%),
      radius: 3pt,
    )
    content((x0, 0.78), anchor: "west", lbl("recipe"))

    let eq = (7.1, 0.0)
    let plus = (5.6, -1.5)
    let ubx = (8.4, -1.5)
    let rbx = (4.9, -2.9)
    let t0 = (6.3, -4.0)
    let t1 = (8.4, -4.0)

    node(eq, op(">", "i"), ink, w: 1.0)
    node(plus, op("/", "i"), ink, w: 1.0)
    node(ubx, "f", ink, w: 1.0)
    node(rbx, "1", ink, w: 1.0)

    // The holes a firing fills.
    let hole(pos, name, hue) = {
      rect(
        (pos.at(0) - 0.5, pos.at(1) - nh / 2),
        (pos.at(0) + 0.5, pos.at(1) + nh / 2),
        fill: hue.lighten(92%),
        stroke: (paint: hue, thickness: 0.7pt, dash: "dashed"),
        radius: 1.5pt,
      )
      content(pos, mono(name, size: 0.76em, fill: hue.darken(25%)))
    }
    hole(t0, "t0", cap)
    hole(t1, "t1", hot)

    arg(eq, plus, dx: -0.22)
    arg(eq, ubx, dx: 0.22)
    arg(plus, rbx, dx: -0.2)
    arg(plus, t0, dx: 0.2)
    arg(ubx, t1)

    // The payload names the recipe. Dotted, because it is not a child.
    line(
      (q.at(0) + 0.8, 0.0),
      (x0, 0.0),
      mark: (end: ">", scale: 0.45),
      stroke: (paint: ink.lighten(5%), thickness: 0.7pt, dash: "dotted"),
    )

    // ------------------------------------------------------------------
    // The firing: the two holes filled from opposite sides.
    // ------------------------------------------------------------------
    line(
      (k.at(0) + 0.5, k.at(1)),
      (t0.at(0) - 0.5, t0.at(1)),
      mark: (end: ">", scale: 0.5),
      stroke: 0.9pt + cap,
    )

    // Routed under everything, so it crosses nothing on its way.
    line(
      (three.at(0), three.at(1) - nh / 2),
      (three.at(0), -5.2),
      (t1.at(0), -5.2),
      (t1.at(0), t1.at(1) - nh / 2),
      mark: (end: ">", scale: 0.5),
      stroke: 0.9pt + hot,
    )
    content((5.15, -5.15), anchor: "south", tag("trigger match"))

  })
}
