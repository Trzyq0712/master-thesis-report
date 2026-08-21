#import "../macros.typ": *
#import "@preview/cetz:0.4.2"

/// The state of @sec:impl-execution's fragment either side of its `assume`,
/// drawn as an e-graph: solid boxes are e-nodes, dashed boxes are e-classes,
/// arrows run from a node to the class of each of its arguments.
///
/// The point of the pair is that nothing is rebuilt between the two panels. The
/// `assume` merges one class with `true`; everything else on the right is a
/// consequence propagated into terms that were already there, which is why the
/// classes drawn in amber are the whole of the difference.
#let egraph-assume = {
  set par(justify: false)
  set text(hyphenate: false)

  let base = rgb("#0f766e")
  let hot = rgb("#b45309")

  let nw = 0.66
  let nh = 0.44
  let mono(s, size: 0.62em, fill: base.darken(35%)) = text(
    size: size,
    font: "DejaVu Sans Mono",
    fill: fill,
    s,
  )

  cetz.canvas({
    import cetz.draw: *

    // One e-node: a filled, rounded box centred on `pos`.
    let node(pos, label, hue) = {
      rect(
        (pos.at(0) - nw / 2, pos.at(1) - nh / 2),
        (pos.at(0) + nw / 2, pos.at(1) + nh / 2),
        fill: hue.lighten(90%),
        stroke: 0.5pt + hue.darken(5%),
        radius: 1.5pt,
      )
      content(pos, mono(label, fill: hue.darken(35%)))
    }

    // The dashed box around a run of e-nodes, plus the handles naming it.
    let cls(x0, x1, y, hue, tag) = {
      let p = 0.15
      rect(
        (x0 - nw / 2 - p, y - nh / 2 - p),
        (x1 + nw / 2 + p, y + nh / 2 + p),
        stroke: (paint: hue, thickness: 0.55pt, dash: "dashed"),
        radius: 3pt,
      )
      if tag != none {
        content(
          ((x0 + x1) / 2, y + nh / 2 + p + 0.04),
          anchor: "south",
          mono(tag, size: 0.55em, fill: hue.darken(10%)),
        )
      }
    }

    // A node-to-class edge, leaving the parent's bottom and arriving at the top
    // of the child's class box. `dx` shifts the departure point, so a node with
    // two arguments in the same class draws two arrows into it; `sag` bends the
    // edge below the row between the two, clearing the boxes sitting there.
    let edge(from, to, hue: luma(55%), dx: 0.0, sag: none) = {
      let p0 = (from.at(0) + dx, from.at(1) - nh / 2)
      let p1 = (to.at(0) + dx, to.at(1) + nh / 2 + 0.15)
      let s = 0.5pt + hue
      let m = (end: ">", scale: 0.26)
      if sag == none { line(p0, p1, mark: m, stroke: s) } else {
        bezier(p0, p1, sag, mark: m, stroke: s)
      }
    }

    let panel(x, title, after) = {
      let y0 = 0.0 // a, b, 2
      let y1 = 1.3 // the multiplications
      let y2 = 2.6 // the equalities and `true`

      content((x + 2.1, y2 + 1.0), text(size: 0.68em, weight: "bold", fill: luma(25%), title))

      if not after {
        // Six classes, one node each: nothing in the graph is equal to anything
        // else yet, and `e4` is an `==` over two classes that differ.
        let a = (x + 0.45, y0)
        let two = (x + 1.65, y0)
        let b = (x + 2.85, y0)
        let m0 = (x + 1.05, y1)
        let m1 = (x + 2.35, y1)
        let goal = (x + 1.7, y2)
        let eq = (x + 3.75, y1)
        let tt = (x + 3.75, y2)

        edge(m0, a)
        edge(m0, two)
        edge(m1, two)
        edge(m1, b)
        edge(goal, m0)
        edge(goal, m1)
        edge(eq, b)
        edge(eq, a)

        for (p, l, t) in (
          (a, "a", "e0"),
          (two, "2", none),
          (b, "b", "e1"),
          (m0, "*", "e2"),
          (m1, "*", "e3"),
          (goal, "==", "e4"),
          (eq, "==", "e5"),
          (tt, "true", none),
        ) {
          cls(p.at(0), p.at(0), p.at(1), base, t)
          node(p, l, base)
        }
      } else {
        // `a ~ b` by the assumed equality, `a * 2 ~ b * 2` by congruence over
        // it, and both equalities in the class of `true` by reflexivity.
        let a = (x + 0.19, y0)
        let b = (x + 1.01, y0)
        let ab = (x + 0.6, y0)
        let two = (x + 2.7, y0)
        let m = (x + 0.6, y1)
        let goal = (x + 1.65, y2)
        let eq = (x + 2.47, y2)
        let tt = (x + 3.29, y2)

        edge(m, ab, hue: hot.lighten(10%))
        edge(m, two)
        for d in (-0.13, 0.13) {
          edge(goal, m, hue: hot.lighten(10%), dx: d)
          // Curved out to the right of the `*` class rather than through it.
          edge(eq, ab, hue: hot.lighten(10%), dx: d, sag: (x + 2.0 + d, y1 - 0.3))
        }

        cls(a.at(0), b.at(0), y0, hot, "e0, e1")
        node(a, "a", hot)
        node(b, "b", hot)

        cls(two.at(0), two.at(0), y0, base, none)
        node(two, "2", base)

        cls(m.at(0), m.at(0), y1, hot, "e2, e3")
        node(m, "*", hot)

        cls(goal.at(0), tt.at(0), y2, hot, "e4, e5")
        node(goal, "==", hot)
        node(eq, "==", hot)
        node(tt, "true", hot)
      }
    }

    let pw = 4.3
    let gap = 1.5
    panel(0, [before #raw("assume e5")], false)
    panel(pw + gap, [after #raw("assume e5")], true)

    // The step between the two states.
    line(
      (pw + 0.3, 1.3),
      (pw + gap - 0.3, 1.3),
      mark: (end: ">", scale: 0.34),
      stroke: 0.7pt + hot,
    )
    content(
      (pw + gap / 2, 1.4),
      anchor: "south",
      text(size: 0.55em, fill: hot.darken(15%))[union],
    )
  })
}
