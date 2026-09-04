#import "../macros.typ": *
#import "@preview/cetz:0.4.2"
#import "egraph-draw.typ": *

/// The state of @sec:impl-execution's fragment either side of its `assume`,
/// drawn as an e-graph: solid boxes are e-nodes, dashed boxes are e-classes,
/// arrows run from a node to the class of each of its arguments.
///
/// The point of the pair is that nothing is rebuilt between the two panels. The
/// `assume` merges one class with `true`, and everything else on the right is a
/// consequence propagated into terms that were already there, so the two panels
/// hold the same nodes and differ only in how the classes group them.
#let egraph-saturate = {
  set par(justify: false)
  set text(hyphenate: false)

  cetz.canvas({
    import cetz.draw: *

    let panel(x, after) = {
      let y0 = 0.0 // a, b, 2
      let y1 = 1.7 // the multiplications
      let y2 = 3.4 // the equalities and `true`

      if not after {
        // The state after `assume e5`: the assumed equality `a == b` sits in
        // the class of `true`, and the goal `e4` is an `==` over two classes
        // that are still distinct. Six classes, one node each, plus that pair.
        let a = (x + 0.6, y0)
        let two = (x + 2.15, y0)
        let b = (x + 3.7, y0)
        // Shifted left of their operands so the two edges from `e5` down to
        // `a` and `b` sweep past the row instead of crossing these boxes.
        let m0 = (x + 0.7, y1)
        let m1 = (x + 2.5, y1)
        let goal = (x + 2.2, y2)
        let eq = (x + 3.95, y2)
        let tt = (x + 5.0, y2)

        edge(m0, a, dx: -0.1)
        edge(m0, two, dx: 0.1)
        edge(m1, b, dx: -0.1)
        edge(m1, two, dx: 0.1)
        edge(goal, m0, dx: -0.1)
        edge(goal, m1, dx: 0.1)
        // Curved out to the right of the `*` classes rather than through them.
        edge(eq, a, dx: -0.1, sag: (x + 4.75, y1 - 0.3))
        edge(eq, b, dx: 0.1, sag: (x + 4.95, y1 - 0.3))

        for (p, l, t) in (
          (a, "a", "e0"),
          (two, "2", none),
          (b, "b", "e1"),
          (m0, op("*", "i"), "e2"),
          (m1, op("*", "i"), "e3"),
          (goal, "==", "e4"),
        ) {
          cls(p.at(0), p.at(0), p.at(1), ink, t)
          node(p, l, ink)
        }

        // `assume e5` has already merged the assumed equality with `true`, so
        // the saturation on the right only has to account for `e0` with `e1`,
        // `e2` with `e3`, and the goal with `true`.
        cls(eq.at(0), tt.at(0), y2, ink, "e5")
        node(eq, "==", ink)
        node(tt, "true", ink)
      } else {
        // `a ~ b` by the assumed equality, `a * 2 ~ b * 2` by congruence over
        // it, and both equalities in the class of `true` by reflexivity.
        let a = (x + 0.25, y0)
        let b = (x + 1.3, y0)
        let ab = (x + 0.78, y0)
        let two = (x + 3.5, y0)
        let m = (x + 0.78, y1)
        let goal = (x + 2.15, y2)
        let eq = (x + 3.2, y2)
        let tt = (x + 4.25, y2)

        edge(m, ab, dx: -0.1)
        edge(m, two, dx: 0.1)
        for d in (-0.1, 0.1) {
          edge(goal, m, dx: d)
          // Curved out to the right of the `*` class rather than through it.
          edge(eq, ab, dx: d, sag: (x + 2.6 + d, y1 - 0.3))
        }

        cls(a.at(0), b.at(0), y0, ink, ("e0", "e1"))
        node(a, "a", ink)
        node(b, "b", ink)

        cls(two.at(0), two.at(0), y0, ink, none)
        node(two, "2", ink)

        cls(m.at(0), m.at(0), y1, ink, ("e2", "e3"))
        node(m, op("*", "i"), ink)

        cls(goal.at(0), tt.at(0), y2, ink, ("e4", "e5"))
        node(goal, "==", ink)
        node(eq, "==", ink)
        node(tt, "true", ink)
      }
    }

    let pw = 5.8
    let gap = 2.0
    panel(0, false)
    panel(pw + gap, true)

    // The step between the two states.
    line(
      (pw + 0.3, 1.7),
      (pw + gap - 0.3, 1.7),
      mark: (end: ">", scale: 0.34),
      stroke: 0.7pt + ink,
    )
    content(
      (pw + gap / 2, 1.8),
      anchor: "south",
      text(size: 0.8em, fill: ink)[saturate],
    )
  })
}
