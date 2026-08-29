#import "../macros.typ": *
#import "@preview/cetz:0.4.2"
#import "egraph-draw.typ": *

/// The state of @sec:impl-execution's fragment either side of its `assume`,
/// drawn as an e-graph: solid boxes are e-nodes, dashed boxes are e-classes,
/// arrows run from a node to the class of each of its arguments.
///
/// The point of the pair is that nothing is rebuilt between the two panels. The
/// `assume` merges one class with `true`; everything else on the right is a
/// consequence propagated into terms that were already there, which is why the
/// classes drawn in amber are the whole of the difference.
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
        // Six classes, one node each: nothing in the graph is equal to anything
        // else yet, and `e4` is an `==` over two classes that differ.
        let a = (x + 0.6, y0)
        let two = (x + 2.15, y0)
        let b = (x + 3.7, y0)
        let m0 = (x + 1.4, y1)
        let m1 = (x + 3.05, y1)
        let goal = (x + 2.2, y2)
        let eq = (x + 4.9, y1)
        let tt = (x + 3.25, y2)

        edge(m0, a, dx: -0.1)
        edge(m0, two, dx: 0.1)
        edge(m1, b, dx: -0.1)
        edge(m1, two, dx: 0.1)
        edge(goal, m0, dx: -0.1)
        edge(goal, m1, dx: 0.1)
        edge(eq, a, dx: -0.1)
        edge(eq, b, dx: 0.1)

        for (p, l, t) in (
          (a, "a", "e0"),
          (two, "2", none),
          (b, "b", "e1"),
          (m0, "*", "e2"),
          (m1, "*", "e3"),
          (eq, "==", "e5"),
        ) {
          cls(p.at(0), p.at(0), p.at(1), base, t)
          node(p, l, base)
        }

        // `e4` already merged with `true`, so the assume on the right only
        // has to account for `e0` with `e1` and `e2` with `e3`.
        cls(goal.at(0), tt.at(0), y2, base, "e4")
        node(goal, "==", base)
        node(tt, "true", base)
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

        edge(m, ab, hue: hot.lighten(10%), dx: -0.1)
        edge(m, two, hue: hot.lighten(10%), dx: 0.1)
        for d in (-0.1, 0.1) {
          edge(goal, m, hue: hot.lighten(10%), dx: d)
          // Curved out to the right of the `*` class rather than through it.
          edge(eq, ab, hue: hot.lighten(10%), dx: d, sag: (x + 2.6 + d, y1 - 0.3))
        }

        cls(a.at(0), b.at(0), y0, hot, ("e0", "e1"))
        node(a, "a", hot)
        node(b, "b", hot)

        cls(two.at(0), two.at(0), y0, base, none)
        node(two, "2", base)

        cls(m.at(0), m.at(0), y1, hot, ("e2", "e3"))
        node(m, "*", hot)

        cls(goal.at(0), tt.at(0), y2, hot, ("e4", "e5"))
        node(goal, "==", hot)
        node(eq, "==", hot)
        node(tt, "true", hot)
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
      stroke: 0.7pt + hot,
    )
    content(
      (pw + gap / 2, 1.8),
      anchor: "south",
      text(size: 0.8em, fill: hot.darken(15%))[saturate],
    )
  })
}
