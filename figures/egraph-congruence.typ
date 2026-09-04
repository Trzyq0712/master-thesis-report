#import "../macros.typ": *
#import "@preview/cetz:0.4.2"
#import "egraph-draw.typ": *

/// One congruence step, for @sec:bg-equality. The reader's first sight of the
/// notation, so it holds as little as the point allows: two variables, two
/// applications of the same function, and the merge that makes the two
/// applications congruent.
///
/// The left panel is the graph after `f(x)` and `f(y)` have been added and
/// nothing is known to be equal. The right panel is the graph after `x` and `y`
/// are merged: one class below holds both variable nodes, so the two `f` nodes
/// apply the same operator to the same class. Restoring the invariant merges
/// their classes too, which is the step the prose calls congruence.
#let egraph-congruence = {
  set par(justify: false)
  set text(hyphenate: false)

  cetz.canvas({
    import cetz.draw: *

    let panel(x, after) = {
      let y0 = 0.0 // the variables
      let y1 = 1.7 // the applications

      if not after {
        let vx = (x + 0.6, y0)
        let vy = (x + 2.3, y0)
        let fx = (x + 0.6, y1)
        let fy = (x + 2.3, y1)

        edge(fx, vx)
        edge(fy, vy)

        cls(vx.at(0), vx.at(0), y0, ink, "x")
        node(vx, "x", ink)
        cls(vy.at(0), vy.at(0), y0, ink, "y")
        node(vy, "y", ink)

        cls(fx.at(0), fx.at(0), y1, ink, none)
        node(fx, "f", ink)
        cls(fy.at(0), fy.at(0), y1, ink, none)
        node(fy, "f", ink)
      } else {
        // The merge leaves one class below holding both variable nodes, so the
        // two `f` nodes name the same argument class and are congruent.
        let vx = (x + 0.92, y0)
        let vy = (x + 1.97, y0)
        let fx = (x + 0.92, y1)
        let fy = (x + 1.97, y1)

        edge(fx, vx)
        edge(fy, vy)

        cls(vx.at(0), vy.at(0), y0, ink, none)
        node(vx, "x", ink)
        node(vy, "y", ink)

        cls(fx.at(0), fy.at(0), y1, ink, none)
        node(fx, "f", ink)
        node(fy, "f", ink)
      }
    }

    let pw = 3.5
    let gap = 2.3
    panel(0, false)
    panel(pw + gap, true)

    // The step between the two states.
    line(
      (pw + 0.2, 0.85),
      (pw + gap - 0.2, 0.85),
      mark: (end: ">", scale: 0.34),
      stroke: 0.7pt + ink,
    )
    content(
      (pw + gap / 2, 0.95),
      anchor: "south",
      mono("x = y", size: 0.8em),
    )
  })
}
