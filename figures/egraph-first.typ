#import "../macros.typ": *
#import "@preview/cetz:0.4.2"
#import "egraph-draw.typ": *

/// The e-graph of @sec:impl-execution's first program, either side of its
/// `assume`. It is the reader's first sight of the notation, so it holds four
/// nodes and one step: the `assume` merges the class of the `==` node with the
/// class of `true`.
///
/// The right panel carries both handles on the merged class, which is what
/// makes the assertion that follows a comparison of two handles. Re-stating the
/// equality as `e2` builds no node, because the graph already holds one with
/// the same operator over the same classes, so `e2` names the class `e1`
/// already named.
#let egraph-first = {
  set par(justify: false)
  set text(hyphenate: false)

  cetz.canvas({
    import cetz.draw: *

    let panel(x, after) = {
      let y0 = 0.0 // a and the constant 42
      let y1 = 1.7 // the equality and `true`

      let a = (x + 0.6, y0)
      let const = (x + 2.15, y0)
      let eq = (x + 1.4, y1)

      edge(eq, a, dx: -0.1)
      edge(eq, const, dx: 0.1)

      cls(a.at(0), a.at(0), y0, ink, "e0")
      node(a, "Int#0", ink)
      cls(const.at(0), const.at(0), y0, ink, none)
      node(const, "42", ink)

      if not after {
        // Two classes at the top row: the equality is a term like any other,
        // and holds no truth value until the `assume` gives it one.
        let tt = (x + 3.6, y1)
        cls(eq.at(0), eq.at(0), y1, ink, "e1")
        node(eq, "==", ink)
        cls(tt.at(0), tt.at(0), y1, ink, none)
        node(tt, "true", ink)
      } else {
        // The merge, and the second handle the assertion arrives with.
        let tt = (x + 2.45, y1)
        cls(eq.at(0), tt.at(0), y1, ink, "e1")
        node(eq, "==", ink)
        node(tt, "true", ink)
      }
    }

    let pw = 4.6
    let gap = 2.1
    panel(0, false)
    panel(pw + gap, true)

    // The step between the two states.
    line(
      (pw + 0.3, 0.85),
      (pw + gap - 0.3, 0.85),
      mark: (end: ">", scale: 0.34),
      stroke: 0.7pt + ink,
    )
    content(
      (pw + gap / 2, 0.95),
      anchor: "south",
      mono("assume e1", size: 0.8em),
    )
  })
}
