#import "@preview/cetz:0.4.2"

// A log-log scatter of one verification unit's cost against the size of the
// e-graph it built, for section 5.4.
//
// Both axes are log-10 because both quantities span three orders of magnitude
// across the corpus: a member is a few milliseconds or several seconds, and its
// graph a few dozen e-nodes or several thousand. On linear axes every point but
// the largest handful collapses into the origin.
//
// The line is fitted over every member of the corpus, not over the points drawn.
// Drawing a subset keeps the plot readable; fitting the subset would let the
// choice of which members to draw decide the law they are supposed to obey.
//
// `series` is a list of dictionaries:
//   (name: [branch-structured], colour: rgb(...), points: ((1150, 0.42), ...))
// with x in e-nodes and y in seconds, both unlogged.
// `fit` is (slope, intercept) in log-10 space, so the line is
//   log10(seconds) = slope * log10(nodes) + intercept.

#let _log(v) = calc.log(calc.max(v, 1e-9), base: 10)

#let member-scatter(
  series,
  fit: none,
  x-label: [e-nodes in the member's ground e-graph],
  y-label: [seconds],
  x-from: 1,
  x-to: 5,
  y-from: -4,
  y-to: 1,
  width: 9.5,
  height: 6.0,
  legend: true,
) = {
  let px(v) = width * (_log(v) - x-from) / (x-to - x-from)
  let py(v) = height * (_log(v) - y-from) / (y-to - y-from)
  let rule-colour = luma(88%)
  let ink = luma(45%)
  let decade(k) = if k < 0 { "0." + "0" * (-k - 1) + "1" } else { "1" + "0" * k }

  cetz.canvas(length: 1cm, {
    import cetz.draw: *

    for k in range(y-from, y-to + 1) {
      let y = height * (k - y-from) / (y-to - y-from)
      line((0, y), (width, y), stroke: 0.5pt + rule-colour)
      content((-0.25, y), text(size: 7pt, fill: ink, decade(k)), anchor: "east")
    }
    for k in range(x-from, x-to + 1) {
      let x = width * (k - x-from) / (x-to - x-from)
      line((x, 0), (x, -0.12), stroke: 0.7pt + ink)
      content((x, -0.28), text(size: 7pt, fill: ink, decade(k)), anchor: "north")
    }

    line((0, 0), (width, 0), stroke: 0.7pt + ink)
    line((0, 0), (0, height), stroke: 0.7pt + ink)
    content((width / 2, -0.85), text(size: 7.5pt, fill: ink, x-label))
    content((-1.05, height / 2), angle: 90deg, text(size: 7.5pt, fill: ink, y-label))

    // The fitted law, drawn across the full width so a reader can see which
    // points sit above it and which below.
    if fit != none {
      let (slope, intercept) = fit
      let fy(k) = height * ((slope * k + intercept) - y-from) / (y-to - y-from)
      line(
        (0, fy(x-from)), (width, fy(x-to)),
        stroke: (paint: luma(35%), thickness: 0.9pt, dash: "dashed"),
      )
    }

    for s in series {
      for (x, y) in s.points {
        circle((px(x), py(y)), radius: 0.07, stroke: none, fill: s.colour)
      }
    }

    if legend {
      let y = height + 0.45
      let step = width / calc.max(series.len(), 1)
      for (i, s) in series.enumerate() {
        let x = i * step
        circle((x + 0.15, y), radius: 0.07, stroke: none, fill: s.colour)
        content((x + 0.4, y), text(size: 7.5pt, s.name), anchor: "west")
      }
    }
  })
}
