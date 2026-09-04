#import "@preview/cetz:0.4.2"

// A log-scale line chart, for the two generated families of section 5.3.
//
// Both families vary a knob of a generated program and ask what each verifier's
// time does as the knob turns. A linear axis cannot show that: the two tools are
// two to three orders of magnitude apart, so on a linear scale Helium's curve is
// the x-axis. The y-axis is therefore log-10 seconds, and a decade of it is a
// factor of ten either way.
//
// A run abandoned at the cap is a lower bound, not a measurement. Its point is
// drawn hollow and the segment leading into it is dashed, so a reader can see
// where the data stops being data.
//
// `series` is a list of dictionaries:
//   (name: [Silicon], colour: rgb(...), points: ((0, 16.6, false), (1, 41.7, true)))
// with x an index into `x-ticks` and y a time in seconds. An optional `dash` key
// draws that series' line dashed, which is how two families of the same two
// tools are told apart on one pair of axes. It does not change the points: a
// hollow point means censored and nothing else.

#let _log(v) = calc.log(calc.max(v, 1e-9), base: 10)

#let perf-plot(
  series,
  x-ticks: (),
  x-label: none,
  y-label: [seconds],
  y-from: -2,
  y-to: 3,
  width: 9.5,
  height: 5.5,
  legend: true,
) = {
  let nx = x-ticks.len()
  let px(i) = if nx <= 1 { 0.0 } else { width * i / (nx - 1) }
  let py(v) = height * (_log(v) - y-from) / (y-to - y-from)
  let rule-colour = luma(88%)
  let ink = luma(45%)

  cetz.canvas(length: 1cm, {
    import cetz.draw: *

    // Decade gridlines, labelled on the left. A label is 10^k written out, since
    // "0.01" reads faster than "-2" for a reader scanning for a magnitude.
    for k in range(y-from, y-to + 1) {
      let y = height * (k - y-from) / (y-to - y-from)
      line((0, y), (width, y), stroke: 0.5pt + rule-colour)
      let label = if k < 0 { "0." + "0" * (-k - 1) + "1" } else { "1" + "0" * k }
      content((-0.25, y), text(size: 7pt, fill: ink, label), anchor: "east")
    }

    // Axes.
    line((0, 0), (width, 0), stroke: 0.7pt + ink)
    line((0, 0), (0, height), stroke: 0.7pt + ink)

    for (i, tick) in x-ticks.enumerate() {
      line((px(i), 0), (px(i), -0.12), stroke: 0.7pt + ink)
      content((px(i), -0.28), text(size: 7pt, fill: ink, tick), anchor: "north")
    }

    content((-0.95, height / 2), angle: 90deg, text(size: 7.5pt, fill: ink, y-label))
    if x-label != none {
      content((width / 2, -0.85), text(size: 7.5pt, fill: ink, x-label))
    }

    for s in series {
      let pts = s.points
      let family-dash = s.at("dash", default: false)
      for i in range(pts.len() - 1) {
        let (x0, y0, c0) = pts.at(i)
        let (x1, y1, c1) = pts.at(i + 1)
        // A segment that ends in a censored point is drawn dashed: where it goes
        // is not known, only that it goes at least that far.
        line(
          (px(x0), py(y0)), (px(x1), py(y1)),
          stroke: (
            paint: s.colour,
            thickness: 1.1pt,
            dash: if c1 or family-dash { "dashed" } else { none },
          ),
        )
      }
      for (x, y, censored) in pts {
        if censored {
          circle((px(x), py(y)), radius: 0.09, stroke: 1pt + s.colour, fill: white)
        } else {
          circle((px(x), py(y)), radius: 0.075, stroke: none, fill: s.colour)
        }
      }
    }

    if legend {
      // Two series fit across the width; four do not, so the legend wraps into
      // rows of at most two and grows upwards from the plot.
      let cols = if series.len() > 2 { 2 } else { calc.max(series.len(), 1) }
      let rows = calc.ceil(series.len() / cols)
      let step = width / cols
      for (i, s) in series.enumerate() {
        let y = height + 0.45 + 0.4 * (rows - 1 - calc.floor(i / cols))
        let x = calc.rem(i, cols) * step
        line(
          (x, y), (x + 0.5, y),
          stroke: (
            paint: s.colour,
            thickness: 1.1pt,
            dash: if s.at("dash", default: false) { "dashed" } else { none },
          ),
        )
        content((x + 0.65, y), text(size: 7.5pt, s.name), anchor: "west")
      }
    }
  })
}
