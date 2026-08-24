#import "../macros.typ": *
#import "@preview/cetz:0.4.2"

/// Anatomy of a location type, @sec:impl-heap's `&[g] T @ p`, drawn against the
/// concrete instance `&[f] Int @ 1/1` rather than the schematic one — three
/// components in one sentence each is exactly the shape prose handles worst,
/// and the concrete type doubles as the field example @sec:impl-fields opens
/// with.
#let location-anatomy = {
  set par(justify: false)
  set text(hyphenate: false)

  let base = rgb("#0f766e")
  let hot = rgb("#b45309")
  let ink = rgb("#334155")

  let mono(s, size: 1.0em, fill: ink) = text(size: size, font: "DejaVu Sans Mono", fill: fill, s)

  cetz.canvas({
    import cetz.draw: *

    // Invisible bounding rect, purely to give the canvas breathing room —
    // without it cetz crops tight to the ink and the figure reads cramped
    // against its caption.
    rect((-2.9, -2.3), (6.6, 0.55), stroke: none, fill: none)

    // The four tokens of `&[f] Int @ 1/1`, laid out left to right at y = 0.
    let y-code = 0.0
    let toks = (
      (x: 0.0, w: 0.9, s: "&[f]", hue: base),
      (x: 1.3, w: 0.75, s: "Int", hue: base),
      (x: 2.4, w: 0.3, s: "@", hue: ink),
      (x: 3.0, w: 0.75, s: "1/1", hue: base),
    )
    for t in toks {
      content((t.x + t.w / 2, y-code), mono(t.s, size: 1em, fill: t.hue.darken(10%)))
    }

    // Three callouts, all below the code, all fanning down from their token
    // to a slot spread wide enough that no two labels ever touch — an angled
    // leader line, museum-placard style, rather than three vertical drops
    // crowding the same width as the tokens above them.
    let y-slot = -1.35
    let callout(tok, slot-x, name) = {
      let tx = tok.x + tok.w / 2
      line(
        (tx, y-code - 0.3),
        (slot-x, y-slot + 0.2),
        stroke: 0.9pt + hot,
        mark: (end: ">", scale: 0.4, fill: hot),
      )
      content(
        (slot-x, y-slot),
        anchor: "north",
        block(
          width: 2.5cm,
          align(center, std.stack(
            dir: ttb,
            spacing: 0.16em,
            text(size: 0.9em, weight: "bold", fill: hot.darken(15%), name),
          )),
        ),
      )
    }

    callout(toks.at(0), -1.3, [group])
    callout(toks.at(1), 1.7, [stored type])
    callout(
      toks.at(3),
      5.0,
      [permission bound],
    )
  })
}
