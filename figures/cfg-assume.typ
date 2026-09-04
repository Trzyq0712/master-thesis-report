#import "../macros.typ": *
#import "@preview/cetz:0.4.2"

/// The VMIR of @lst:cfg-assume, drawn as the block graph it is rather than set
/// as a listing. A linear listing has to serialise a graph, which costs a page
/// and hides the one thing the section argues about: `bb3` is reached from two
/// predecessors, and its join phase runs before its body.
///
/// Each box carries the block's header — its number, its path condition, and
/// its predecessors — then its phases, separated by a hairline. The join phase of
/// `bb3` is the amber one: it holds the ternary that picks `v`, which is the
/// figure's reason to exist.
#let cfg-assume = {
  set par(justify: false)
  set text(hyphenate: false)

  let base = rgb("#0f766e")
  let hot = rgb("#b45309")
  let ink = rgb("#334155")

  let mono(s, size: 0.72em, fill: ink) = text(
    size: size,
    font: "DejaVu Sans Mono",
    fill: fill,
    s,
  )
  let phase(s, fill: ink) = text(
    size: 0.58em,
    style: "italic",
    fill: fill.lighten(30%),
    s,
  )

  // A block: the header, then one row per phase. A phase with no instructions
  // is still named, since an empty body is a fact about the block.
  let blk(hdr, phases, hue) = block(
    inset: (x: 0.5em, y: 0.42em),
    radius: 2.5pt,
    stroke: 0.6pt + hue.darken(5%),
    fill: hue.lighten(94%),
  )[
    #stack(
      dir: ttb,
      spacing: 0.34em,
      mono(hdr, size: 0.74em, fill: hue.darken(38%)),
      ..phases
        .map(((name, ls)) => stack(
          dir: ttb,
          spacing: 0.3em,
          line(length: 100%, stroke: 0.4pt + hue.lighten(55%)),
          phase(name, fill: hue.darken(10%)),
          ..ls.map(l => mono(l)),
        ))
        .flatten(),
    )
  ]

  cetz.canvas({
    import cetz.draw: *

    let box(pos, name, body) = content(
      pos,
      body,
      name: name,
      anchor: "north",
    )

    box((0, 0), "bb0", blk(
      "bb0 <>:",
      (
        ("join", ("e0: Bool := fresh   // b", "e1: Int  := fresh   // v")),
        ("body", ()),
      ),
      base,
    ))

    box((-2.6, -2.35), "bb1", blk(
      "bb1 <e0> from bb0:",
      (("body", ("e2: Int := 1   // v",)),),
      base,
    ))

    box((2.6, -2.35), "bb2", blk(
      "bb2 <!e0> from bb0:",
      (("body", ("e3: Int := 2   // v",)),),
      base,
    ))

    box((0, -4.5), "bb3", blk(
      "bb3 <> join e0 [bb1, bb2]:",
      (
        ("join", ("e4: Int := e0 ? e2 : e3   // v",)),
        ("body", (
          "e5: Int  := e0 ? 1 : 2",
          "e6: Bool := e4 == e5",
          "assert e6",
        )),
      ),
      hot,
    ),)

    let edge(a, b) = line(
      a,
      b,
      mark: (end: ">", scale: 0.45),
      stroke: 0.6pt + ink.lighten(25%),
    )
    edge("bb0.south-west", "bb1.north")
    edge("bb0.south-east", "bb2.north")
    edge("bb1.south", "bb3.north-west")
    edge("bb2.south", "bb3.north-east")
  })
}
