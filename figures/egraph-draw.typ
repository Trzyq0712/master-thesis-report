#import "@preview/cetz:0.4.2"
#import cetz.draw: bezier, content, line, rect

/// The drawing vocabulary shared by the thesis' e-graph pictures: solid boxes
/// are e-nodes, dashed boxes are the e-classes grouping them, and arrows run
/// from a node to the class of each of its arguments.
///
/// This file is a helper module rather than a figure. Every file that draws an
/// e-graph imports it, so the notation stays the same wherever it appears.

// One ink for every part of every e-graph picture. Colour encoded nothing a
// reader could use, so the figures say what changed in words instead.
#let ink = rgb("#0f766e")

#let nw = 1 // e-node width
#let nh = 0.6 // e-node height
#let clsp = 0.22 // padding between an e-class box and the nodes it holds

#let mono(s, size: 0.8em, fill: ink.darken(35%)) = text(
  size: size,
  font: "DejaVu Sans Mono",
  fill: fill,
  s,
)

/// A sort-tagged operator label. Listings write the tag inline (`*i`, `<r`),
/// which is what the verifier reads; a figure has the room to set it as the
/// subscript the term language uses.
#let op(sym, sort) = [#sym#sub[#sort]]

// One e-node: a filled, rounded box centred on `pos`.
#let node(pos, label, hue) = {
  rect(
    (pos.at(0) - nw / 2, pos.at(1) - nh / 2),
    (pos.at(0) + nw / 2, pos.at(1) + nh / 2),
    fill: hue.lighten(90%),
    stroke: 0.5pt + hue.darken(5%),
    radius: 1.5pt,
  )
  content(pos, mono(label, fill: hue.darken(35%)))
}

// The dashed box around a run of e-nodes, plus the handles naming it. A
// class that several names now share takes them as an array, drawn one per
// line so the handle stays clear of the arrows arriving at the box's top.
#let cls(x0, x1, y, hue, tag) = {
  let p = clsp
  rect(
    (x0 - nw / 2 - p, y - nh / 2 - p),
    (x1 + nw / 2 + p, y + nh / 2 + p),
    stroke: (paint: hue, thickness: 0.55pt, dash: "dashed"),
    radius: 3pt,
  )
  if tag != none {
    let names = if type(tag) == str { (tag,) } else { tag }
    content(
      (x0 - nw / 2 - p, y + nh / 2 + p + 0.04),
      anchor: "south-west",
      mono(
        {
          set par(leading: 0.25em)
          names.map(n => [#n]).join(linebreak())
        },
        size: 0.8em,
        fill: hue.darken(10%),
      ),
    )
  }
}

// A node-to-class edge, leaving the parent's bottom and arriving at the top
// of the child's class box. `dx` shifts the departure point, so a node with
// two arguments in the same class draws two arrows into it; `sag` bends the
// edge below the row between the two, clearing the boxes sitting there.
#let edge(from, to, hue: luma(55%), dx: 0.0, sag: none) = {
  let p0 = (from.at(0) + dx, from.at(1) - nh / 2)
  let p1 = (to.at(0), to.at(1) + nh / 2 + clsp)
  let s = 0.5pt + hue
  let m = (end: ">", scale: 0.6)
  if sag == none { line(p0, p1, mark: m, stroke: s) } else {
    bezier(p0, p1, sag, mark: m, stroke: s)
  }
}
