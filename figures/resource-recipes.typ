#import "../macros.typ": *
#import "@preview/cetz:0.4.2"

/// The record the linked-list resource leaves behind, drawn as three slots
/// whose recipes name the only two things a recipe may name: the resource's
/// argument and the members of its snapshot.
///
/// An earlier version left a hole in each recipe and ran an arrow to the source
/// that filled it. The supervisor's annotation on the §4.3 excerpt was that the
/// arrows were confusing and that a recipe naming two sources would need two
/// arrows into one line, so the holes are now written as the names themselves
/// (`e0`, `s1`) and the arrows are gone. The correspondence is read off the
/// text, which is also what the prose says.
///
/// The canvas was ~14.6 units wide and overflowed the text block. The two
/// columns are now stacked closer and the recipe column is narrower.
#let resource-recipes = {
  set par(justify: false)
  set text(hyphenate: false)

  let src = rgb("#0f766e") // what a recipe may draw on
  let ink = rgb("#334155")

  let mono(s, size: 0.7em, fill: ink) = text(
    size: size, font: "DejaVu Sans Mono", fill: fill, s,
  )
  let lbl(s, fill: ink) = text(size: 0.68em, weight: "bold", fill: fill, s)
  // A name a recipe draws on, tinted so the eye finds it inside a recipe.
  let name(s) = mono(s, fill: src.darken(15%))

  cetz.canvas({
    import cetz.draw: *

    // Breathing room. cetz crops to the ink, which reads cramped against a
    // caption.
    rect((-0.3, -4.2), (11.6, 1.1), stroke: none, fill: none)

    // ------------------------------------------------------------------
    // Left column: what a recipe may name. The argument on top, the
    // snapshot's three members below it. No types here: the adt on the
    // page before already gives them, and repeating them made the third
    // box wider than the column.
    // ------------------------------------------------------------------
    let x-src = 0.0
    let w-src = 1.5

    let source(y, n) = {
      rect(
        (x-src, y - 0.3), (x-src + w-src, y + 0.3),
        stroke: 0.8pt + src, fill: src.lighten(93%), radius: 2pt,
      )
      content((x-src + w-src / 2, y), name(n))
    }

    content((x-src, 0.82), anchor: "west", lbl("Argument", fill: src.darken(15%)))
    source(0.0, "e0")

    content((x-src, -1.15), anchor: "west", lbl("Snapshot", fill: src.darken(15%)))
    content((x-src, -1.55), anchor: "west", lbl("members", fill: src.darken(15%)))
    source(-2.1, "s0")
    source(-2.9, "s1")
    source(-3.7, "s2")

    // ------------------------------------------------------------------
    // Right column: one row per slot, address recipe then permission
    // recipe. Each recipe names its source outright, so no arrow is
    // needed to say where a term came from.
    // ------------------------------------------------------------------
    let x-slot = 2.3
    let w-slot = 9.2
    let x-perm = x-slot + 4.6

    let slot(y, n, addr, perm) = {
      rect(
        (x-slot, y - 0.4), (x-slot + w-slot, y + 0.4),
        stroke: 0.8pt + ink.lighten(45%), fill: luma(98%), radius: 2pt,
      )
      content((x-slot + 0.22, y), anchor: "west", lbl("slot " + n))
      content((x-slot + 1.0, y), anchor: "west", addr)
      line(
        (x-perm - 0.25, y - 0.4), (x-perm - 0.25, y + 0.4),
        stroke: 0.5pt + ink.lighten(65%),
      )
      content((x-perm, y), anchor: "west", perm)
    }

    content((x-slot + 1.0, 0.82), anchor: "west", lbl("Address recipe"))
    content((x-perm, 0.82), anchor: "west", lbl("Permission recipe"))

    slot(0.0, "0", { mono("val("); name("e0"); mono(")") }, mono("1/1"))
    slot(-1.15, "1", { mono("next("); name("e0"); mono(")") }, mono("1/1"))
    slot(-2.3, "2", { mono("LinkedList@loc("); name("s1"); mono(")") }, {
      name("s1"); mono(" != null ? 1/1 : 0/1")
    })
  })
}
