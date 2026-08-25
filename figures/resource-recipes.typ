#import "../macros.typ": *
#import "@preview/cetz:0.4.2"

/// The record the linked-list resource `Node` leaves behind, drawn as three
/// slots whose recipes reach back into the only two things a recipe may name:
/// the resource's argument and the members of its snapshot.
///
/// The table this replaced put the recipes in a column and left the reader to
/// work out where a hole was filled from. The point of the subsection is that
/// slot 2's receiver, written `this.next` in the source, is answered by a
/// snapshot member rather than by a heap, and an arrow says that where a column
/// of terms did not.
#let resource-recipes = {
  set par(justify: false)
  set text(hyphenate: false)

  let src = rgb("#0f766e")   // what a recipe may draw on
  let hot = rgb("#b45309")   // the arrows, and the holes they fill
  let ink = rgb("#334155")

  let mono(s, size: 0.88em, fill: ink) = text(
    size: size, font: "DejaVu Sans Mono", fill: fill, s,
  )
  let lbl(s, fill: ink) = text(size: 0.7em, weight: "bold", fill: fill, s)
  let hole = mono(sym.circle.stroked.small, fill: hot)

  cetz.canvas({
    import cetz.draw: *

    // Breathing room. cetz crops to the ink, which reads cramped against a
    // caption.
    rect((-0.3, -4.3), (14.7, 1.1), stroke: none, fill: none)

    // ------------------------------------------------------------------
    // Left column: the two sources. The argument on top, the snapshot's
    // three members below it.
    // ------------------------------------------------------------------
    let x-src = 0.0
    let w-src = 3.9

    let source(y, name, ty) = {
      rect(
        (x-src, y - 0.32), (x-src + w-src, y + 0.32),
        stroke: 0.8pt + src, fill: src.lighten(93%), radius: 2pt,
      )
      content((x-src + 0.3, y), anchor: "west", mono(name, fill: src.darken(15%)))
      content((x-src + w-src - 0.3, y), anchor: "east", text(
        size: 0.62em, fill: ink.lighten(20%), ty,
      ))
    }

    content((x-src, 0.82), anchor: "west", lbl("Argument", fill: src.darken(15%)))
    source(0.0, "e0", "Ref")

    content((x-src, -1.18), anchor: "west", lbl("Snapshot members", fill: src.darken(15%)))
    source(-2.0, "s0", "Option[Int]")
    source(-2.8, "s1", "Option[Ref]")
    source(-3.6, "s2", "Option[Node@snap]")

    // ------------------------------------------------------------------
    // Right column: one row per slot, address recipe then permission
    // recipe. The hole a recipe leaves is drawn in the arrow colour, so
    // the eye pairs it with the arrow that fills it.
    // ------------------------------------------------------------------
    let x-slot = 6.3
    let w-slot = 8.3
    let x-perm = x-slot + 4.05

    let slot(y, n, addr-pre, addr-post, perm) = {
      rect(
        (x-slot, y - 0.4), (x-slot + w-slot, y + 0.4),
        stroke: 0.8pt + ink.lighten(45%), fill: luma(98%), radius: 2pt,
      )
      content((x-slot + 0.28, y), anchor: "west", lbl("slot " + n))
      content((x-slot + 1.25, y), anchor: "west", {
        mono(addr-pre); hole; mono(addr-post)
      })
      line((x-perm - 0.3, y - 0.4), (x-perm - 0.3, y + 0.4), stroke: 0.5pt + ink.lighten(65%))
      content((x-perm, y), anchor: "west", perm)
    }

    content((x-slot + 1.25, 0.82), anchor: "west", lbl("Address recipe"))
    content((x-perm, 0.82), anchor: "west", lbl("Permission recipe"))

    slot(0.0, "0", "val(", ")", mono("1/1", size: 0.82em))
    slot(-1.15, "1", "next(", ")", mono("1/1", size: 0.82em))
    slot(-2.3, "2", "Node@loc(", ")", {
      hole; mono(" != null ? 1/1 : 0/1", size: 0.82em)
    })

    // ------------------------------------------------------------------
    // The arrows. Slots 0 and 1 reach the argument. Slot 2 reaches the
    // snapshot member the slot before it contributed, and that arrow is
    // the figure.
    // ------------------------------------------------------------------
    let feed(from-y, to-y, bend) = line(
      (x-src + w-src + 0.15, from-y),
      ((x-src + w-src + x-slot) / 2, bend),
      (x-slot - 0.15, to-y),
      stroke: 0.9pt + hot,
      mark: (end: ">", scale: 0.4, fill: hot),
    )

    feed(0.0, 0.0, 0.0)
    feed(0.0, -1.15, -0.6)
    feed(-2.8, -2.3, -2.6)
  })
}
