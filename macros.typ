#import "@preview/codly:1.3.0": codly, codly-init, local as codly-local, no-codly

// ---------------------------------------------------------------------------
// Code listings
//
// Three languages appear in this thesis and each gets its own visual identity,
// so a reader can tell at a glance which level of the pipeline a listing is at:
//
//   rust   — the source program a Prusti user writes
//   viper  — the Silver program Prusti emits (and our verifier consumes)
//   vmir   — the intermediate representation our verifier lowers Silver into
//
// Three languages, one presentation: only hue and the corner tag differ.
//
// `rust` is highlighted by Typst's built-in syntect grammars; `viper` and
// `vmir` are not, so we ship grammars for them in `syntaxes/`.
//
// A fourth tag, `pvmir`, is not a fourth language: it is VMIR written
// schematically, for the places where the real encoding is too verbose to make
// a point with. It shares VMIR's hue and grammar (`pvmir` is an extension of
// the VMIR grammar) and differs only in the corner tag, so a reader can always
// tell a listing that could be fed to the verifier from one that could not.
// ---------------------------------------------------------------------------

#let lang-colors = (
  rust: rgb("#b7410e"), // rust orange
  viper: rgb("#5b57c7"), // indigo
  vmir: rgb("#0f766e"), // teal
  pvmir: rgb("#0f766e"),
)

#let lang-names = (
  rust: [Rust],
  viper: [Viper],
  vmir: [VMIR],
  pvmir: [pseudo-VMIR],
)

// The per-language dictionary codly uses for the little language tag it draws
// in the top-right corner of a listing.
#let codly-langs = (
  rust: (name: lang-names.rust, color: lang-colors.rust),
  viper: (name: lang-names.viper, color: lang-colors.viper),
  vmir: (name: lang-names.vmir, color: lang-colors.vmir),
  pvmir: (name: lang-names.pvmir, color: lang-colors.pvmir),
)

// All three are languages in the same pipeline, so they are presented
// identically: a tint of the language's accent colour, alternating rows a shade
// darker (codly's `zebra-fill`) so long listings stay scannable, a solid accent
// rule down the left, and line numbers so prose can point at a line. Only the
// hue and the corner tag distinguish them.
//
// `tint-base` and `tint-zebra` say how far the accent is lightened to make the
// two row fills. Lower numbers mean a more saturated tint; these are the knobs
// to turn if listings read as too loud or too washed out in print.
#let tint-base = 98%
#let tint-zebra = 94%

#let _lang-style(lang) = {
  let accent = lang-colors.at(lang)
  (
    fill: accent.lighten(tint-base),
    zebra-fill: accent.lighten(tint-zebra),
    rule: 2pt + accent,
  )
}

// The per-language presentation, applied by a `show raw.where(lang: ..)` rule so
// that a plain ```viper block in a chapter is styled exactly like one wrapped in
// `#viper[..]`. Typst does not re-apply a show rule to its own output, so
// re-emitting `it` here does not recurse.
// Set by `#no-numbers[..]`. It has to be a state rather than a `codly-local`
// wrapper: any `codly-local` enclosing a listing installs its own
// `show raw.where(block: true)` rule, which is nested deeper than the
// per-language rules in `code-setup` and would strip the language styling.
#let _numbers-off = state("thesis-numbers-off", false)

// Set while rendering a `#lowering` table cell, where the raw should be
// syntax-highlighted but carry none of the listing chrome (codly's numbering,
// tag and zebra) — the table supplies its own.
#let _bare-raw = state("thesis-bare-raw", false)

#let _style-raw(lang, it) = {
  let style = _lang-style(lang)
  // A single-line listing has nothing to number: the "1" is pure noise, and
  // dropping it lets a one-liner sit closer to the surrounding prose.
  let one-line = it.text.trim().split("\n").len() <= 1

  context {
    // `no-codly` is needed as well as returning `it` unchanged: codly-init's
    // own `show raw.where(block: true)` rule is separate from ours and would
    // still draw the numbering, tag and zebra.
    if _bare-raw.get() { return no-codly(it) }
    let numbered = not one-line and not _numbers-off.get()
    let styled = codly-local(
      fill: style.fill,
      zebra-fill: style.zebra-fill,
      stroke: none,
      nested: true,
      ..(if numbered { (:) } else { (number-format: none) }),
      it,
    )

    // codly's own `stroke` frames the whole table; we want a single accent rule
    // down the left edge instead, so it goes on a wrapper block.
    block(
      stroke: (left: style.rule),
      inset: (left: 0.6em),
      breakable: true,
      width: 100%,
      styled,
    )
  }
}

/// Document-wide setup for code listings. Apply once in `main.typ`:
///   #show: code-setup
#let code-setup(doc) = {
  set raw(
    syntaxes: ("syntaxes/viper.sublime-syntax", "syntaxes/vmir.sublime-syntax"),
    theme: "syntaxes/thesis-code.tmTheme",
  )

  show: codly-init.with()
  codly(
    languages: codly-langs,
    display-name: true,
    display-icon: false,
    // Neutral defaults for a bare ``` block in a language we have no accent
    // for; the show rules below tint the three languages that matter.
    fill: luma(97%),
    zebra-fill: luma(93%),
    radius: 2pt,
    inset: 0.28em,
    number-format: n => text(size: 0.75em, fill: luma(60%))[#n],
  )

  show raw.where(lang: "rust", block: true): it => _style-raw("rust", it)
  show raw.where(lang: "viper", block: true): it => _style-raw("viper", it)
  show raw.where(lang: "vmir", block: true): it => _style-raw("vmir", it)
  show raw.where(lang: "pvmir", block: true): it => _style-raw("pvmir", it)

  // Captioned listings use `kind: "listing"`, not `kind: raw`. `codly-init`
  // installs a `show figure.where(kind: raw)` rule that, for a *labelled*
  // figure, re-shows the raw so `@lst:foo` can resolve to it — and that inner
  // rule wins over the three above, stripping the language styling. A custom
  // kind sidesteps it entirely and gives listings their own counter.
  show figure.where(kind: "listing"): set block(breakable: true)
  show figure.where(kind: "listing"): set figure.caption(position: bottom)

  doc
}

// Recover the plain source text of `body`, which may be a string, a raw block
// (```lang ... ```), or ordinary markup content such as `[&mut Account]`.
#let _plain(body) = {
  if type(body) == str { return body }
  let f = body.func()
  if f == raw or f == text { return body.text }
  if f == [].func() { return body.children.map(_plain).join("") }
  if body.has("body") { return _plain(body.body) }
  if f == [ ].func() { return " " }
  panic("unsupported code body: " + repr(body))
}

/// Suppress line numbers for the listings inside. Single-line listings drop
/// them automatically, so this is for the multi-line cases where the numbers
/// earn nothing — a fragment quoted mid-sentence, say. Works on bare ```lang
/// blocks too:
///   #no-numbers[```viper
///   ...
///   ```]
#let no-numbers(body) = {
  _numbers-off.update(true)
  body
  _numbers-off.update(false)
}

// Shared implementation behind `#rust`, `#viper` and `#vmir`. All of the visual
// styling is done by the show rules in `code-setup`; these wrappers exist only
// to add a caption, a `Listing` number and a cross-reference label. A plain
// ```lang block is styled identically — it just cannot be referenced.
#let _listing(lang, body, caption: none, label: none, numbers: auto) = {
  // Accept either a bare ```lang ...``` block or a language-less raw block,
  // and re-emit it tagged with `lang` so the right grammar is used.
  let code = raw(_plain(body), lang: lang, block: true)
  // `auto` leaves it to `_style-raw`, which numbers everything but one-liners.
  if numbers == false { code = no-numbers(code) }

  if caption == none { return code }

  let fig = figure(code, caption: caption, kind: "listing", supplement: [Listing])
  if label == none { fig } else { [#fig #std.label(label)] }
}

/// A Rust listing — the source program a Prusti user writes.
///   #rust(caption: [...], label: "lst:foo")[```rust ... ```]
#let rust(body, caption: none, label: none, numbers: auto) = _listing(
  "rust",
  body,
  caption: caption,
  label: label,
  numbers: numbers,
)

/// A Viper listing — Prusti's encoding, and our verifier's input.
#let viper(body, caption: none, label: none, numbers: auto) = _listing(
  "viper",
  body,
  caption: caption,
  label: label,
  numbers: numbers,
)

/// A VMIR listing — our verifier's intermediate representation.
#let vmir(body, caption: none, label: none, numbers: auto) = _listing(
  "vmir",
  body,
  caption: caption,
  label: label,
  numbers: numbers,
)

/// A pseudo-VMIR listing — VMIR written schematically, where the real encoding
/// would bury the point being made. Used only where the difference is stated.
#let pvmir(body, caption: none, label: none, numbers: auto) = _listing(
  "pvmir",
  body,
  caption: caption,
  label: label,
  numbers: numbers,
)

// ---------------------------------------------------------------------------
// Lowering tables
//
// Showing which VMIR instructions a Viper statement lowers to. Each side is
// written as an ordinary listing and split into chunks by a separator line;
// chunk `i` on the left is placed beside chunk `i` on the right, so the two
// columns stay in step no matter how many instructions a statement produces.
// ---------------------------------------------------------------------------

#let lowering-separator = "//@"

// Split a listing's source on separator lines, returning one source string per
// chunk with surrounding blank lines trimmed.
#let _chunks(body) = {
  let out = ((),)
  for line in _plain(body).split("\n") {
    if line.trim() == lowering-separator {
      out.push(())
    } else {
      out.last().push(line)
    }
  }
  out.map(c => c.join("\n").trim("\n"))
}

// One cell of code. The `_bare-raw` flag that strips the listing chrome is set
// around the whole table rather than per cell — a `state` update placed inside
// a table cell is not reliably visible to a `context` in that same cell.
#let _cell(lang, src) = raw(src, lang: lang, block: true)

/// A side-by-side lowering table: a Viper listing and the VMIR it lowers to,
/// aligned chunk by chunk. Separate the chunks with a `//@` line in *both*
/// listings; the two must have the same number of chunks.
///
///   #lowering(caption: [...], label: "lst:fields")[```viper
///   x.f := 42
///   //@
///   assert x.f > 0
///   ```][```vmir
///   h1 := h0 assign(e1, 42)
///   //@
///   e2: Int := *[h1] e1
///   assert e2 > 0
///   ```]
/// `target-lang` is `"vmir"` by default and `"pvmir"` where the right-hand side
/// is written schematically (see the note on pseudo-VMIR in @sec:implementation).
#let lowering(source, target, caption: none, label: none, columns: (1fr, 1.15fr), target-lang: "vmir") = {
  let src-chunks = _chunks(source)
  let tgt-chunks = _chunks(target)
  if src-chunks.len() != tgt-chunks.len() {
    panic(
      "lowering: "
        + str(src-chunks.len())
        + " chunk(s) on the left but "
        + str(tgt-chunks.len())
        + " on the right — the two sides must be split into the same number of "
        + "chunks with `"
        + lowering-separator
        + "` lines",
    )
  }

  let langs = ("viper", target-lang)
  let tints = langs.map(l => _lang-style(l).fill)
  let accents = langs.map(l => lang-colors.at(l))

  let head(i) = text(
    size: 0.75em,
    weight: "bold",
    fill: accents.at(i).darken(15%),
    lang-names.at(langs.at(i)),
  )

  let body = {
    // The flag wraps the whole table: a `state` update placed inside a table
    // cell is not reliably visible to a `context` in that same cell.
    _bare-raw.update(true)
    table(
      columns: columns,
      align: left + top,
      inset: (x: 0.6em, y: 0.45em),
      fill: (x, y) => if y == 0 { none } else { tints.at(x) },
      // Hairlines between chunks only, plus each column's accent rule down the
      // left and a rule under the header.
      stroke: (x, y) => (
        left: 2pt + accents.at(x),
        top: if y == 1 { 1pt + accents.at(x) } else if y > 1 { 0.5pt + luma(80%) } else { none },
        rest: none,
      ),
      table.header(head(0), head(1)),
      ..src-chunks
        .zip(tgt-chunks)
        .map(((s, t)) => (_cell("viper", s), _cell("vmir", t)))
        .flatten()
    )
    _bare-raw.update(false)
  }

  if caption == none { return body }
  let fig = figure(body, caption: caption, kind: "listing", supplement: [Listing])
  if label == none { fig } else { [#fig #std.label(label)] }
}

// ---------------------------------------------------------------------------
// Drafting notes
//
// `#todo[..]` and `#note[..]` render as callouts that are impossible to mistake
// for finished prose. Set `show-notes` to `false` to drop every one of them
// from the output — do that before handing a draft to anyone.
// ---------------------------------------------------------------------------

// Compile with `--input no-notes=1` to drop every callout without editing this
// line, e.g. when producing an excerpt to hand to someone.
#let show-notes = "no-notes" not in sys.inputs

// True when building `excerpt.typ` (`--input excerpt=1`). Guard passages that
// are deliberately left out of a hand-out with `#if not excerpt-mode [..]`.
#let excerpt-mode = "excerpt" in sys.inputs

#let _callout(tag, accent, body, keep: false) = {
  if not show-notes and not keep { return }
  block(
    width: 100%,
    fill: accent.lighten(90%),
    stroke: (left: 2.5pt + accent),
    inset: (x: 0.8em, y: 0.6em),
    radius: 2pt,
    breakable: true,
    {
      set text(size: 0.92em)
      block(
        below: 0.5em,
        text(
          size: 0.72em,
          weight: "bold",
          tracking: 0.1em,
          fill: accent.darken(20%),
          upper(tag),
        ),
      )
      // A `#para` inside a planning note sketches structure rather than being
      // it, so it must not reach the PDF outline.
      set heading(bookmarked: false)
      body
    },
  )
}

/// Work still to be done. Loud on purpose.
///
/// `keep: true` survives `--input no-notes=1`, for the placeholders a reader of
/// a stripped-down draft still has to see — a figure that is described but not
/// yet drawn, say, where dropping the note would leave the prose referring to
/// nothing.
#let todo(body, keep: false) = _callout("todo", rgb("#b45309"), body, keep: keep)

/// An observation to keep in mind while writing, not itself a task.
#let note(body) = _callout("note", rgb("#475569"), body)

/// Prose that is written but not settled: the mechanism it describes may still
/// change, so it is fenced off rather than left to read as finished text.
#let wip(body) = _callout("wip", rgb("#7c3aed"), body)

/// A short inline marker, for a gap mid-sentence.
#let tbd(body) = if show-notes {
  box(
    fill: rgb("#b45309").lighten(85%),
    inset: (x: 0.3em),
    outset: (y: 0.28em),
    radius: 2pt,
    text(size: 0.85em, weight: "bold", fill: rgb("#b45309").darken(20%), body),
  )
}

/// A run-in subsection heading, for structure below `==` (i.e. below `4.1`).
/// Unnumbered and absent from the outline, so section numbering never goes
/// three levels deep:
///
///   #para[Path conditions] Every chunk carries the cube of branch literals ...
/// The hidden level-3 heading is what puts the paragraph in a PDF reader's
/// navigation pane. It is `place`d so that it occupies no space at all and
/// disturbs neither the paragraph spacing above nor the run-in below; a
/// zero-height block is not equivalent, since its own spacing then replaces the
/// paragraph gap. `outlined: false` keeps section numbering and the table of
/// contents two levels deep, and bookmarking is left to the
/// `set heading(bookmarked: true)` in `main.typ`, so that a callout can switch it
/// off for its own body with a nested `set` rule.
#let para(title) = {
  place(hide(heading(level: 3, numbering: none, outlined: false, title)))
  text(weight: "bold")[#title.]
  h(0.5em)
}

/// Cross-reference a labelled `#para`. Run-in headings are unnumbered, so
/// there is nothing for `@label` to print — and `#para` returns a plain
/// sequence, which Typst refuses to reference at all. Link by name instead:
///
///   #para[Partitioning] <sec:heap-partitioning> The symbolic heap is ...
///   ... is explained in #pararef(<sec:heap-partitioning>, [Partitioning]).
#let pararef(target, title) = link(target, emph(title))

// Inline code fragments, coloured by language, for use in prose:
//   the #vi[fold] statement, the #ru[`&mut`] parameter
//
// The body is ordinary markup, so a fragment containing characters Typst treats
// specially (`*`, `_`, `#`, an unbalanced `[`) must be written as inline raw:
// `#vm[`*[h0] e1`]`, not `#vm[*[h0] e1]`. Both forms are highlighted the same.
//
// Tinted a little more strongly than a block's base fill — a few characters need
// more contrast than a whole listing does to read as code.
#let _inline(lang, body) = {
  let src = _plain(body)
  box(
    fill: lang-colors.at(lang).lighten(tint-zebra),
    inset: (x: 0.25em),
    outset: (y: 0.25em),
    radius: 1.5pt,
    raw(src, lang: lang, block: false),
  )
}

/// A ternary in math mode: `$ternary(p > 0, p, 0)$`.
///
/// Typst classes `?` as punctuation, so writing the ternary directly sets it
/// flush against the condition (`p > 0? p : 0`). Re-classing it as a binary
/// operator restores the spacing; `:` already reads as a relation.
#let ternary(cond, then, els) = $cond class("binary", ?) then : els$

#let ru(body) = _inline("rust", body)
#let vi(body) = _inline("viper", body)
#let vm(body) = _inline("vmir", body)
