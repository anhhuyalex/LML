// Theme for the Talagrand book: boxes, references and page setup.
// The generated files (generated/) only call the functions defined here.

#import "@preview/mitex:0.2.7": mi, mitex
#import "../typstverso/typst/lean.typ": lean-signature

// ------------------------------------------------------------------ settings
#let body-font = "New Computer Modern"
#let mono-font = "DejaVu Sans Mono"
#let accent = rgb("245b96")
#let muted = rgb("626a64")
// Namespaces opened when Lean prints a statement: shorter names, scoped notation.
#let lean-opens = ("SpinGlasses", "MeasureTheory", "ProbabilityTheory")
#let blueprint-url = "https://anhhuyalex.github.io/LML/blueprint/"

// Which book section a per-section build renders; `none` while building the whole book.
#let current-part = state("book-part", none)

// ------------------------------------------------------------- small helpers
#let tt(body) = text(font: mono-font, size: 0.88em, body)

#let run-in(body) = [#strong(body)#h(0.5em)]

#let labeled-items(..items) = block(above: 0.8em, below: 0.8em)[
  #for (marker, body) in items.pos() {
    grid(columns: (2.2em, 1fr), column-gutter: 0.4em, strong(marker), body)
    v(0.3em)
  }
]

// SVG export drops Typst's own links, so the HTML reader gets a region to turn into a link.
#let html-link(body, href) = context {
  let size = measure(body)
  box[
    #metadata((kind: "book-link", href: href, width: size.width.pt(), height: size.height.pt()))
    #body
  ]
}

// A link target for the HTML reader (`id` is also the Typst label).
#let html-anchor(id) = metadata((kind: "book-anchor", id: id))

// A reference. `shown` is computed by the converter (Talagrand's number first).
#let rf(target, shown, section: none, external: false) = context {
  let here = current-part.get()
  if external {
    link(blueprint-url, html-link(shown, blueprint-url))
  } else if here == none or section == none {
    link(label(target), html-link(shown, "#" + target))
  } else {
    // A statement in another section of a per-section build lives on another page.
    let href = section + ".html#" + target
    link(href, html-link(shown, href))
  }
}

// -------------------------------------------------------------- boxes
#let box-color = (
  theorem: accent, proposition: accent, lemma: rgb("4a7c59"), corollary: rgb("4a7c59"),
  definition: rgb("8959a8"), remark: muted,
)

#let capitalize(word) = upper(word.first()) + word.slice(1)

// The Lean statements of a box, as `#check` prints them.
#let lean-panel(names) = block(width: 100%, above: 0.9em, breakable: true)[
  #set block(above: 0.45em, below: 0.45em)
  #text(size: 0.75em, weight: "bold", fill: muted, tracking: 0.08em)[LEAN]
  #v(-0.2em)
  #for name in names {
    lean-signature(name, opens: lean-opens, size: 0.78em)
  }
]

// Header text: Talagrand's own numbering first, the blueprint's running number second.
#let box-header(kind, serial, tal, title) = {
  if tal != none {
    strong[#tal.at(0) #tal.at(1)]
    h(0.4em)
    text(fill: muted, size: 0.85em)[(#capitalize(kind) #serial)]
  } else {
    strong[#capitalize(kind) #serial]
  }
  if title != none [ #h(0.3em);(#emph(title))]
}

// A theorem-like box. `names` are the Lean declarations shown below the statement.
#let thm(kind, serial, tal: none, title: none, label: none, source: none, names: (), body) = {
  let color = box-color.at(kind)
  let framed = block(width: 100%, breakable: true, above: 1.3em, below: 0.8em,
    inset: (left: 10pt, y: 4pt), stroke: (left: 2pt + color))[
    #box-header(kind, serial, tal, title)
    #if source != none {
      linebreak()
      text(size: 0.82em, fill: muted)[\[Talagrand, #source\]]
    }
    #parbreak()
    #body
    #if names.len() > 0 { lean-panel(names) }
  ]
  if label != none { html-anchor(label) }
  [#framed#if label != none { std.label(label) }]
}

#let proof(body) = block(width: 100%, breakable: true, above: 0.6em, below: 1.2em,
  inset: (left: 10pt))[
  #emph[Proof.] #body
  #align(right, text(fill: muted, sym.square.stroked))
]

// ------------------------------------------------------------ page setup
#let base-style(body) = {
  set page(paper: "iso-b5", margin: (x: 18mm, y: 20mm), numbering: "1")
  set text(font: body-font, size: 10pt, lang: "en")
  set par(justify: true)
  set heading(numbering: "1.1")
  show heading: it => {
    let id = it.at("label", default: none)
    if id != none { html-anchor(str(id)) }
    if it.level == 1 { pagebreak(weak: true); v(1em); it; v(0.6em) } else { it }
  }
  show link: set text(fill: accent)
  show raw: set text(font: mono-font)
  body
}

// One book section, built on its own: heading numbers continue from the previous sections.
#let book-section(part: 1, title: "", body) = {
  set document(title: title)
  show: base-style
  current-part.update(str(part))
  counter(heading).update(calc.max(part - 1, 0))
  body
}

// The whole book: cover, contents, all sections.
#let book(title: [], subtitle: [], body) = {
  set document(title: "Talagrand's SK theory (Lean blueprint book)")
  show: base-style
  page(numbering: none)[
    #align(center + horizon)[
      #text(size: 24pt, weight: "bold")[#title]
      #v(1cm)
      #text(size: 13pt)[#subtitle]
    ]
  ]
  outline(title: [Contents], depth: 2, indent: auto)
  body
}
