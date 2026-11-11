# The Talagrand book

A book version of the blueprint chapter `blueprint/src/chapters/spinglasses_talagrand.tex`
(the Sherrington–Kirkpatrick model at high temperature, following Talagrand's *Spin Glasses*,
Volume I), typeset with [Typst](https://typst.app) and the
[TypstVerso](https://github.com/Shreyas4991/TypstVerso) Lean tooling.

It is published at <https://anhhuyalex.github.io/LML/talagrand/>: one HTML page per section
(with hoverable Lean code) and one PDF of the whole book (about 600 pages, 7 MB; it has no hover information).

## What the book shows

* Every statement carries **both numbers**: Talagrand's (`Lemma 1.6.3`, taken from the
  `\talsource` tag) and the blueprint's running number (`(Lemma 41)`). Cross-references use
  Talagrand's number; when several Lean statements share one book number, the running number
  is added (`1.6.3 [#41]`) so the right piece is identified.
* Below each statement, the **Lean signature** of every `\lean{...}` declaration, exactly as
  `#check` prints it, with hover information for the types and documentation.
* Proofs are the blueprint's informal proofs. Lean proofs are not included.

## How it works

```
blueprint/src/chapters/spinglasses_talagrand.tex      (the only source; edited by hand)
        │  book/talagrand/tex2typ  (LaTeX subset -> Typst; fails on anything it does not know)
        ▼
book/talagrand/generated/   s00.typ … s14.typ, book.typ, labels.json, lean-names.json   (not committed)
        │  book/typstverso/build.py  (SubVerso/Lean `#check` of every name, Typst export)
        ▼
home_page/talagrand/        s00.html … s14.html, spin-glasses-talagrand.pdf, index.html
```

Never edit `generated/`. Change the `.tex` (or the theme) and rebuild.

| Path | Purpose |
|---|---|
| `talagrand/tex2typ/` | the converter: `parser` (LaTeX → AST), `index` (numbering), `emit` (AST → Typst), `cli` |
| `talagrand/theme.typ` | boxes, references, page setup (all styling lives here) |
| `talagrand/overrides.toml` | manual corrections of Talagrand numbers |
| `talagrand/verify_signatures.py` | fails if a cited Lean name has no signature (renamed/private) |
| `talagrand/make_index.py` | the landing page |
| `talagrand/checks/` | tests (`check_*.py`; the repository ignores `test*` names) |
| `typstverso/` | vendored TypstVerso with small changes, see `typstverso/VENDORED.md` |
| `../scripts/build_talagrand_book.sh` | the whole pipeline |

## Building locally

Needs `typst` ≥ 0.15 and, for the full build, the Lean project built (`lake build`).

```sh
scripts/build_talagrand_book.sh                 # full build into home_page/talagrand
scripts/build_talagrand_book.sh --check         # convert + compile only, no Lean (seconds)
BOOK_REFRESH=1 scripts/build_talagrand_book.sh  # extract the Lean signatures again
python3 -m unittest discover -s book/talagrand/checks -p 'check_*.py'   # with PYTHONPATH=book/talagrand
```

The first full build asks Lean to `#check` about 1 600 declarations in one process (a few
minutes) and stores the results in `book/typstverso/typst/lean.json` (about 25 MB, not
committed). Later builds reuse it. The 15 sections are typeset in parallel (`BOOK_JOBS`, default
all cores); on a 44-core machine the whole script takes about 20 minutes with a cold cache. The cache is keyed on the toolchain and dependency pins, not
on the Lean sources: after changing Lean code, rebuild the oleans and run with `BOOK_REFRESH=1`
(the build warns when sources are newer than the cache). CI keys its cache on the sources.

## Adding or changing content

* New LaTeX constructs: the converter stops with `file:line: unsupported command \foo`. Add it to
  `parser.py` (and a test in `checks/`); do not work around it in the `.tex` unless it is wrong.
* A wrong Talagrand number (a tag citing several statements): add the label to
  `talagrand/overrides.toml`.
* Styling: `talagrand/theme.typ`. Namespaces opened when Lean prints a statement: `lean-opens`.
