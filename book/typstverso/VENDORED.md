# Vendored TypstVerso

Source: <https://github.com/Shreyas4991/TypstVerso> at commit
`e00a419e35ac2fa4ebec5c6bbdc22b74480642e0` (Apache-2.0, see `LICENSE.txt`).
Only what the Talagrand book needs is copied: `build.py`, `ExportLean.lean`, `typst/lean.typ`,
`templates/html/{book.html,reader.js,tooltips.js,tooltips.css}`. The sample documents, the other
templates, the demo Lean project and the SubVerso patch are **not** used.

`packages/preview/mitex/0.2.7/` is the Typst package [mitex](https://typst.app/universe/package/mitex)
(Apache-2.0), vendored so that builds work offline. `scripts/build_talagrand_book.sh` points
`TYPST_PACKAGE_PATH` at it.

## Why not the stock workflow

TypstVerso expects its own Lean project and quotes whole declarations, which needs a patched
SubVerso. LML already builds its Lean code, and the book shows only statements. So the book asks
Lean for `#check <name>` (through `ExportLean.lean --commands`, which is stock) in the already
built LML environment. This needs no patch and does not touch LML's SubVerso, which verso uses.

## Changes (all marked `LML:` in the files)

`build.py`
* `--prebuilt`: do not run `lake update`/`lake build` or patch SubVerso; the project is built.
  The cache fingerprint then covers the toolchain/dependency pins (by content) and `ExportLean.lean`,
  not `build.py` or the Lean sources (see `CACHE_FORMAT`); a warning reports stale sources.
* `--export-script`: `ExportLean.lean` lives next to `build.py`, not in the Lean project.
* Several entry files in one run: all requests are discovered first, so Lean runs once.
* `lean.json` is compact: shared tooltip table (`compact_cache`/`expand_cache`), raw `fragments`
  dropped (25 MB instead of 160 MB).
* HTML export also collects `book-link` / `book-anchor` metadata (cross-references and their targets).
* `--light-pdf`: no Lean hover annotations, no hover boxes (`lean-plain` input) and no accessibility
  tags (`--no-pdf-tags`). A whole book has over 100 000 hover regions; the full PDF was 103 MB
  and is 7 MB this way.
* `--jobs N`: export entry files in parallel (they are independent Typst runs).

`typst/lean.typ`
* `lean-plain` input (hover boxes off), `lean-command(source: false)`, and `lean-signature(name, opens:, width:)` (a `#check` with
  `format.width` and `open … in`).
* `lean-tooltip(part)` resolves the shared tooltip table.

`templates/html/`
* `tooltips.js`/`tooltips.css`: `<a class="book-link">` overlays; `reader.js`: anchor targets.

## Updating

Copy the new upstream files over, re-apply the changes above (search for `LML:`), run
`python3 -m unittest discover -s book/talagrand/checks -p 'check_*.py'` and a full build.
`lml-changes.patch` is the exact difference to the pinned upstream commit (it applies with
`patch -p1` to a checkout of that commit).
