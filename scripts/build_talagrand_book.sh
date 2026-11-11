#!/usr/bin/env bash
# Build the Talagrand book: per-section HTML pages and a whole-book PDF.
#
#   scripts/build_talagrand_book.sh [OUTPUT_DIR]        full build (needs the built Lean project)
#   scripts/build_talagrand_book.sh --check [OUTPUT_DIR] only convert and compile without Lean data
#
# OUTPUT_DIR defaults to home_page/talagrand. Set BOOK_REFRESH=1 to extract the Lean signatures
# again (the results are cached in book/typstverso/typst/lean.json). BOOK_JOBS sets the number of
# sections typeset in parallel (default: all cores).
# Run it from anywhere; it needs `typst` (>= 0.15), python3 and, for the full build, `lake`.
set -euo pipefail

cd "$(dirname "$0")/.."
check_only=false
if [[ "${1:-}" == "--check" ]]; then
  check_only=true
  shift
fi
output="${1:-home_page/talagrand}"

tex=blueprint/src/chapters/spinglasses_talagrand.tex
book=book/talagrand
viewer=book/typstverso
pdf_name=spin-glasses-talagrand.pdf
# Typst downloads packages on first use; a vendored copy keeps the build offline and pinned.
export TYPST_PACKAGE_PATH="$PWD/$viewer/packages"

echo "== Converting $tex to Typst"
PYTHONPATH="$book" python3 -m tex2typ "$tex" --out "$book/generated" --overrides "$book/overrides.toml"

if $check_only; then
  echo "== Compiling without Lean results"
  typst compile --root book --input lean-discover=true "$book/generated/book.typ" "$book/generated/check.pdf"
  rm -f "$book/generated/check.pdf"
  exit 0
fi

# Sections are independent Typst runs; use the available cores (BOOK_JOBS overrides).
jobs="${BOOK_JOBS:-$(nproc 2>/dev/null || echo 2)}"

refresh=()
if [[ "${BOOK_REFRESH:-}" == "1" ]]; then refresh=(--refresh); fi

build() {  # build FORMAT ENTRY...
  local format="$1"; shift
  python3 "$viewer/build.py" "$@" --document "$book" --project . --module LeanMachineLearning \
    --prebuilt --library "$viewer/typst" --templates "$viewer/templates/html" --template book \
    --format "$format" --output "$book/build" --light-pdf --jobs "$jobs" ${refresh[@]+"${refresh[@]}"}
}

echo "== Building the HTML sections (extracts Lean signatures on the first run)"
sections=$(cd "$book" && ls generated/s??.typ)
build html $sections
echo "== Checking that every cited Lean declaration has a signature"
python3 "$book/verify_signatures.py" "$book/generated/lean-names.json" "$viewer/typst/lean.json"
echo "== Checking that every cross-reference reaches an anchor"
python3 "$book/verify_links.py" "$book/build"
echo "== Building the whole-book PDF"
build pdf generated/book.typ

echo "== Assembling $output"
mkdir -p "$output"
cp "$book"/build/s??.html "$output"/
cp "$book/build/book.pdf" "$output/$pdf_name"
python3 "$book/make_index.py" "$book/generated/sections.json" "$output" --pdf "$pdf_name"
echo "Done: $output/index.html"
