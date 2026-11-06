# Exposition statistics

The public page is https://anhhuyalex.github.io/LML/exposition/stats/.

If three different included declarations use A, A's count is three. Repeating A in
one declaration still counts once. Statements, proofs and definition bodies all
count; using B, which itself uses A, does not add a use of A. Counts concern LML
only and do not measure quality or use by other projects.

We include named public declarations written in LML source files and shown in
the exposition. This includes explicitly named instances. Private declarations,
unnamed instances, declarations with no source location, and generated companions
are excluded from both the counted declarations and their users. Referee already
looks through automatic helper code to recover the author's references. The
download records the included population and reasons for exclusions.

The calculation follows the distinct-user rule of M1 in
[lean-code-reuse](https://github.com/Vilin97/lean-code-reuse). Its population policy
differs, so counts should not be described as directly comparable to that report.

## Build and preview

Requires Python **3.10+** for extractor datasets (legacy examples also run on 3.9),
Node **18+** for histogram tests, and Chrome/Chromium for
browser tests. The normal GitHub runner already provides them. Set `CHROME` if
Chrome is not on PATH. Extractor datasets need the maintained `evidence-core`
reader (`pip install -r scripts/website_stats/requirements.txt`); the Referee
action also installs it. No online chart services are needed.

First obtain **the same build's** Referee dataset and rendered
site. In CI these are `steps.referee.outputs.dataset` and `.site`. Keep the site in
`home_page/exposition/`. The source checkout must match the collected data; source
links are pinned to that checkout's Git commit.

```bash
# Run from LML. This consumes existing outputs; it does not compile or extract Lean.
python3 scripts/build_stats.py --data /path/to/dataset \
  --repository https://github.com/anhhuyalex/LML
python3 scripts/check_stats.py --site home_page/exposition
python3 -m http.server 8080 --directory home_page
# Open http://localhost:8080/exposition/stats/
```

The output is ignored by Git. A repeat build updates the same page and inserts
exactly one Stats link after Sorries in each existing sidebar. An incompatible
Referee data format, partial-library input, missing source or documentation page,
or unexpected sidebar structure fails the build instead of publishing partial counts.

For the small example used on pull requests (no Lean build or Referee needed):

```bash
python3 scripts/check_stats.py
# Optional screenshots of the example at desktop and phone widths:
python3 scripts/check_stats.py --screenshots /tmp/lml-stats-preview
```

The tests check known reuse counts, exclude private/unnamed/generated declarations,
check compressed data and bad inputs, test histogram membership and totals,
and exercise bar choices, keyboard selection, search, pagination, shared links,
browser back navigation and documentation links at 1280px and 390px.

A separate GitHub job runs these checks from a fresh checkout before the Lean
build starts. It catches files present only on a developer's machine. In
particular, the example data builder is `example.py`: `fixture.py` would match
this repository's `fix*` ignore rule and could be omitted from a commit.
The checks also launch both command-line scripts from another directory without
user-installed Python packages or `PYTHONPATH` supplying missing imports.

## Add another statistic

- `dataset.py` reads the public `ltb-dataset/2` protocol using `evidence-core`.
  It normalizes declarations, source ranges and proof-inclusive references into
  the same records used by the legacy collected-JSON reader. Compatibility is
  checked by schema; no Lean or Referee release is hardcoded in the adapter.
  A toolchain bump needs no Stats change while the protocol remains compatible.
- `reader.py` validates the declaration population and links against the rendered
  site and source checkout. The dataset, rendered site and checkout must agree
  on the project and revision. Unknown schemas and partial sites fail clearly.
- `render.py` shares the output writer and interactive viewer across both site
  layouts. The current Referee integration adds its own small navigation script
  without rewriting upstream's application JavaScript.
- `metrics.py` registers a statistic's stable name, explanation, subject,
  calculation and display. Calculations receive the shared declaration catalog
  plus the decoded input. Add a metric there and a small, independently countable
  test. For another declaration-count histogram, the page, selector, links and
  searchable list work without changes.
- `render.py` adds the page and navigation. The viewer and styles live in
  `assets/`. A future chart style belongs in the viewer's display handlers;
  it should reuse the catalog and list instead of copying the whole page.

`stats/data.json` has a versioned public format (`schema_version: 1`): `build`
records the repository, exact commit, Lean version, tool versions and input hash;
`population` records the included/excluded counts; `declarations` stores names,
modules, kinds, documentation/source links and source lines; and `metrics` stores
each metric's explanation, subject, method, display and values keyed by declaration ID.
The URL records the selected metric, number of bars, selected range, search and page.

Later results from
[lean-quality-indicators](https://github.com/RemyDegenne/lean-quality-indicators)
must enter as separately recorded review results, not as ordinary reuse counts.
Each imported review must identify the exact source commit, whether its subjects
are declarations or files, the eligible and reviewed populations, sampling method,
judge/model and review instructions, failures and uncertainty/confidence intervals.
A file review should reference a shared file catalog with source links; it must not
be assigned arbitrarily to every declaration in that file. Add a display handler
for these results and reuse the surrounding selector and navigation. Reject or
clearly separate reviews of a different commit. Missing/failed reviews must never
count as clean results. No paid reviews run in the website workflow.

After the first deployment, open the public Stats URL, choose a nonempty bar, and
follow a declaration's Documentation and Source links. Confirm API docs, tutorial,
blueprint, exposition and Leanviz still load from the same Pages artifact.

## Compatibility checks

The tests normalize the same hand-counted declarations from the legacy JSON and
extractor dataset formats and require identical reuse counts. They also change
the recorded toolchain to a future version to verify that schema compatibility
is independent of the Lean release. Browser checks cover both site layouts.
The new-format tests need `evidence-core`; the Referee action installs the pinned
Python dependencies before the full-site checks. For standalone use, install
the maintained Referee tools into a separate Python environment. Tool versions
and the input digest are recorded as provenance, rather than compatibility gates.
