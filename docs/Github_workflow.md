# GitHub Workflow Guide — anhhuyalex/LML

This document explains how the CI/CD pipeline works for the LML fork and what to keep in mind when modifying Lean source, documentation, or the website at https://anhhuyalex.github.io/LML/.

---

## Overview

The workflow lives at `.github/workflows/blueprint.yml` and runs on every push to `main` and every PR targeting `main`. It builds the Lean library, runs linters, generates three documentation outputs, and deploys them to GitHub Pages.

Monitor runs at: https://github.com/anhhuyalex/LML/actions

The live site is at: https://anhhuyalex.github.io/LML/

---

## What the workflow builds

| Output | URL path | Source | Built on |
|---|---|---|---|
| Landing page | `/` | `home_page/index.html` | push + PR |
| Tutorial docs (Verso) | `/tutorial/` | `LMLTutorial/` via `scripts/build_docs.sh` | push + PR |
| Exposition (interactive theorem browser) | `/exposition/` | `LeanMachineLearning/exposition` tool + Lean source | push only |
| API docs | `/docs/` | `leanprover-community/docgen-action` | push + PR |

The exposition step is skipped on PRs to save build time — you only get it after merging to `main`.

---

## Build pipeline, step by step

1. **Free disk space** — deletes Android SDK (~12 GB) to make room for Mathlib's `.olean` cache.
2. **Build and lint** (`leanprover/lean-action`) — compiles the library, runs all linters, and checks that `LeanMachineLearning.lean` is up to date via `mk_all`.
3. **Build Verso docs** (`scripts/build_docs.sh`) — builds the tutorial using `lake exe tutorial`.
4. **Clone exposition tool** — clones `LeanMachineLearning/exposition` (controlled by `LEAN_EXPOSITION_REPO` / `LEAN_EXPOSITION_REF` env vars at the top of the workflow).
5. **Run exposition** — runs the exposition binary against your compiled Lean source to produce the interactive HTML.
6. **docgen-action** — generates API documentation.
7. **Deploy** — uploads `home_page/` as a GitHub Pages artifact and deploys it.

---

## Subtleties and gotchas

### `LeanMachineLearning.lean` must stay in sync

The `mk_all-check: true` flag in the workflow verifies that the root import file `LeanMachineLearning.lean` lists every `.lean` file in the library. If you add or delete a file without regenerating this index, the build fails with:

```
The file 'LeanMachineLearning.lean' is out of date: run `lake exe mk_all` to update it
```

Fix: run `lake exe mk_all` locally after adding or deleting any `.lean` file, then commit the updated `LeanMachineLearning.lean`.

### Linter requirements for new code

The workflow runs all Mathlib linters. Two that commonly trip up new files:

- **`docBlame`** — every field of a `structure` needs a `/-- ... -/` doc string. The parent structure's doc string is not enough; each field must have its own.
- **`unusedArguments`** — theorem hypotheses that appear in the signature but are not referenced in the proof body will cause a lint error. Either use the hypothesis in the proof, or prefix it with `_` (e.g. `(_hρ : 0 < ρ)`) to signal it is intentionally unused.

Lint exemptions can be added to `scripts/nolints.json` as a last resort, but fixing the code is preferred.

### Exposition only deploys on push to `main`

Steps that clone and run the exposition tool are gated on `github.event_name == 'push'`. PRs will build and lint successfully but will not update the exposition output. This is intentional — the full exposition build takes significant time.

### The landing page (`home_page/index.html`)

The upstream repo's `home_page/index.html` is a redirect to `leanmachinelearning.github.io`. This fork replaces it with a simple landing page linking to `/exposition/` and `/tutorial/`. Do not revert this file to the upstream version or the site will bounce visitors to the upstream project.

### Hardcoded fork URLs

Two places in the repo reference the fork's GitHub URL directly. If the repo is ever renamed or transferred, both must be updated:

- `.github/workflows/blueprint.yml` lines 79–80: `--repo-url` and `--site-url` flags passed to the exposition binary.
- `verso_blueprint/Main.lean` lines 16–17: `sourceLink` and `issueLink` values used in the blueprint HTML.

### GitHub Pages must be set to "GitHub Actions" source

In the fork's settings (`Settings → Pages → Source`), the source must be set to **GitHub Actions**, not a branch. If it is set to a branch, the deploy step will succeed but the site will not update.

### Exposition tool version is pinned to `LeanMachineLearning/exposition@main`

The workflow always clones the latest `main` of the upstream exposition tool (see `LEAN_EXPOSITION_REF: main` at the top of the workflow). If the upstream tool introduces a breaking change, the build may fail. To pin to a specific commit, change `LEAN_EXPOSITION_REF` to a commit SHA.

---

## Common failure modes and fixes

| Symptom | Cause | Fix |
|---|---|---|
| `mk_all failed` | New `.lean` file not in `LeanMachineLearning.lean` | Run `lake exe mk_all` locally and commit |
| `docBlame` lint errors | Struct fields missing doc strings | Add `/-- ... -/` above each field |
| `unusedArguments` lint errors | Hypothesis in theorem signature not used in proof | Prefix with `_` or use it in the proof |
| Site not updating after successful build | GitHub Pages source not set to "GitHub Actions" | Fix in `Settings → Pages` |
| Site redirects to leanmachinelearning.github.io | `home_page/index.html` was reverted to upstream | Restore fork version of `home_page/index.html` |
| Exposition output missing after PR merge | Exposition only runs on push, not PR | Wait for the post-merge push build to complete |

---

## Local development and preview

None of the tools in this stack have hot-reload. Iteration speed depends on what you are editing.

### Blueprint prose (`verso_blueprint/LMLBlueprint/`)

No Lean recompile needed — the fastest loop:

```bash
cd /jukebox/norman/qanguyen/autoform/LML
lake exe blueprint-gen --output verso_blueprint/_out/site
python3 -m http.server 8080 --directory verso_blueprint/_out/site/html-multi/
```

Edit → re-run `blueprint-gen` → refresh browser.

### Lean source (theorems, definitions)

Always validate proofs in the VS Code infoview before running any build. `lake build` with Mathlib takes tens of minutes from scratch; the `.olean` cache helps on subsequent runs:

```bash
lake exe cache get   # fetch prebuilt Mathlib .olean files
lake build
```

### Exposition (interactive theorem browser)

The exposition tool has a three-step split. Steps 1–2 require Lean data and are slow; step 3 is standalone and fast, allowing iteration on site generation without re-importing:

```bash
# Step 1 & 2: only when Lean source changes
lake env "$EXPOSITION_BIN" collect --root LeanMachineLearning --data data.json
lake env "$EXPOSITION_BIN" extract --data data.json --output ./exposition-out

# Step 3: fast, iterate freely
"$EXPOSITION_BIN" build-site --data data.json --output ./exposition-out
python3 -m http.server 8080 --directory ./exposition-out
```

### API docs (doc-gen4)

```bash
cd /jukebox/norman/qanguyen/autoform/LML/docbuild
lake build LeanMachineLearning:docs
python3 -m http.server 8080 --directory .lake/build/doc/
```

Must be served via HTTP — opening HTML files directly in a browser breaks navigation.

### Tutorial docs

```bash
./scripts/build_docs.sh
python3 -m http.server 8080 --directory LMLTutorial/_out/site/html-multi/
```

### Recommended edit loop

1. Validate Lean changes in the VS Code infoview before running any build.
2. Preview blueprint prose locally with `blueprint-gen` — no CI needed.
3. Run `lake lint` locally before pushing to catch `docBlame` and `unusedArguments` errors early.
4. Push to CI when Lean source changes are ready or you want the full exposition output.
5. Committing just to check output is expensive (30–60 min build). Prefer local preview for everything except the final exposition.

---

## Pre-push checklist

Run these steps in order before every push that touches Lean source. Each one catches a class of CI failure that is expensive to debug after the fact.

### 1. Verify all Mathlib imports exist on disk

The Mathlib version is pinned in `lake-manifest.json`. Module reorganizations between Mathlib releases mean a path that looks correct may not exist in the pinned version. Always check imports against the actual files under `.lake/packages/mathlib/`:

```bash
# Check a specific import — e.g. Mathlib.MeasureTheory.Integral.Bochner
find .lake/packages/mathlib -path "*/MeasureTheory/Integral/Bochner.lean"
# If nothing is printed, the file does not exist; browse the directory to find the real path:
ls .lake/packages/mathlib/Mathlib/MeasureTheory/Integral/
```

Common reorganizations that have caused failures in this repo:

| Old path (no longer exists) | Correct path in current Mathlib |
|---|---|
| `Mathlib.MeasureTheory.Integral.Bochner` | `Mathlib.MeasureTheory.Integral.Bochner.Basic` (also `.L1`, `.Set`, etc.) |
| `Mathlib.MeasureTheory.Decomposition.SignedHahn` | `Mathlib.MeasureTheory.VectorMeasure.Decomposition.Jordan` |
| `Mathlib.MeasureTheory.Function.L1Space` | `Mathlib.MeasureTheory.Function.L1Space.Integrable` (also `.AEEqFun`, etc.) |
| `Mathlib.MeasureTheory.Measure.GaussianOrthogonalGroup` | Does not exist in current Mathlib; remove the import (use `Mathlib.Probability.Distributions.Gaussian.Real` instead) |
| `Mathlib.Probability.Distributions.Gaussian` | `Mathlib.Probability.Distributions.Gaussian.Real` (for `gaussianReal`) or `.Basic`, `.Multivariate`, etc. |
| `Mathlib.Probability.Variance` | `Mathlib.Probability.Moments.Variance` |

A bad import in one file produces `bad import` errors in every file that transitively imports it, so a single wrong path can break the entire build.

### 2. Register new files with `mk_all`

Every `.lean` file in `LeanMachineLearning/` must appear in the root `LeanMachineLearning.lean` index. The CI enforces this with `mk_all-check: true`. After adding or deleting any file:

```bash
cd /jukebox/norman/qanguyen/autoform/LML
lake exe mk_all
git add LeanMachineLearning.lean
```

### 3. Fetch the Mathlib cache and build locally

A full build from scratch takes tens of minutes. The `.olean` cache makes it fast:

```bash
lake exe cache get
lake build
```

Fix all errors before pushing. Warnings about `sorry` are acceptable (CI treats them as warnings, not failures), but import errors and type errors will fail the build.

### 4. Run the linter

```bash
lake lint
```

The two linter errors most likely to appear in new files are `docBlame` (struct fields missing doc strings) and `unusedArguments` (hypothesis in signature not referenced in proof body — prefix with `_` to silence). See the *Linter requirements* section above for details.
