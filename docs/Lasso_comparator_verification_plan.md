# Plan: verifying `Optimization/Lasso` against `docs/Lasso.md` with comparator

Target project: `LeanMachineLearning/Optimization/Lasso`
Source of truth: `docs/Lasso.md` (Berthier, *Diagonal Linear Networks and the Lasso
Regularization Path*, arXiv:2509.18766)
Tool: <https://github.com/leanprover/comparator>

---

## 1. What comparator actually does (and does not do)

Comparator is a **proof judge**, not a faithfulness judge. It takes two Lean modules —
a `challenge_module` holding statements and a `solution_module` holding proofs — plus a
JSON config, and certifies that for every name in `theorem_names`:

1. the solution's declaration has **exactly the same type** as the challenge's;
2. the proof term uses **no axiom outside `permitted_axioms`**;
3. the term **passes the Lean kernel**, re-checked from a `lean4export` dump rather
   than from `.olean` files (deliberately, since `.olean` loading is untrusted), under a
   `landrun` sandbox that exists to protect the checker from meta-program attacks, not
   to protect the host.

Config shape:

```json
{
    "challenge_module": "Challenge",
    "solution_module": "Solution",
    "theorem_names": ["thm_2_1"],
    "definition_names": [],
    "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"],
    "enable_nanoda": false
}
```

Invocation: `lake env path/to/comparator config.json`, optionally wrapped in
`systemd-run --property=RestrictAddressFamilies=~AF_UNIX --user --pty ...`.

**What it does not do.** Comparator has no idea what `Lasso.md` says. If the challenge
module's `lassoObjective` is subtly wrong, comparator will happily certify a proof of the
wrong theorem. The README says this explicitly about definition holes: they are
"vulnerable to trivial solutions. Humans must verify definitions separately."

So comparator closes exactly one of the two gaps:

| Gap | Question | Closed by |
| --- | --- | --- |
| A | Is this Lean statement the paper's theorem? | human audit of a small spec file |
| B | Is this Lean statement honestly proved? | comparator |

The whole plan below is structured around shrinking gap A to something a human can
actually read, then handing gap B to comparator.

---

## 2. Baseline: where the project stands right now

Measured on 2026-07-31, toolchain `leanprover/lean4:v4.33.0-rc1`, Mathlib pinned at
`abb22825db7e020c94f38a007ae3fffe6c3a7532`.

- 287 `theorem`/`lemma` declarations across the folder.
- No `axiom`, `native_decide`, `unsafe`, or `implemented_by` anywhere. Good.
- **30 `sorry`s**: 23 in [Theorems.lean](LeanMachineLearning/Optimization/Lasso/Theorems.lean),
  7 in [Bounds/Energy.lean](LeanMachineLearning/Optimization/Lasso/Bounds/Energy.lean).
  All other files are sorry-free.
- Theorem 3.1 itself is a `sorry`:
  [Theorems.lean:504](LeanMachineLearning/Optimization/Lasso/Theorems.lean#L504).
- All four headline theorems are `sorryAx`-tainted today:

```
'Lasso.lasso_connection_monotone'      depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Lasso.lasso_connection_approx'        depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Lasso.pos_lasso_connection_monotone'  depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Lasso.pos_lasso_connection_approx'    depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

There is also an existing self-assessment,
[docs/Lasso_formalization_report.md](docs/Lasso_formalization_report.md), which concludes
"**There are no missing statements** ... You can safely proceed with filling in the
proofs without worrying about proving the wrong statements." That claim is unverified and
was written by the same process that wrote the code. It is precisely the kind of artifact
comparator exists to backstop; this plan treats it as a hypothesis to test, not as
evidence.

---

## 3. The surface that actually needs auditing

The four headline theorems mention only ~18 defined notions. Everything else in the
folder is proof plumbing that comparator's kernel check covers for free. Enumerated:

| Notion | Location | Paper anchor |
| --- | --- | --- |
| `ProblemData` | [Basic.lean:156](LeanMachineLearning/Optimization/Lasso/Basic.lean#L156) | §1, `M ⪰ 0`, `r ∈ Span M`, `λ ≥ 0` |
| `lassoObjective` | [Basic.lean:171](LeanMachineLearning/Optimization/Lasso/Basic.lean#L171) | `Lasso(x, μ)` |
| `positiveLassoObjective` | [Basic.lean:180](LeanMachineLearning/Optimization/Lasso/Basic.lean#L180) | §3 |
| `IsLassoMinimizer` | [Basic.lean:219](LeanMachineLearning/Optimization/Lasso/Basic.lean#L219) | Thm 2.1 preamble |
| `IsPositiveLassoMinimizer` | [Basic.lean:225](LeanMachineLearning/Optimization/Lasso/Basic.lean#L225) | Thm 3.1 preamble |
| `NonzeroCoordinates` | [Basic.lean:71](LeanMachineLearning/Optimization/Lasso/Basic.lean#L71) | §3 initialization |
| `dlnGradientFlow` | [Dynamic.lean:39](LeanMachineLearning/Optimization/Lasso/Dynamic.lean#L39) | Eq. (1.2) |
| `posDlnGradientFlow` | [Dynamic.lean:53](LeanMachineLearning/Optimization/Lasso/Dynamic.lean#L53) | §3, `x = u²` |
| `averageTrajectory` | [Dynamic.lean:67](LeanMachineLearning/Optimization/Lasso/Dynamic.lean#L67) | `x̄^ε(t)` |
| `posAverageTrajectory` | [Dynamic.lean:83](LeanMachineLearning/Optimization/Lasso/Dynamic.lean#L83) | §3 |
| `timeFromRescaled` | [Dynamic.lean:96](LeanMachineLearning/Optimization/Lasso/Dynamic.lean#L96) | Eq. (2.2), `t = (s/2)·log(1/ε)` |
| `posTimeFromRescaled` | [Dynamic.lean:104](LeanMachineLearning/Optimization/Lasso/Dynamic.lean#L104) | §3 analogue |
| `lassoMin` | [Definitions.lean:33](LeanMachineLearning/Optimization/Lasso/Definitions.lean#L33) | `Lasso_*(s)` |
| `posLassoMin` | [Definitions.lean:38](LeanMachineLearning/Optimization/Lasso/Definitions.lean#L38) | §3 |
| `suboptimalityGap` | [Definitions.lean:76](LeanMachineLearning/Optimization/Lasso/Definitions.lean#L76) | Eq. (2.4), `η(λ,s,z↓)` |
| `positiveZDownward` | [Definitions.lean:58](LeanMachineLearning/Optimization/Lasso/Definitions.lean#L58) | Eq. (3.6) |
| `signedZDownward` | [Theorems.lean:974](LeanMachineLearning/Optimization/Lasso/Theorems.lean#L974) | Eq. (2.3) |
| `LocallyAbsolutelyContinuousOnPositiveCompacts` | [LCP.lean:69](LeanMachineLearning/Optimization/Lasso/LCP.lean#L69) | Thm 2.2 hypothesis |
| `LocallyAbsolutelyContinuousOnNonnegativeCompacts` | [LCP.lean:79](LeanMachineLearning/Optimization/Lasso/LCP.lean#L79) | Lem. 4.12 |

**This table is the entire gap-A surface for the headline results.** Roughly 200 lines of
definitions versus ~330 KB of proof. That ratio is the leverage.

---

## 4. Phased plan

### Phase 0 — Honest baseline (½ day, no comparator needed)

**0.1 Axiom census.** Script `#print axioms` over every declaration that the paper
names — not just the four headliners, but Prop 4.1, Lem 4.2–4.12, Thm 4.6, Prop 4.8–4.9,
Lem 5.1(1)–(3), and the §5.1.2 dynamics reduction, using the mapping already tabulated in
`Lasso_formalization_report.md`. Emit a machine-readable table of
`decl → {clean | sorryAx}`. This is a 30-second proxy for what comparator will conclude,
and it tells you up front which configs can pass.

**0.2 Sorry provenance.** For each of the 30 `sorry`s, record which paper statement it
blocks. Distinguish "this is a genuine open proof obligation" from "this is a statement
that was never going to be provable as written."

**0.3 Non-vacuity witnesses.** *This is the failure mode comparator structurally cannot
see.* A theorem with unsatisfiable hypotheses is trivially true and will pass every
mechanical check. For each headline theorem, construct a concrete instance — `ι = Fin 1`,
`M = 1`, `r = 1`, `λ = 0`, `β = 1`, `γ = 0` — and prove the hypothesis bundle is
inhabited:

```lean
example : ∃ (M : Matrix (Fin 1) (Fin 1) ℝ) (r : EuclideanSpace ℝ (Fin 1)) (lambda : ℝ),
    ProblemData M r lambda := ...
example : ∃ w, ∀ ε > 0, dlnGradientFlow M r lambda ε β γ (w ε) := ...
example : ∃ x, ∀ μ > 0, IsLassoMinimizer M r lambda μ (x μ) := ...
```

`dlnGradientFlow` and `IsLassoMinimizer` are the two to worry about: an existence
predicate over an ODE solution and over a minimizer, either of which could be
accidentally over-constrained into emptiness. Ship these as permanent regression tests.

**Deliverable:** `docs/Lasso_verification_status.md`, generated, with a row per paper
statement.

### Phase 1 — Write `Spec.lean`, the trust anchor (2–4 days, the real work)

Create a new lean_lib so the verification artifacts never contaminate the library:

```
Verification/
  Lasso/
    Spec.lean       -- paper-faithful definitions, Mathlib imports ONLY
    Challenge.lean  -- import Spec; four theorem statements, proofs := sorry
    Solution.lean   -- import Spec + the project; four theorems, real proofs
    Bridge.lean     -- Lasso.foo = Spec.foo, one per row of §3
  comparator/
    strict.json
    progress.json
```

`lakefile.toml` gains:

```toml
[[lean_lib]]
name = "Verification"
```

**The hard constraint on `Spec.lean`: it must not import `LeanMachineLearning`.** If the
spec imports the project's definitions, the whole exercise is circular — comparator would
be checking the project against itself. Every notion in the §3 table gets re-derived from
Mathlib primitives by direct transcription from `Lasso.md`, with a doc-comment citing the
equation number and the `Lasso.md` line range.

Then a human reads `Spec.lean` against the paper. That review — a few hundred lines — is
the *only* irreducibly manual step, and its output is a sign-off recording the git blob
hash of `Spec.lean`. CI asserts the hash hasn't drifted without a fresh sign-off, since a
silent edit to `Spec.lean` would invalidate everything downstream and comparator would not
notice.

### Phase 2 — Bridge lemmas (2–5 days, where mismatches surface)

`Bridge.lean` proves one equation per row of the §3 table:

```lean
theorem lassoObjective_eq (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda μ : ℝ) :
    Lasso.lassoObjective M r lambda μ = Spec.lassoObjective M r lambda μ := rfl
```

Most should be `rfl` or a one-liner. **Any bridge that resists proof is a faithfulness
bug** — either the project definition or the spec transcription is wrong, and you have
localized it to one notion instead of searching 330 KB. Prioritize the four with the most
room for error: `timeFromRescaled` (the `s = (2/log(1/ε))·t` rescaling in Eq. (2.2) is
easy to invert), `suboptimalityGap` (Eq. (2.4)'s `(1+λs)[(z↓)^{1/2}/s + z↓/s²]`),
`signedZDownward` (Eq. (2.3)'s positive-and-negative-part integral with the `(·)_-` on the
derivative), and `dlnGradientFlow` (Eq. (1.2)'s weight-decay term).

`Solution.lean` then states each theorem *in spec vocabulary* and discharges it by
rewriting through the bridges into the project theorem:

```lean
theorem thm_2_1 ... : Filter.Tendsto (fun ε => Spec.lassoObjective ...) ... := by
  simpa only [Bridge.lassoObjective_eq, Bridge.averageTrajectory_eq, ...]
    using Lasso.lasso_connection_monotone ...
```

`Challenge.lean` is `Solution.lean` with every proof replaced by `sorry`. Generate it
mechanically from `Solution.lean` so the statements cannot drift apart by hand-editing.

### Phase 3 — Install and run comparator (1–2 days, mostly friction)

Environment is favorable — already confirmed on this host:

- Landlock LSM active (`landlock: Up and running`; `CONFIG_SECURITY_LANDLOCK=y`; LSM list
  is `lockdown,capability,landlock,yama,selinux,bpf`), so `landrun` will work.
- `go`, `cargo`, `rustc`, `systemd-run`, `elan`/`lake` all present.

Steps:

1. Build `landrun` from its **main** branch (the README requires main, not a release).
2. Build `lean4export` at a revision compatible with **v4.33.0-rc1**.
3. Build `comparator`; optionally `nanoda` via `cargo build --release` for the second
   kernel.
4. Either put all three on `PATH` or set `COMPARATOR_LANDRUN`, `COMPARATOR_LEAN4EXPORT`,
   `COMPARATOR_NANODA`.

Two configs, because the interesting information differs:

`comparator/progress.json` — permits `sorryAx`, so it runs today. It answers "do the
proofs we *do* have prove the spec statements, with nothing else fishy?"

```json
{
  "challenge_module": "Verification.Lasso.Challenge",
  "solution_module": "Verification.Lasso.Solution",
  "theorem_names": ["thm_2_1", "thm_2_2", "thm_3_1", "thm_3_2"],
  "permitted_axioms": ["propext", "Quot.sound", "Classical.choice", "sorryAx"],
  "enable_nanoda": false
}
```

`comparator/strict.json` — identical but **`sorryAx` removed** and `enable_nanoda: true`.
This is the completion gate. Per the Phase-0 census it fails today on all four theorems;
the number of theorems it accepts is the project's real progress metric.

Run:

```bash
systemd-run --property=RestrictAddressFamilies=~AF_UNIX --user --pty \
  -E PATH="$PATH" --working-directory "$(pwd)" -- \
  bash -c 'lake env /path/to/comparator Verification/comparator/strict.json'
```

Extend `theorem_names` to every paper-facing declaration from §3/`Lasso_formalization_report.md`
once the four headliners are wired — comparator only checks what you list, and the
Lemma 4.x / 5.x layer is where the sorries actually live.

### Phase 4 — CI and reporting (1 day)

- `scripts/verify_lasso.sh` runs Phase 0's axiom census, the non-vacuity witnesses, the
  `Spec.lean` hash check, and both comparator configs.
- GitHub Actions job on PRs touching `Optimization/Lasso` or `Verification/`; `progress`
  config blocking, `strict` config reported but non-blocking until the sorries close.
- Regenerate `docs/Lasso_verification_status.md` each run.
- Correct `docs/Lasso_formalization_report.md`: keep the statement-mapping table, which is
  genuinely useful, but replace the "safely proceed / no missing statements" conclusion
  with a pointer to the generated status file. As written it overstates what has been
  established.

---

## 5. Risks

**R1 — Module system vs. lean4export (highest).** The project uses Lean 4.33's new module
system: `module`, `public import`, `@[expose] public section`. Comparator and lean4export
were exercised mostly on pre-module code, and the Zulip thread shows lean4export's export
scope is actively being tightened (the `NeZero` / `IsLeftRegular` "Const not found in
target" bug, fixed in comparator PR #16). *Mitigation:* spike this first — before writing
any spec, put a two-line toy challenge/solution pair through comparator against a single
trivial `Lasso` lemma. If module-system files fail to export, write `Verification/` as
plain non-module files (ordinary `import`) and check whether importing a module-system
library from a non-module file exports cleanly. Do this in an afternoon, before Phase 1.

**R2 — Toolchain skew.** Comparator pins its own toolchain and the Zulip thread's most
common failure is exactly this mismatch (4.22 vs 4.29-rc1). If comparator's toolchain is
incompatible with v4.33.0-rc1, the options are bumping comparator's toolchain (Henrik
called downgrading unreliable) or advancing the project. Resolve during the R1 spike.

**R3 — Circularity.** Guarded by the "Spec must not import the project" rule plus the
sign-off hash. It is the single easiest way to make this whole effort worthless, and the
easiest way to do it accidentally is to add one convenience import to `Spec.lean`.

**R4 — Vacuous hypotheses.** Comparator is blind to it. Phase 0.3 is the only defense.

**R5 — Sandbox in a shared-cluster environment.** `systemd-run --user` needs a user
session bus; on a login node without one, fall back to running comparator's own `landrun`
sandbox unwrapped. Do not attempt to disable sandboxing — upstream is explicit that this
is not negotiable and there is no unsandboxed mode.

---

## 6. Effort and sequencing

| Phase | Effort | Blocking |
| --- | --- | --- |
| R1/R2 spike | ½ day | everything |
| 0 — baseline + non-vacuity | ½–1 day | independent, do in parallel |
| 1 — `Spec.lean` + human sign-off | 2–4 days | needs R1 resolved |
| 2 — bridges + Solution/Challenge | 2–5 days | needs 1 |
| 3 — comparator wiring | 1–2 days | needs 2 |
| 4 — CI + reporting | 1 day | needs 3 |

Roughly 1.5–3 weeks to a green `progress` gate. The `strict` gate is not an engineering
task — it is gated on closing 30 sorries, which is the mathematics.

The order matters: Phase 0 and the R1 spike are cheap and independently useful, and Phase
0's axiom census alone already tells you more about the project's true state than
`Lasso_formalization_report.md` does.
