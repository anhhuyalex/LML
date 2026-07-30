# Efficiency Audit: `LeanMachineLearning/Optimization/Lasso`

This report complements `docs/Lasso_formalization_report.md` (which certifies
*faithfulness*: every statement in `docs/Lasso.md` has a matching, correctly-stated
Lean declaration). This report asks a different question: **given that the
statements are right, is the surrounding proof code the most effective way to
get to a finished, maintainable proof?**

Method: every file in the folder was read in full (Definitions.lean, Dynamic.lean,
Basic.lean, Theorems.lean, Bounds/Energy.lean read directly; MirrorFlow.lean,
LCP.lean, Bounds/Delta.lean reviewed by three parallel deep-read passes), cross-checked
against Mathlib source in `.lake/packages/mathlib` and against `grep -rn` usage across
the whole `Lasso/` folder. Total: ~8,150 lines across 8 files.

**Bottom line:** the four flagship theorem *statements* (`lasso_connection_monotone`,
`lasso_connection_approx`, `pos_lasso_connection_monotone`, `pos_lasso_connection_approx`)
are well-designed and not the problem — see §5. The inefficiency lives almost entirely
in the ~6,700 lines of supporting API beneath them, and it clusters into five repeatable
patterns rather than being scattered randomly. Fixing the patterns (not each site
individually) is the highest-leverage next step, and would directly unblock several of
the `sorry`s that remain in `Theorems.lean` and `Bounds/Delta.lean`.

---

## 1. The dominant pattern: no shared "EuclideanSpace plumbing" library

`EuclideanSpace ℝ ι` is `PiLp 2 (fun _ : ι => ℝ)` under the hood, so every basic
operation (inner products, `matVec`, coordinate access, continuity of coordinate
projections) has to be unwrapped through `WithLp.equiv`/`PiLp.inner_apply` before
`ring`/`simp` can see through it. This project never factored that unwrapping into a
reusable lemma set, so **the same three or four unwrapping idioms get re-proved from
scratch at 25+ call sites across four different files**:

| Idiom | Occurrences | Where |
|---|---|---|
| `EuclideanSpace ℝ ι ≃L[ℝ] (ι → ℝ)` + "coordinate projection is continuous" | **14** | `Bounds/Delta.lean:29,63,269,504,1022`; `MirrorFlow.lean:225,628,684,694,995,1010,1295,1320,1341` |
| `inner ℝ (euclideanOf f) h = ∑ i, f i * h i` via `EuclideanSpace.inner_eq_star_dotProduct` + `Finset.sum_congr` | **12** | `MirrorFlow.lean:138,148,158,178,187,194,201,770,807,1479,1669,1683` |
| `inner`/sum splitting over `ι ⊕ ι` via `Fintype.sum_sum_type` | **3** | `Basic.lean:191-220` (`inner_augmentedVector_sumElim`, could just call the general `inner_sumElim` at `Basic.lean:223` two lines below it instead of re-deriving the same computation), `Basic.lean:223-234` (`inner_sumElim` itself, the one that should be canonical), `Theorems.lean:615-636` (`h_norm` inside `lasso_objective_reduction`, unfolds the L¹-norm case of the identical split by hand a third time) |
| `matVec M` repackaged as a `LinearMap` (`{toFun := matVec M, map_add' := ..., map_smul' := ...}`) | 2 | `MirrorFlow.lean:452-456`, `MirrorFlow.lean:1013-1017` — should live once in `Basic.lean` next to `matVec_add`/`matVec_smul_eq` |
| `log(1/ε) > 0` for `0 < ε < 1` | 8 | `Bounds/Delta.lean:319,410,664,726,744,814,869,1058` |
| `Set.Ioo 0 c ∈ 𝓝[>] 0` filter boilerplate | 6 | `Bounds/Delta.lean:313-316,402-404,613-615,649-651,809-811,1235-1237` |

**Recommendation:** add a small `EuclideanAPI` section to `Basic.lean` (or a new
`Lasso/EuclideanAPI.lean`) exposing: `euclideanToPiEquiv`, `continuous_euclidean_apply`,
`inner_euclideanOf_eq_sum` (as `@[simp]`), `matVecLM`, `log_one_div_pos`, and
`eventually_mem_Ioo_zero`. This one change would delete on the order of 300-400 lines
of repeated boilerplate and — more importantly — make the remaining `sorry`s in
`Theorems.lean`/`Bounds/Delta.lean` shorter to close, since most of them currently need
exactly this plumbing before they can even state their real content.

---

## 2. Generic math facts reproved from scratch instead of reused

This is the most consequential category because in two cases the from-scratch version
is not just longer but *strictly weaker*, which is itself the direct cause of open
`sorry`s downstream.

- **Cauchy–Schwarz for a PSD matrix's `matVec` seminorm — proved three separate ways.**
  - `Basic.lean:327-356` (`matVec_norm_sq_le_trace_mul`) does it right: builds
    `B := Matrix.toLinearMap₂' ℝ M` and calls Mathlib's
    `LinearMap.BilinForm.apply_sq_le_of_symm` (`Mathlib/LinearAlgebra/SesquilinearForm/Basic.lean:843`,
    which for **arbitrary** `x y` gives `(B x y)^2 ≤ B x x * B y y` directly — no
    per-index restriction). This is correctly reused later at `MirrorFlow.lean:1183`.
  - `Bounds/Energy.lean:64-115` (`h_cauchy_sq` inside `dual_path_derivative_inner_bound`)
    re-derives the *identical* inequality — `inner u (matVec M v)^2 ≤ inner u (matVec M u) * inner v (matVec M v)`
    — from scratch via a 35-line discriminant argument (`h_quad_nonneg`, case split on
    whether `c = 0`, etc.), instead of one call to `B.apply_sq_le_of_symm hs hB u v`
    with the same `B` construction already in `Basic.lean`.
  - `LCP.lean:1715-1838` (`psd_matrix_norm_sq_bound`/`_nonempty`, ~125 lines) proves the
    *weaker, corollary* fact `‖Mv‖² ≤ C·⟨v,Mv⟩` via a full spectral decomposition
    (eigenbasis, `repr` formulas, `Finset.sup'` over eigenvalues) — a strictly harder
    proof of something `matVec_norm_sq_le_trace_mul` already gives directly with
    `C := ∑ i, M i i`. Its only consumer, `scaled_dual_lipschitz` (`LCP.lean:2134`), can
    switch to the existing lemma outright.

  **Total avoidable proof mass: ~160 lines**, and it is the same underlying fact
  proved three times at three different levels of generality.

- **`Bounds/Delta.lean:1464-1487` (`bound_of_deriv_bound`) reproves a Mathlib comparison
  theorem — with strictly stronger, harder-to-discharge hypotheses.** Mathlib's
  `image_le_of_deriv_right_le_deriv_boundary` (`Mathlib/Analysis/Calculus/MeanValue.lean:199`)
  is exactly "if `f a ≤ B a`, both continuous on `[a,b]`, right-differentiable on
  `[a,b)` with `f' ≤ B'` there, then `f ≤ B` on `[a,b]`" — precisely the
  "integrate a differential inequality with matching initial value" step used here.
  Crucially, it only needs **right**-derivatives on a half-open interval, whereas the
  current proof demands full `DifferentiableOn` on `Ioo`, which is *why*
  `positive_path_delta_bound_full` (`Bounds/Delta.lean:1555-1558`) currently has to
  `sorry` its `hF_cont`/`hG_cont`/`hF_diff`/`hG_diff` side goals. Switching to the
  Mathlib lemma would likely close that `sorry`, not just shorten the file.

- **`LCP.lean:1276-1291` (`strict_convex_norm_midpoint_lt`)** reproves Mathlib's
  `norm_midpoint_lt_iff` (`Mathlib/Analysis/Convex/StrictConvexSpace.lean:211`), available
  for any inner product space via the standard `UniformConvexSpace → StrictConvexSpace`
  instance. 16 lines → 1 line.

- **`Bounds/Delta.lean:482-594` (`pos_param_ne_zero_of_gradient_flow`, ~113 lines)**
  hand-builds the integrating-factor argument for "if `x' = a(t)·x` and `x(0) ≠ 0` then
  `x(t) ≠ 0`" per coordinate. This is a generic scalar-ODE fact independent of anything
  Lasso-specific; worth its own standalone lemma (parametrized over `a x : ℝ → ℝ`) even
  if no exact Mathlib match exists, so it isn't re-derived if a signed-path analogue
  needs the same fact later.

---

## 3. Local duplication within a single file

Several proofs are copy-pasted near-verbatim within the same file rather than factored
into a shared private lemma:

- `MirrorFlow.lean:1150-1164` and `MirrorFlow.lean:2019-2031` — the bound
  `quadraticLoss M r (ε • a) ≤ K` is proved twice, line-for-line identical.
- `MirrorFlow.lean:399-404` (`tendsto_sub_self`) is already in scope but
  `MirrorFlow.lean:741-744` re-derives it character-for-character instead of calling it.
- `LCP.lean:1932-1939` and `LCP.lean:2063-2070` — the same 8-line `μ*N < 1` derivation
  (case-split on `N ≤ 1`) is repeated verbatim; factor to
  `mul_lt_one_of_lt_one_div_max`.
- `LCP.lean:814-819`, `1966-1971`, `2091-2096` — the identical 4-clause proof that
  `(0, q)` trivially solves the LCP for pointwise-positive `q` appears three times;
  factor to `isLCP_zero_of_forall_pos`.
- `LCP.lean:562` (`matVec_smul'`) and `LCP.lean:1994` (private `matVec_smul`) each
  restate `Basic.lean:251`'s `matVec_smul_eq` (opposite argument order), used exactly
  once each right after their own definitions — pure near-duplicates that should be
  deleted in favor of the one in `Basic.lean`, which is already used 10+ times
  elsewhere in the same file.

---

## 4. Dead / orphaned code

Confirmed via `grep -rn <name>` across the entire `Lasso/` folder — none of the
following are referenced anywhere outside their own definition:

- `Definitions.lean:68` — `zDownward`, labeled "Compatibility alias for the
  positive-lasso downward variation," is never called; only `positiveZDownward` and
  `signedZDownward` are actually used in `Theorems.lean`.
- `MirrorFlow.lean:882-953` — `tiltedLoss_uniform_upper_bound` (~70 lines, fully
  proved) is unused; it re-derives a fact already covered ad hoc elsewhere (§1's
  `hquadinit`/`hinit` duplication).
- `MirrorFlow.lean:778-787` — `inner_tiltedGradient_positiveEffectiveVectorField_nonpos`
  is unused (its non-`_nonpos` sibling at line 763 is used; this corollary isn't).
- `LCP.lean` — of the four near-identical formalizations of "Lemma 4.10" (small-`μ` LCP
  uniqueness), only `parametric_lcp_eq_iff_of_small_mu` (`LCP.lean:1922`) is actually
  the strongest/most useful form. `parametric_lcp_unique_of_mul_supNorm_lt_one`
  (`LCP.lean:803-836`, ~34 lines) is never called anywhere; `parametric_lcp_unique_small_mu`
  (`LCP.lean:1979`) is referenced only in prose docstrings, and its real call site in
  `Theorems.lean` is itself a `sorry`. Recommend consolidating to one canonical lemma
  plus a derived `∃!` corollary, and deleting the rest — this alone removes ~80 lines
  and one axis of "which of these four do I use" confusion for future contributors.

---

## 5. The four flagship theorems specifically

Re-examining `lasso_connection_monotone`, `lasso_connection_approx`,
`pos_lasso_connection_monotone`, `pos_lasso_connection_approx` in `Theorems.lean`
against the question "is this the best formalization *approach*":

- **The top-level statement shapes are correct and idiomatic.** `limsup ≤ bound` is
  expressed as `∃ C > 0, ∀ s > 0, ∀ δ > 0, ∀ᶠ ε in 𝓝[>] 0, ... ≤ ... + δ`, which is the
  standard Mathlib idiom for a `limsup` upper bound without committing to a
  `Filter.limsup` term that would need extra boundedness side conditions. The exact
  case uses plain `Tendsto ... (𝓝[>] 0) (𝓝 ...)`. Both match `docs/Lasso_formalization_report.md`'s
  assessment and don't need to change.
- **The dependency structure mirrors the paper correctly**: `pos_lasso_connection_monotone`
  is planned to be derived from `pos_lasso_connection_approx` by showing the error term
  vanishes under monotonicity (`positiveZDownward x_lasso s = 0`), exactly matching the
  paper's Thm 3.2 ⟹ Thm 3.1 structure and the dependency graph in
  `Lasso_formalization_report.md`. Same for the signed pair via the Section 5 reduction.
  This is the right decomposition — it is not being second-guessed here.
- **What *is* costing effort at this layer**: `positive_path_energy_bound`
  (`Theorems.lean:291-373`) has three `sorry`d `have`s (`hw_eq`, `hx_nonneg`,
  `hxE_nonneg`, `h_average_eq`, `h_lasso_min_eq`) that are pure algebraic
  unfolding of `isParametricLCP`/`scaledPrimalPath`/`posAverageTrajectory` definitions —
  exactly the kind of gap that a slightly richer field-access API on
  `isParametricLCP`/`isLCP` (in the spirit of how `ParametricLCPDualRegular`'s named
  fields already let `Bounds/Energy.lean` consume it without re-deriving spectral facts
  — a pattern the LCP.lean review explicitly called out as *already working well*)
  would close quickly. In other words: the theorem statements don't need to change,
  but closing them is currently harder than it should be because the definitions one
  layer down (`isParametricLCP`, `scaledPrimalPath`) don't yet expose the same kind of
  ergonomic derived-lemma surface that `ParametricLCPDualRegular` does.

---

## 6. Prioritized recommendations

1. **Add the `EuclideanAPI` mini-library described in §1.** Single highest-leverage
   change; touches every file and shortens/simplifies several open `sorry`s for free.
2. **Delete the `LCP.lean:1715-1838` spectral proof and route `scaled_dual_lipschitz`
   through `Basic.lean`'s `matVec_norm_sq_le_trace_mul` instead.** ~125 lines removed,
   zero mathematical content lost.
3. **Replace `Bounds/Energy.lean`'s 35-line discriminant argument with
   `LinearMap.BilinForm.apply_sq_le_of_symm` directly**, using the same `B` construction
   already established in `Basic.lean:332-343`.
4. **Swap `Bounds/Delta.lean`'s `bound_of_deriv_bound` for Mathlib's
   `image_le_of_deriv_right_le_deriv_boundary`.** This is the one case where the
   refactor is likely to *close* a `sorry` (the differentiability side conditions at
   `Bounds/Delta.lean:1555-1558`) rather than merely shorten a finished proof.
5. **Consolidate the four Lemma-4.10 variants in `LCP.lean` to one.**
6. **Sweep the confirmed dead code** (§4): `zDownward`, `tiltedLoss_uniform_upper_bound`,
   `inner_tiltedGradient_positiveEffectiveVectorField_nonpos`,
   `parametric_lcp_unique_of_mul_supNorm_lt_one`, `matVec_smul'`/private `matVec_smul`.
7. **Factor the small repeated blocks in §3** (`mul_lt_one_of_lt_one_div_max`,
   `isLCP_zero_of_forall_pos`, the `quadraticLoss M r (ε•a) ≤ K` duplicate).

None of these require touching the mathematical content of any proof or the statement
of any theorem — they are pure API/reuse cleanups, safe to do incrementally file-by-file
without risking the faithfulness verified in `docs/Lasso_formalization_report.md`.
