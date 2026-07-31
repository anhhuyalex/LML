/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.Lasso.Dynamic
public import LeanMachineLearning.Optimization.Lasso.LCP
public import LeanMachineLearning.Optimization.Lasso.MirrorFlow
public import LeanMachineLearning.Optimization.Lasso.Definitions
public import LeanMachineLearning.Optimization.Lasso.Bounds.Delta
public import LeanMachineLearning.Optimization.Lasso.Bounds.Energy
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Data.Matrix.Block

/-!
# Theorems on the Lasso Regularization Path

This file states the main theorem layer for the lasso regularization path
formalization.  Declarations are ordered by proof dependency:

1. path quantities;
2. Section 4.6 positive-path estimates;
3. positive approximate and monotone theorems;
4. Section 5 signed-to-positive reductions;
5. signed approximate and monotone theorems.

This topological order is intentional.  In particular, signed theorems appear
after `lasso_objective_reduction` and `dln_dynamics_reduction`, because their
informal proofs depend on those reductions.
-/

@[expose] public section

namespace Lasso

open Filter Topology
variable {ι : Type*} [Fintype ι]
set_option linter.unusedFintypeInType false

/--
The product `μ ↦ μ x(μ)` is locally absolutely continuous on positive compacts because
both `x` and `μ ↦ μ` are.

Informal Proof Outline:
For `μ > 0`, `x(μ)` is locally absolutely continuous (by hypothesis), and the identity
function `μ ↦ μ` is Lipschitz, hence locally absolutely continuous. The product of two locally
absolutely continuous functions is locally absolutely continuous.
-/
lemma scaled_path_ac_on_positive
    (x_lasso : ℝ → EuclideanSpace ℝ ι)
    (h_regular : LocallyAbsolutelyContinuousOnPositiveCompacts x_lasso) :
    LocallyAbsolutelyContinuousOnPositiveCompacts (scaledPrimalPath x_lasso) := by
  -- Goal: ∀ a b, 0 < a → a ≤ b → AbsolutelyContinuousOnInterval (scaledPrimalPath x_lasso) a b
  refine ⟨λ a b ha hle => ?_⟩
  -- Extract AC of x_lasso on [a,b] from the hypothesis
  have hx_ac : AbsolutelyContinuousOnInterval x_lasso a b :=
    h_regular.absolutelyContinuousOn_Icc a b ha hle
  -- The identity function μ ↦ μ is 1-Lipschitz on any compact interval, hence AC
  -- (pattern from Bounds/Delta.lean:3487; Mathlib: LipschitzOnWith.absolutelyContinuousOnInterval)
  have hid_lip : LipschitzOnWith 1 (fun μ : ℝ => μ) (Set.uIcc a b) :=
    fun x _ y _ => by simp
  have hid_ac : AbsolutelyContinuousOnInterval (fun μ : ℝ => μ) a b :=
    hid_lip.absolutelyContinuousOnInterval
  -- Product (smul) of two AC functions is AC (Mathlib: AbsolutelyContinuousOnInterval.smul)
  -- Need to bridge: scaledPrimalPath x_lasso = (fun μ => μ) • x_lasso
  have h_prod_ac : AbsolutelyContinuousOnInterval (scaledPrimalPath x_lasso) a b := by
    have h_eq : scaledPrimalPath x_lasso = (fun μ : ℝ => μ) • x_lasso := by
      ext μ; simp [scaledPrimalPath]
    rw [h_eq]
    exact AbsolutelyContinuousOnInterval.smul hid_ac hx_ac
  exact h_prod_ac

/--
The scaled primal path is identically zero for all sufficiently small `μ ≥ 0`.

Informal Proof Outline:
By Lemma 4.10 (`parametric_lcp_unique_small_mu`), there exists a threshold
`μ_0 > 0` such that for `0 ≤ μ < μ_0`, the unique solution to the parametric
LCP is `(0, q(μ))`.
For `μ > 0`, since `x(μ)` minimizes the positive lasso, it corresponds to a
solution of the LCP (by `pos_lasso_is_lcp`). Thus `z(μ) = μ x(μ)` solves
the parametric LCP. By uniqueness, `z(μ) = 0` for `0 < μ < μ_0`.
At `μ = 0`, `z(0) = 0 * x(0) = 0`.
-/
lemma scaled_path_zero_near_zero
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ)
    (x_lasso : ℝ → EuclideanSpace ℝ ι)
    (hdata : ProblemData M r lambda)
    (hx_lasso : ∀ μ > 0, IsPositiveLassoMinimizer M r lambda μ (x_lasso μ)) :
    ∃ μ_0 > 0, ∀ μ ∈ Set.Icc 0 μ_0, scaledPrimalPath x_lasso μ = 0 := by
  sorry

/--
If a function is identically zero near zero and locally absolutely continuous on positive compacts,
then it is locally absolutely continuous on nonnegative compacts.

Informal Proof Outline:
Let the function be zero on `[0, μ_0]`. Being constant, it is absolutely continuous on `[0, μ_0/2]`.
For any compact interval `[a, b] ⊂ [0, ∞)`, we can split it at `μ_0/2`. The function is absolutely
continuous on `[a, μ_0/2]` and on `[μ_0/2, b]` (since the latter is a positive compact).
Gluing them together gives absolute continuity on `[a, b]`.
-/
lemma locally_ac_on_nonnegative_of_zero_near_zero_and_ac_on_positive
    (f : ℝ → EuclideanSpace ℝ ι)
    (hf_pos : LocallyAbsolutelyContinuousOnPositiveCompacts f)
    (hf_zero : ∃ μ_0 > 0, ∀ μ ∈ Set.Icc 0 μ_0, f μ = 0) :
    LocallyAbsolutelyContinuousOnNonnegativeCompacts f := by
  sorry

/-- Regularity bridge used between the public statement of Theorem 3.2 and its
scaled-path energy proof.

On `[a,b] ⊂ (0,∞)`, the product `μ ↦ μ x(μ)` is absolutely continuous because
both factors are. Lemma 4.10 says the positive-Lasso minimizer is zero for all
sufficiently small `μ`, so the scaled path is constant near zero; the two
pieces glue on every `[0,b]`. This is the endpoint argument in Sections
4.5--4.6 of <https://arxiv.org/abs/2509.18766>. Mathlib's supported operations
on absolutely continuous functions are documented at
<https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Function/AbsolutelyContinuous.html>.

Informal Proof Outline:
1. Let `z(μ) = μ x(μ)`. We must show `z` is locally absolutely continuous on `[0, ∞)`.
2. For `μ > 0`, `x(μ)` is locally absolutely continuous (by hypothesis), and `μ ↦ μ`
   is Lipschitz. Thus their product `z(μ)` is locally absolutely continuous on `(0, ∞)`.
3. By Lemma 4.10 (`parametric_lcp_unique_small_mu`), there exists a threshold
   `μ_0 > 0` such that for `0 ≤ μ < μ_0`, the unique solution to the parametric
   LCP is `(0, q(μ))`.
4. For `μ > 0`, since `x(μ)` minimizes the positive lasso, it corresponds to a
   solution of the LCP (by `pos_lasso_is_lcp`). Thus `z(μ) = μ x(μ)` solves
   the parametric LCP.
5. By uniqueness, `z(μ) = 0` for `0 < μ < μ_0`. At `μ = 0`, `z(0) = 0 * x(0) = 0`.
6. Therefore, `z` is identically zero on `[0, μ_0/2]`, making it absolutely
   continuous on that interval.
7. For any compact interval `[a, b] ⊂ [0, ∞)`, we can split it at `μ_0/2`. `z` is
   absolutely continuous on `[a, μ_0/2]` and on `[μ_0/2, b]`, so it is absolutely
   continuous on `[a, b]`.
-/
theorem scaledPrimalPath_regular_of_path_regular
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ)
    (x_lasso : ℝ → EuclideanSpace ℝ ι)
    (hdata : ProblemData M r lambda)
    (hx_lasso : ∀ μ > 0, IsPositiveLassoMinimizer M r lambda μ (x_lasso μ))
    (h_regular : LocallyAbsolutelyContinuousOnPositiveCompacts x_lasso) :
    LocallyAbsolutelyContinuousOnNonnegativeCompacts (scaledPrimalPath x_lasso) := by
  apply locally_ac_on_nonnegative_of_zero_near_zero_and_ac_on_positive
  · exact scaled_path_ac_on_positive x_lasso h_regular
  · exact scaled_path_zero_near_zero M r lambda x_lasso hdata hx_lasso


/--
For `μ > 0`, if `x` minimizes the positive lasso, there exists a dual solution `w` such that
the scaled primal and dual vectors solve the parametric LCP.

Informal Proof Outline:
For `μ > 0`, `x(μ)` satisfies the KKT conditions for the positive lasso, meaning it solves the
standard LCP (`pos_lasso_is_lcp`). By scaling the standard LCP by `μ`, we obtain a solution
to the `parametricLcpQ` LCP. This corresponds to setting `w = μ v` where `v` is the standard dual.
(Source: docs/Lasso.md Section 4.5).
-/
lemma exists_parametric_lcp_solution_for_positive_lasso
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda μ : ℝ)
    (x_lasso : ℝ → EuclideanSpace ℝ ι)
    (hdata : ProblemData M r lambda)
    (hμ : 0 < μ)
    (hx_lasso : IsPositiveLassoMinimizer M r lambda μ (x_lasso μ)) :
    ∃ w : EuclideanSpace ℝ ι, isParametricLCP M r lambda μ (scaledPrimalPath x_lasso μ) w := by
  sorry

/--
At `μ = 0`, the origin and the all-ones vector solve the parametric LCP.

Informal Proof Outline:
At `μ = 0`, `z = 0`. The parametric LCP data is `q(0) = 1 > 0`.
Setting `w = 1` satisfies the LCP since `w ≥ 0`, `z ≥ 0`, and `z^T w = 0`.
(Source: docs/Lasso.md Section 4.5).
-/
lemma exists_parametric_lcp_solution_at_zero
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ)
    (x_lasso : ℝ → EuclideanSpace ℝ ι) :
    ∃ w : EuclideanSpace ℝ ι, isParametricLCP M r lambda 0 (scaledPrimalPath x_lasso 0) w := by
  sorry

/--
Given that `w(μ)` can be constructed piecewise to solve the parametric LCP,
and because the dual solution of an LCP with PSD matrix is unique (`psd_lcp_unique_dual`),
the dual trajectory satisfies the regularity package `ParametricLCPDualRegular`.

(We use `Classical.choose` on the existence lemmas to build `w`).
-/
lemma dual_certificate_regularity
    (M Mdagger : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ)
    (x_lasso : ℝ → EuclideanSpace ℝ ι)
    (w : ℝ → EuclideanSpace ℝ ι)
    (hdata : ProblemData M r lambda)
    (hinverse : IsPSDRangeInverse M Mdagger)
    (hsol : ∀ μ ≥ 0, isParametricLCP M r lambda μ (scaledPrimalPath x_lasso μ) (w μ)) :
    ParametricLCPDualRegular M Mdagger r lambda w := by
  apply parametric_lcp_dual_regular M Mdagger r lambda _ _ hdata hsol _ hinverse
  intros μ _ z1 z2 w1 w2 h1 h2
  exact psd_lcp_unique_dual M hdata.psd (parametricLcpQ r lambda μ) z1 z2 w1 w2 h1 h2
/-- Construct the auxiliary Moore--Penrose/LCP data from the selected positive
Lasso minimizer path.

The KKT conditions for the constrained convex quadratic give the dual slack
`w(μ)` and show that `(μx(μ),w(μ))` solves the parametric LCP. A symmetric PSD
matrix has a PSD Moore--Penrose inverse by diagonalizing it and inverting the
positive eigenvalues; Lemma 4.11 then supplies the regularity package. See
Sections 4.4--4.5 of <https://arxiv.org/abs/2509.18766>, the KKT development in
Boyd--Vandenberghe <https://web.stanford.edu/~boyd/cvxbook/>, and the spectral
construction of the pseudoinverse in <https://arxiv.org/abs/1110.6882>.

Informal Proof Outline:
1. By `exists_psd_range_inverse`, let `Mdagger` be a matrix satisfying
   `IsPSDRangeInverse M Mdagger`.
2. For each `μ > 0`, `lcp_exists_unique_dual` gives a unique dual slack `v(μ)`
   such that `isLCP M (lcpQ r lambda μ) (x(μ)) (v(μ))` holds. Let `w(μ) = μ v(μ)`.
3. For `μ = 0`, set `w(0) = parametricLcpQ r lambda 0 = 1`.
4. Then for all `μ ≥ 0`, `(z(μ), w(μ))` solves the parametric LCP.
5. Because `w(μ)` is the unique dual solution of the parametric LCP, Lemma 4.11
   (`parametric_lcp_dual_regular`) applies and provides the full regularity
   package `ParametricLCPDualRegular M Mdagger r lambda w`.
6. Thus `Mdagger` and `w` witness the existential quantifiers.
-/
theorem exists_dual_certificate_for_positive_path
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ)
    (x_lasso : ℝ → EuclideanSpace ℝ ι)
    (hdata : ProblemData M r lambda)
    (hx_lasso : ∀ μ > 0, IsPositiveLassoMinimizer M r lambda μ (x_lasso μ)) :
    ∃ Mdagger : Matrix ι ι ℝ, ∃ w : ℝ → EuclideanSpace ℝ ι,
      ParametricLCPDualRegular M Mdagger r lambda w ∧
        ∀ μ, 0 ≤ μ →
          isParametricLCP M r lambda μ (scaledPrimalPath x_lasso μ) (w μ) := by
  rcases exists_psd_range_inverse M hdata.psd.symm hdata.psd with ⟨Mdagger, hinverse⟩
  use Mdagger
  -- Construct w piecewise using Classical.choose
  have hw_pos : ∀ μ > 0, ∃ w, isParametricLCP M r lambda μ (scaledPrimalPath x_lasso μ) w :=
    fun μ hμ => exists_parametric_lcp_solution_for_positive_lasso M r lambda μ x_lasso hdata hμ (hx_lasso μ hμ)
  have hw_zero : ∃ w, isParametricLCP M r lambda 0 (scaledPrimalPath x_lasso 0) w :=
    exists_parametric_lcp_solution_at_zero M r lambda x_lasso
  let w : ℝ → EuclideanSpace ℝ ι := fun μ =>
    if hμ : μ > 0 then Classical.choose (hw_pos μ hμ)
    else if μ = 0 then Classical.choose hw_zero
    else 0 -- arbitrary for negative μ
  use w
  have hsol : ∀ μ ≥ 0, isParametricLCP M r lambda μ (scaledPrimalPath x_lasso μ) (w μ) := by
    intro μ hμ
    dsimp [w]
    split_ifs with h_pos h_zero
    · exact Classical.choose_spec (hw_pos μ h_pos)
    · have h_eq : μ = 0 := le_antisymm (not_lt.1 h_pos) hμ
      subst h_eq
      exact Classical.choose_spec hw_zero
    · exfalso
      exact h_zero (le_antisymm (not_lt.1 h_pos) hμ)
  constructor
  · exact dual_certificate_regularity M Mdagger r lambda x_lasso w hdata hinverse hsol
  · exact hsol

/--
Helper lemma: integration of `positive_energy_differential_inequality`.
This uses the FTC and the boundary condition `initial_positive_energy_zero` to conclude
an upper bound on the energy $E^\varepsilon(s)$.

Informal proof: Integrate `positive_energy_differential_inequality` from 0 to $s$.
By FTC and `initial_positive_energy_zero`, the integral evaluates exactly to the energy
at time $s$ scaled by $1 / (1 + s \lambda)$. The right-hand side is bounded by substituting
the uniform bound on $\Delta^\varepsilon(\tau)$ from `positive_path_delta_bound`.
-/
lemma positive_energy_integrated_bound
    (M Mdagger : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ)
    (β : EuclideanSpace ℝ ι)
    (u : ℝ → ℝ → EuclideanSpace ℝ ι)
    (hdata : ProblemData M r lambda) (hβ : NonzeroCoordinates β)
    (hu : ∀ ε > 0, posDlnGradientFlow M r lambda ε β (u ε))
    (x_lasso : ℝ → EuclideanSpace ℝ ι)
    (hx_lasso : ∀ μ > 0, IsPositiveLassoMinimizer M r lambda μ (x_lasso μ))
    (w : ℝ → EuclideanSpace ℝ ι)
    (hdual : ParametricLCPDualRegular M Mdagger r lambda w)
    (hdual_selected : ∀ μ, 0 ≤ μ →
      isParametricLCP M r lambda μ (scaledPrimalPath x_lasso μ) (w μ))
    (h_regular : LocallyAbsolutelyContinuousOnNonnegativeCompacts (scaledPrimalPath x_lasso)) :
    ∃ C > 0, ∀ s > 0, ∀ δ > 0, ∀ᶠ ε in 𝓝[>] 0,
      inner ℝ (w s) (posIntegratedTrajectoryRescaled ε (u ε) s - scaledPrimalPath x_lasso s) +
        pathDelta M (fun ρ => posIntegratedTrajectoryRescaled ε (u ε) ρ)
          (scaledPrimalPath x_lasso) s
      ≤ s^2 * (C * suboptimalityGap lambda s (positiveZDownward x_lasso s) + δ) := by
  sorry

/--
Section 4.6 final estimate: the `Δε` control implies the positive-lasso
objective suboptimality bound of Theorem 3.2.

Informal proof reference: `docs/Lasso.md`, Section 4.6.

Informal Proof Outline:
1. Use `positiveLassoObjective_eq_energy` to rewrite the objective gap
   `Lasso(xε) - Lasso(x)` as `1/s^2 * E^\varepsilon(s)`.
2. Apply `positive_energy_differential_inequality` to bound the derivative of `E^\varepsilon(\tau)`.
3. Integrate this bound from `τ = 0` to `τ = s`.
4. Use `initial_positive_energy_zero` to show that the integral evaluates
   exactly to `E^\varepsilon(s)`.
5. Substitute the integrated `Δ^\varepsilon(τ)` bound from `positive_path_delta_bound`.
6. Conclude the limit bound for `E^\varepsilon(s) / s^2`, which matches
   `suboptimalityGap` as `ε → 0`.
-/
theorem positive_path_energy_bound
    (M Mdagger : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ)
    (β : EuclideanSpace ℝ ι)
    (u : ℝ → ℝ → EuclideanSpace ℝ ι)
    (hdata : ProblemData M r lambda) (hβ : NonzeroCoordinates β)
    (hu : ∀ ε > 0, posDlnGradientFlow M r lambda ε β (u ε))
    (x_lasso : ℝ → EuclideanSpace ℝ ι)
    (hx_lasso : ∀ μ > 0, IsPositiveLassoMinimizer M r lambda μ (x_lasso μ))
    (w : ℝ → EuclideanSpace ℝ ι)
    (hdual : ParametricLCPDualRegular M Mdagger r lambda w)
    (hdual_selected : ∀ μ, 0 ≤ μ →
      isParametricLCP M r lambda μ (scaledPrimalPath x_lasso μ) (w μ))
    (h_regular :
      LocallyAbsolutelyContinuousOnNonnegativeCompacts (scaledPrimalPath x_lasso)) :
    ∃ C > 0, ∀ s > 0, ∀ δ > 0, ∀ᶠ ε in 𝓝[>] 0,
      positiveLassoObjective M r lambda s
        (posAverageTrajectory (u ε) (posTimeFromRescaled ε s))
      ≤ posLassoMin M r lambda s +
        C * suboptimalityGap lambda s (positiveZDownward x_lasso s) + δ := by
  /-
  INFORMAL PROOF. Integrate the uniform-in-`s` delta and energy differential
  inequalities of Section 4.6, use the zero initial energy, and divide by
  `s²`. The constants in Lemmas 4.1--4.11 depend only on the fixed problem
  data and initialization, so one `C` works for every `s > 0`. This is the
  calculation concluding Theorem 3.2 in <https://arxiv.org/abs/2509.18766>;
  the absolute-continuity/FTC step is supported by Mathlib's interval-integral
  API <https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Integral/IntervalIntegral/AbsolutelyContinuousFun.html>.
  -/
  obtain ⟨C, hC_pos, h_energy_bound⟩ := positive_energy_integrated_bound M Mdagger r lambda β u hdata hβ hu x_lasso hx_lasso w hdual hdual_selected h_regular
  use C, hC_pos
  intro s hs δ hδ
  have hs_inv_pos : 0 < s⁻¹ := inv_pos.mpr hs
  have hs2_pos : 0 < s^2 := pow_pos hs 2
  have hs_inv2_pos : 0 < s⁻¹ ^ 2 := pow_pos hs_inv_pos 2
  filter_upwards [h_energy_bound s hs δ hδ] with ε hε
  have hw_eq : matVec M (s⁻¹ • scaledPrimalPath x_lasso s) + lcpQ r lambda s = s⁻¹ • w s := by
    -- From hdual_selected s hs, we have isParametricLCP.
    -- The first condition is exactly what we need, after identifying w(s) with the slack.
    sorry
  have hx_nonneg : Nonnegative (s⁻¹ • scaledPrimalPath x_lasso s) := by
    sorry
  have hxE_nonneg : Nonnegative (s⁻¹ • posIntegratedTrajectoryRescaled ε (u ε) s) := by
    sorry
  have h_obj_gap := positiveLassoObjective_eq_energy M r lambda s hs
    (scaledPrimalPath x_lasso s) (posIntegratedTrajectoryRescaled ε (u ε) s) (w s)
    hx_nonneg hxE_nonneg hw_eq hdata.psd.symm
  -- The definition of pathDelta is exactly the quadratic term with M
  have h_delta_eq : (1 / 2 : ℝ) * inner ℝ (posIntegratedTrajectoryRescaled ε (u ε) s - scaledPrimalPath x_lasso s)
      (matVec M (posIntegratedTrajectoryRescaled ε (u ε) s - scaledPrimalPath x_lasso s)) =
      pathDelta M (fun ρ => posIntegratedTrajectoryRescaled ε (u ε) ρ) (scaledPrimalPath x_lasso) s := by
    rfl
  rw [h_delta_eq] at h_obj_gap
  have h_average_eq : posAverageTrajectory (u ε) (posTimeFromRescaled ε s) =
      s⁻¹ • posIntegratedTrajectoryRescaled ε (u ε) s := by
    sorry
  rw [h_average_eq]
  have h_lasso_min_eq : posLassoMin M r lambda s = positiveLassoObjective M r lambda s (s⁻¹ • scaledPrimalPath x_lasso s) := by
    sorry
  rw [h_lasso_min_eq]
  -- We now have positiveLassoObjective (...) - positiveLassoObjective (...) in h_obj_gap.
  -- Rearranging the inequality:
  -- A - B = s⁻¹ ^ 2 * E
  -- E ≤ s^2 * (C * gap + δ)
  -- So A - B ≤ s⁻¹ ^ 2 * s^2 * (C * gap + δ) = C * gap + δ
  -- So A ≤ B + C * gap + δ
  have h_gap_bound : positiveLassoObjective M r lambda s (s⁻¹ • posIntegratedTrajectoryRescaled ε (u ε) s) -
      positiveLassoObjective M r lambda s (s⁻¹ • scaledPrimalPath x_lasso s)
      ≤ C * suboptimalityGap lambda s (positiveZDownward x_lasso s) + δ := by
    rw [h_obj_gap]
    calc
      s⁻¹ ^ 2 * (inner ℝ (w s) (posIntegratedTrajectoryRescaled ε (u ε) s - scaledPrimalPath x_lasso s) +
          pathDelta M (fun ρ => posIntegratedTrajectoryRescaled ε (u ε) ρ) (scaledPrimalPath x_lasso) s)
        ≤ s⁻¹ ^ 2 * (s^2 * (C * suboptimalityGap lambda s (positiveZDownward x_lasso s) + δ)) := by
        exact mul_le_mul_of_nonneg_left hε hs_inv2_pos.le
      _ = (s⁻¹ ^ 2 * s^2) * (C * suboptimalityGap lambda s (positiveZDownward x_lasso s) + δ) := by
        rw [mul_assoc]
      _ = C * suboptimalityGap lambda s (positiveZDownward x_lasso s) + δ := by
        have h_inv : s⁻¹ ^ 2 * s ^ 2 = 1 := by
          rw [← mul_pow]
          rw [inv_mul_cancel₀ hs.ne']
          exact one_pow 2
        rw [h_inv, one_mul]
  linarith [h_gap_bound]

/-! ## Positive-lasso main theorems -/

/--
Theorem 3.2: an approximate connection to the positive lasso minimum in the
general case.

Informal proof reference: `docs/Lasso.md`, Section 4.6.  This theorem is now
placed after the delta and energy estimates that prove it.
-/
theorem pos_lasso_connection_approx
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ)
    (β : EuclideanSpace ℝ ι)
    (u : ℝ → ℝ → EuclideanSpace ℝ ι)
    (hdata : ProblemData M r lambda) (hβ : NonzeroCoordinates β)
    (hu : ∀ ε > 0, posDlnGradientFlow M r lambda ε β (u ε))
    (x_lasso : ℝ → EuclideanSpace ℝ ι)
    (hx_lasso : ∀ μ > 0, IsPositiveLassoMinimizer M r lambda μ (x_lasso μ))
    (h_regular : LocallyAbsolutelyContinuousOnPositiveCompacts x_lasso) :
    ∃ C > 0, ∀ s > 0, ∀ δ > 0, ∀ᶠ ε in 𝓝[>] 0,
      positiveLassoObjective M r lambda s
        (posAverageTrajectory (u ε) (posTimeFromRescaled ε s))
      ≤ posLassoMin M r lambda s +
        C * suboptimalityGap lambda s (positiveZDownward x_lasso s) + δ := by
  obtain ⟨Mdagger, w, hdual, hdual_selected⟩ := exists_dual_certificate_for_positive_path M r lambda x_lasso hdata hx_lasso
  have h_reg_nonneg : LocallyAbsolutelyContinuousOnNonnegativeCompacts (scaledPrimalPath x_lasso) :=
    scaledPrimalPath_regular_of_path_regular M r lambda x_lasso hdata hx_lasso h_regular
  exact positive_path_energy_bound M Mdagger r lambda β u hdata hβ hu x_lasso hx_lasso w hdual hdual_selected h_reg_nonneg

/--
Lemma 4.12 from `docs/Lasso.md`: under the monotonicity hypothesis of Theorem
3.1, the scaled positive-lasso path has enough compact-interval regularity to
apply Theorem 3.2.

Informal proof reference: Section 4.7, Lemma 4.12. Lemma 4.11 gives local
Lipschitz control of the dual path and hence of the projection of `z(μ)` onto
`Span M`. Complementarity controls the kernel component; monotonicity converts
coordinatewise variation into an `L¹` bound on compact intervals.
-/
theorem monotone_positive_path_regular
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ)
    (x_lasso : ℝ → EuclideanSpace ℝ ι)
    (hdata : ProblemData M r lambda)
    (hx_lasso : ∀ μ > 0, IsPositiveLassoMinimizer M r lambda μ (x_lasso μ))
    (h_monotone : ∀ i, MonotoneOn (fun μ => μ * x_lasso μ i) (Set.Ioi 0)) :
    LocallyAbsolutelyContinuousOnNonnegativeCompacts (scaledPrimalPath x_lasso) := by
  /-
  INFORMAL PROOF. KKT gives the unique dual path attached to `x_lasso`.
  Lemma 4.11 controls the range projection of `z`; complementarity expresses
  the scalar kernel contribution in terms of locally Lipschitz quantities.
  Coordinatewise monotonicity turns its increment into the `ℓ¹` norm of the
  full increment, yielding local Lipschitz continuity of `z`, hence absolute
  continuity. Lemma 4.10 supplies `z=0` near the endpoint. See Lemma 4.12 of
  <https://arxiv.org/abs/2509.18766> and Mathlib's implication
  Lipschitz `⇒` absolutely continuous
  <https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Function/AbsolutelyContinuous.html>.
  -/
  sorry

/--
Theorem 3.1: under monotonicity, the positive average trajectory exactly
connects to the positive lasso minimum.

Informal proof reference: `docs/Lasso.md`, Section 4.7.  Unlike the earlier
skeleton, this statement no longer assumes compact-interval regularity as an
extra hypothesis; that regularity is supplied by `monotone_positive_path_regular`.
-/
theorem pos_lasso_connection_monotone
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ)
    (β : EuclideanSpace ℝ ι)
    (s : ℝ) (hs : 0 < s)
    (u : ℝ → ℝ → EuclideanSpace ℝ ι)
    (hdata : ProblemData M r lambda) (hβ : NonzeroCoordinates β)
    (hu : ∀ ε > 0, posDlnGradientFlow M r lambda ε β (u ε))
    (x_lasso : ℝ → EuclideanSpace ℝ ι)
    (hx_lasso : ∀ μ > 0, IsPositiveLassoMinimizer M r lambda μ (x_lasso μ))
    (h_monotone : ∀ i, MonotoneOn (fun μ => μ * x_lasso μ i) (Set.Ioi 0)) :
    Tendsto
      (fun ε =>
        positiveLassoObjective M r lambda s
          (posAverageTrajectory (u ε) (posTimeFromRescaled ε s)))
      (𝓝[>] 0) (𝓝 (posLassoMin M r lambda s)) := by
  /-
  INFORMAL PROOF. Lemma 4.12 supplies the regularity needed by Theorem 3.2.
  A coordinatewise nondecreasing absolutely continuous `z` has nonnegative
  derivative almost everywhere, so `positiveZDownward x_lasso s = 0`.
  The approximate upper bound therefore has zero error term; feasibility of
  the averaged positive trajectory supplies the matching lower bound. See
  Sections 4.6--4.7 of <https://arxiv.org/abs/2509.18766> and the standard
  a.e.-derivative characterization of absolute continuity
  <https://en.wikipedia.org/wiki/Absolute_continuity>.
  -/
  sorry

/-! ## Section 5: signed-to-positive reductions -/

/-- Positive part of a coordinate vector. -/
noncomputable def coordinatePositivePart (x : EuclideanSpace ℝ ι) :
    EuclideanSpace ℝ ι :=
  euclideanOf (fun i => max (x i) 0)

/-- Negative part of a coordinate vector, as a nonnegative vector. -/
noncomputable def coordinateNegativePart (x : EuclideanSpace ℝ ι) :
    EuclideanSpace ℝ ι :=
  euclideanOf (fun i => max (-(x i)) 0)

/-- Canonical signed-to-positive split `x ↦ (x_+, x_-)`. -/
noncomputable def signedCanonicalSplit (x : EuclideanSpace ℝ ι) :
    EuclideanSpace ℝ (ι ⊕ ι) :=
  (WithLp.equiv 2 _).symm
    (Sum.elim (coordinatePositivePart x) (coordinateNegativePart x))

/-- Local absolute continuity is preserved by the canonical positive/negative
split used in Section 5.

Coordinatewise `max` is Lipschitz, hence composition with an absolutely
continuous scalar path is absolutely continuous; finite products preserve the
property. This is the regularity step in Section 5.2.2 of
<https://arxiv.org/abs/2509.18766>, cross-checked with Mathlib's absolute
continuity API
<https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Function/AbsolutelyContinuous.html>.
-/
theorem signedCanonicalSplit_path_regular
    (x : ℝ → EuclideanSpace ℝ ι)
    (hx : LocallyAbsolutelyContinuousOnPositiveCompacts x) :
    LocallyAbsolutelyContinuousOnPositiveCompacts
      (fun μ => signedCanonicalSplit (x μ)) := by
  sorry

/-- A signed coordinate that is monotone in either direction becomes two
nondecreasing coordinates after the positive/negative split.

Lemma 4.10 makes `z(μ)=μx(μ)` zero near the origin. Thus a nondecreasing
coordinate stays nonnegative, so `zᵢ⁺=zᵢ` and `zᵢ⁻=0`; a nonincreasing
coordinate stays nonpositive, so `zᵢ⁺=0` and `zᵢ⁻=-zᵢ`. In either case both
coordinates of the canonical nonnegative representation are nondecreasing.
This is exactly the reduction in Section 5.2.1 of
<https://arxiv.org/abs/2509.18766>.
-/
theorem signedCanonicalSplit_scaled_monotonicity
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ)
    (x : ℝ → EuclideanSpace ℝ ι)
    (hdata : ProblemData M r lambda)
    (hmin : ∀ μ > 0, IsLassoMinimizer M r lambda μ (x μ))
    (hx : ∀ i,
      MonotoneOn (fun μ => μ * x μ i) (Set.Ioi 0) ∨
        AntitoneOn (fun μ => μ * x μ i) (Set.Ioi 0)) :
    ∀ j : ι ⊕ ι,
      MonotoneOn (fun μ => μ * signedCanonicalSplit (x μ) j) (Set.Ioi 0) := by
  sorry

/-- Difference map `(y_pos, y_neg) ↦ y_pos - y_neg`. -/
noncomputable def splitDifference (y : EuclideanSpace ℝ (ι ⊕ ι)) :
    EuclideanSpace ℝ ι :=
  euclideanOf (fun i => y (Sum.inl i) - y (Sum.inr i))

/-- Coordinatewise complementarity of an arbitrary signed split. -/
def SplitComplementary (y : EuclideanSpace ℝ (ι ⊕ ι)) : Prop :=
  ∀ i : ι, y (Sum.inl i) * y (Sum.inr i) = 0

/-- The signed-to-positive augmentation preserves the standing problem-data
assumptions.

For `y=(y⁺,y⁻)`, the augmented quadratic form is
`⟨y, M̃y⟩ = ⟨y⁺-y⁻, M(y⁺-y⁻)⟩`, hence is nonnegative. If `r=Mq`, then
`(r,-r)=M̃(q,0)`, and the penalty parameter is unchanged. This is the block
calculation in Section 5.1.1 of <https://arxiv.org/abs/2509.18766>, consistent
with the standard PSD characterization by quadratic forms in
Boyd--Vandenberghe <https://web.stanford.edu/~boyd/cvxbook/>.
-/
theorem augmented_problem_data
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ)
    (hdata : ProblemData M r lambda) :
    ProblemData (augmentedMatrix M) (augmentedVector r) lambda := by
  sorry

/--
Lemma 5.1(1), inequality part: any nonnegative split gives an augmented positive
objective no smaller than the signed lasso objective of its difference.

Informal proof reference: `docs/Lasso.md`, Section 5.1.1, Lemma 5.1(1).
-/
lemma lasso_split_objective_le
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda μ : ℝ)
    (y : EuclideanSpace ℝ (ι ⊕ ι)) (hy : Nonnegative y)
    (hpenalty : 0 ≤ lambda + 1 / μ) :
    lassoObjective M r lambda μ (splitDifference y) ≤
      positiveLassoObjective (augmentedMatrix M) (augmentedVector r) lambda μ y := by
  -- Proof sketch (Section 5.1.1, Lemma 5.1(1)):
  -- The signed lasso objective evaluates the L1 norm |x|. The augmented positive objective
  -- evaluates the sum of the positive and negative components (y_pos + y_neg).
  -- By the triangle inequality, |y_pos - y_neg| <= y_pos + y_neg for any nonnegative components.
  -- This makes the signed objective always less than or equal to the augmented positive objective.
  sorry

/--
Lemma 5.1(1), equality criterion: equality holds exactly for complementary
positive and negative parts.

Informal proof reference: `docs/Lasso.md`, Section 5.1.1, Lemma 5.1(1).
-/
lemma lasso_split_objective_eq_iff_complementary
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda μ : ℝ)
    (y : EuclideanSpace ℝ (ι ⊕ ι)) (hy : Nonnegative y)
    (hpenalty : 0 < lambda + 1 / μ) :
    lassoObjective M r lambda μ (splitDifference y) =
        positiveLassoObjective (augmentedMatrix M) (augmentedVector r) lambda μ y ↔
      SplitComplementary y := by
  -- Proof sketch (Section 5.1.1, Lemma 5.1(1)):
  -- Equality in the triangle inequality |y_pos - y_neg| <= y_pos + y_neg holds if and only if
  -- y_pos and y_neg have disjoint support. Since they are nonnegative, this is equivalent
  -- to the complementarity condition y_pos * y_neg = 0 for all coordinates.
  sorry

/--
Canonical objective equality for the split `x = x_+ - x_-`.

Informal proof reference: `docs/Lasso.md`, Section 5.1.1.
-/
lemma lasso_objective_reduction
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda μ : ℝ)
    (x : EuclideanSpace ℝ ι) :
    Nonnegative (signedCanonicalSplit x) ∧
      lassoObjective M r lambda μ x =
        positiveLassoObjective (augmentedMatrix M) (augmentedVector r) lambda μ
          (signedCanonicalSplit x) := by
  constructor
  · -- Nonnegative (signedCanonicalSplit x)
    intro j
    cases j <;>
      simp [signedCanonicalSplit, coordinatePositivePart, coordinateNegativePart, euclideanOf]
  · -- lassoObjective equality
    have h_split : splitDifference (signedCanonicalSplit x) = x := by
      ext i
      change max (x i) 0 - max (-x i) 0 = x i
      rcases le_total 0 (x i) with hpos | hneg
      · rw [max_eq_left hpos, max_eq_right (by linarith)]
        linarith
      · rw [max_eq_right hneg, max_eq_left (by linarith)]
        linarith

    have h_norm :
        ‖(WithLp.equiv 1 (ι → ℝ)).symm x‖ =
          ‖(WithLp.equiv 1 (ι ⊕ ι → ℝ)).symm (signedCanonicalSplit x)‖ := by
      rw [PiLp.norm_eq_of_L1, PiLp.norm_eq_of_L1]
      change (∑ i, ‖x i‖) = ∑ j, ‖signedCanonicalSplit x j‖
      have h_sum_rhs :
          (∑ j : ι ⊕ ι, ‖signedCanonicalSplit x j‖) =
            (∑ i : ι, ‖signedCanonicalSplit x (Sum.inl i)‖) +
              ∑ i : ι, ‖signedCanonicalSplit x (Sum.inr i)‖ := by
        exact Fintype.sum_sum_type _
      rw [h_sum_rhs, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      change ‖x i‖ = ‖max (x i) 0‖ + ‖max (-x i) 0‖
      simp only [Real.norm_eq_abs]
      rcases le_total 0 (x i) with hpos | hneg
      · have hm1 : max (x i) 0 = x i := max_eq_left hpos
        have hm2 : max (-x i) 0 = 0 := max_eq_right (by linarith)
        rw [hm1, hm2, abs_zero, add_zero]
      · have hm1 : max (x i) 0 = 0 := max_eq_right hneg
        have hm2 : max (-x i) 0 = -x i := max_eq_left (by linarith)
        rw [hm1, hm2, abs_zero, zero_add, abs_neg]

    have h_quad : quadraticLoss M r x =
        quadraticLoss (augmentedMatrix M) (augmentedVector r) (signedCanonicalSplit x) := by
      /-
      Expand the block matrix `[M,-M;-M,M]` and vector `[r;-r]`.
      Both expressions reduce to the quadratic loss at `x₊-x₋=x`.
      This is Lemma 5.1 of <https://arxiv.org/abs/2509.18766>.
      -/
      sorry

    rw [positiveLassoObjective, lassoObjective, lassoObjective, h_norm, h_quad]

/--
Lemma 5.1(2): a signed lasso minimizer gives an augmented positive-lasso
minimizer via the canonical split.

Informal proof reference: `docs/Lasso.md`, Section 5.1.1, Lemma 5.1(2).
-/
lemma lasso_minimizer_to_augmented_positive_minimizer
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda μ : ℝ)
    (x : EuclideanSpace ℝ ι)
    (hpenalty : 0 ≤ lambda + 1 / μ)
    (hx : IsLassoMinimizer M r lambda μ x) :
    IsPositiveLassoMinimizer (augmentedMatrix M) (augmentedVector r) lambda μ
      (signedCanonicalSplit x) := by
  -- Proof sketch (Section 5.1.1, Lemma 5.1(2)):
  -- If x minimizes the signed lasso objective, its canonical split minimizes the augmented
  -- positive objective. Any other positive split y can be mapped to a signed vector y_pos - y_neg,
  -- whose signed objective is ≤ the positive objective of y. Since x is the global minimum,
  -- the canonical split of x must achieve the absolute minimum of the augmented problem.
  sorry

/--
Lemma 5.1(3): equality of the signed lasso minimum and the augmented positive
lasso minimum.

Informal proof reference: `docs/Lasso.md`, Section 5.1.1, Lemma 5.1(3).
-/
lemma lasso_min_eq_augmented_pos_lasso_min
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda μ : ℝ)
    (hpenalty : 0 ≤ lambda + 1 / μ) :
    lassoMin M r lambda μ =
      posLassoMin (augmentedMatrix M) (augmentedVector r) lambda μ := by
  -- Proof sketch (Section 5.1.1, Lemma 5.1(3)):
  -- Follows directly from `lasso_minimizer_to_augmented_positive_minimizer` and
  -- `lasso_objective_reduction`. The minimum values of both problems coincide.
  sorry

/-- Initial positive weights associated to signed initialization vectors. -/
noncomputable def signedToPositiveInitialization
    (β γ : EuclideanSpace ℝ ι) : EuclideanSpace ℝ (ι ⊕ ι) :=
  (WithLp.equiv 2 _).symm
    (Sum.elim ((1 / 2 : ℝ) • (β + γ)) ((1 / 2 : ℝ) • (β - γ)))

/--
The pointwise change of variables
`p_pos=(u+v)/2`, `p_neg=(u-v)/2`.
-/
noncomputable def signedToPositiveWeights
    (state : WithLp 2 (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)) :
    EuclideanSpace ℝ (ι ⊕ ι) :=
  let uv := WithLp.equiv 2 _ state
  (WithLp.equiv 2 _).symm
    (Sum.elim ((1 / 2 : ℝ) • (uv.1 + uv.2)) ((1 / 2 : ℝ) • (uv.1 - uv.2)))

/-- `signedToPositiveWeights` bundled as a linear map, so that its derivative along a curve
follows from the chain rule for continuous linear maps
(`ContinuousLinearMap.hasFDerivAt.comp_hasDerivAt`), reused in `dln_dynamics_reduction`. -/
noncomputable def signedToPositiveWeightsLM :
    WithLp 2 (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) →ₗ[ℝ] EuclideanSpace ℝ (ι ⊕ ι) where
  toFun := signedToPositiveWeights
  map_add' := by
    intro s1 s2
    dsimp [signedToPositiveWeights]
    ext j
    cases j with
    | inl i => simp; ring
    | inr i => simp; ring
  map_smul' := by
    intro c s
    dsimp [signedToPositiveWeights]
    ext j
    cases j with
    | inl i => simp [smul_eq_mul]; ring
    | inr i => simp [smul_eq_mul]; ring

/--
Section 5.1.2 of `docs/Lasso.md`: the `u ∘ v` DLN vector field maps, under
`signedToPositiveWeights` and the time-doubling `t ↦ 2t` from the chain rule, to the positive
`u ∘ u` DLN vector field for the augmented system `(augmentedMatrix M, augmentedVector r)`.

Informal proof: write `p_pos = (u+v)/2`, `p_neg = (u-v)/2` for the two `signedToPositiveWeights`
components. By `gradient_posDlnObjective`, `augmentedMatrix_matVec`,
`coordinateSquare_half_add_sub_eq_hadamard`, and the block-vector components
`augmentedVector_apply_inl/inr`, the positive vector field at `signedToPositiveWeights state`
evaluates, coordinatewise in `j = inl i` and `j = inr i`, to
`-(u_i+v_i)(D_i+lambda)` and `(u_i-v_i)(D_i-lambda)` respectively, where
`D = matVec M (hadamard u v) - r`. Comparing with `dlnVectorField_eq`'s explicit formula for
`-(∇_u, ∇_v) dlnObjective` shows these are exactly `2 p_pos`/`2 p_neg` applied to that same pair,
i.e. the two sides agree after scaling by 2 (the chain-rule factor from `t ↦ 2t`).
-/
lemma posDlnVectorField_signedToPositiveWeights_eq
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ) (hM : M.IsSymm)
    (t t' : ℝ) (state : WithLp 2 (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)) :
    (2 : ℝ) • signedToPositiveWeights (dlnVectorField M r lambda t state) =
      posDlnVectorField (augmentedMatrix M) (augmentedVector r) lambda t'
        (signedToPositiveWeights state) := by
  set u := (WithLp.equiv 2 (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) state).1
  set v := (WithLp.equiv 2 (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) state).2
  set ppos := (1 / 2 : ℝ) • (u + v) with hppos
  set pneg := (1 / 2 : ℝ) • (u - v) with hpneg
  have hstw : signedToPositiveWeights state = euclideanOf (Sum.elim ppos pneg) := rfl
  rw [hstw]
  dsimp only [posDlnVectorField]
  rw [(hasGradientAt_posDlnObjective (augmentedMatrix M) (augmentedVector r) lambda
    (augmentedMatrix_isSymm M hM) (euclideanOf (Sum.elim ppos pneg))).gradient]
  rw [coordinateSquare_sumElim, augmentedMatrix_matVec]
  have hdiff : matVec M (coordinateSquare ppos) - matVec M (coordinateSquare pneg) =
      matVec M (hadamard u v) := by
    rw [← matVec_sub, coordinateSquare_half_add_sub_eq_hadamard]
  dsimp only [dlnVectorField]
  rw [(hasGradientAt_dlnObjective_left M r lambda hM u v).gradient,
      (hasGradientAt_dlnObjective_right M r lambda hM u v).gradient]
  ext j
  cases j with
  | inl i =>
    simp [signedToPositiveWeights, euclideanOf, hadamard, augmentedVector_apply_inl]
    have hbridge : (WithLp.toLp 2 fun i : ι => u.ofLp i * v.ofLp i) = hadamard u v := rfl
    rw [hbridge]
    have hd :
        (matVec M (coordinateSquare ppos)).ofLp i - (matVec M (coordinateSquare pneg)).ofLp i =
          (matVec M (hadamard u v)).ofLp i := by
      have h := hdiff
      apply_fun (fun x => x.ofLp i) at h
      simpa using h
    have hppos_val : ppos.ofLp i = 2⁻¹ * u.ofLp i + 2⁻¹ * v.ofLp i := by
      simp [hppos, smul_eq_mul]
    rw [hppos_val]
    linear_combination (u.ofLp i + v.ofLp i) * hd
  | inr i =>
    simp [signedToPositiveWeights, euclideanOf, hadamard, augmentedVector_apply_inr]
    have hbridge : (WithLp.toLp 2 fun i : ι => u.ofLp i * v.ofLp i) = hadamard u v := rfl
    rw [hbridge]
    have hd :
        (matVec M (coordinateSquare ppos)).ofLp i - (matVec M (coordinateSquare pneg)).ofLp i =
          (matVec M (hadamard u v)).ofLp i := by
      have h := hdiff
      apply_fun (fun x => x.ofLp i) at h
      simpa using h
    have hpneg_val : pneg.ofLp i = 2⁻¹ * u.ofLp i - 2⁻¹ * v.ofLp i := by
      simp [hpneg, smul_eq_mul]; ring
    rw [hpneg_val]
    linear_combination (v.ofLp i - u.ofLp i) * hd

omit [Fintype ι] in
/-- Coordinatewise components of the signed-to-positive initialization. -/
lemma signedToPositiveInitialization_apply_inl (β γ : EuclideanSpace ℝ ι) (i : ι) :
    signedToPositiveInitialization β γ (Sum.inl i) = (1 / 2 : ℝ) * (β i + γ i) := by
  simp [signedToPositiveInitialization]; ring

omit [Fintype ι] in
lemma signedToPositiveInitialization_apply_inr (β γ : EuclideanSpace ℝ ι) (i : ι) :
    signedToPositiveInitialization β γ (Sum.inr i) = (1 / 2 : ℝ) * (β i - γ i) := by
  simp [signedToPositiveInitialization]

/--
Algebraic identity behind Section 5.1.2:
`u ∘ v = p_pos^2 - p_neg^2`.

Informal proof reference: `docs/Lasso.md`, Section 5.1.2.
-/
lemma signed_effective_eq_split_positive_effective
    (state : WithLp 2 (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)) :
    effectiveParameter (fun _ => state) 0 =
      splitDifference (coordinateSquare (signedToPositiveWeights state)) := by
  -- Proof sketch (Section 5.1.2):
  -- Algebraic identity: p_pos = (u+v)/2 and p_neg = (u-v)/2.
  -- Therefore, p_pos^2 - p_neg^2 = ((u+v)^2 - (u-v)^2) / 4 = 4uv / 4 = uv.
  -- This exactly matches the effective parameter `u ∘ v`.
  sorry

/--
Time-averaged version of the signed-to-positive effective-parameter identity.

Informal proof reference: `docs/Lasso.md`, Section 5.2.
-/
lemma signed_average_eq_split_positive_average
    (w : ℝ → WithLp 2 (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)) (t : ℝ) :
    averageTrajectory w t =
      splitDifference
        (posAverageTrajectory
          (fun τ => signedToPositiveWeights (w (2 * τ))) ((1 / 2 : ℝ) * t)) := by
  -- Proof sketch (Section 5.2):
  -- This follows by integrating the pointwise identity
  -- `signed_effective_eq_split_positive_effective` over time. The time scaling factor of two
  -- accounts for the chain rule in the squared parameterization.
  sorry

/--
Section 5.1.2: reduction of dynamics in the `u ∘ v` case to the `u ∘ u` case.

Informal proof reference: `docs/Lasso.md`, Section 5.1.2.  The positive
trajectory is explicitly `τ ↦ signedToPositiveWeights (wᵋ(2τ))`.

Informal proof: `dlnGradientFlow` gives `HasDerivAt (w ε) (dlnVectorField M r lambda t ((w ε) t)) t`
for every `t`. Composing `t ↦ 2τ` (chain rule, `HasDerivAt.scomp`) with the linear map
`signedToPositiveWeightsLM` (`ContinuousLinearMap.hasFDerivAt.comp_hasDerivAt`) shows
`τ ↦ signedToPositiveWeights ((w ε)(2τ))` has derivative
`signedToPositiveWeights (2 • dlnVectorField M r lambda (2τ) ((w ε)(2τ)))` at `τ`, and this
equals `posDlnVectorField (augmentedMatrix M) (augmentedVector r) lambda τ
(signedToPositiveWeights ((w ε)(2τ)))` by `posDlnVectorField_signedToPositiveWeights_eq`. The
initial condition and `C¹` regularity transfer along the same chain-rule composition; the
initialization identity is the pointwise algebraic computation `signedToPositiveWeights
((WithLp.equiv 2 _).symm (√ε•β, √ε•γ)) = √ε • signedToPositiveInitialization β γ`.
-/
lemma dln_dynamics_reduction
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ)
    (hdata : ProblemData M r lambda)
    (β γ : EuclideanSpace ℝ ι)
    (w : ℝ → ℝ → WithLp 2 (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)) :
    ∀ ε > 0, dlnGradientFlow M r lambda ε β γ (w ε) →
      posDlnGradientFlow (augmentedMatrix M) (augmentedVector r) lambda ε
        (signedToPositiveInitialization β γ)
        (fun τ => signedToPositiveWeights ((w ε) (2 * τ))) := by
  have hM : M.IsSymm := hdata.psd.get_symm
  intro ε _hε hw
  refine ⟨?_, ?_, ?_⟩
  · -- init
    have h0 := hw.init
    simp only [mul_zero]
    rw [h0]
    dsimp [signedToPositiveWeights, signedToPositiveInitialization]
    ext j
    cases j with
    | inl i => simp [smul_eq_mul]; ring
    | inr i => simp [smul_eq_mul]; ring
  · -- cont_diff
    have h1 : ContDiff ℝ 1 (fun τ : ℝ => (w ε) (2 * τ)) :=
      hw.cont_diff.comp (contDiff_const.mul contDiff_id)
    exact signedToPositiveWeightsLM.toContinuousLinearMap.contDiff.comp h1
  · -- ode
    intro τ
    have hg : HasDerivAt (fun τ' : ℝ => 2 * τ') 2 τ := by
      simpa using (hasDerivAt_id τ).const_mul (2 : ℝ)
    have hscaled := (hw.ode (2 * τ)).scomp τ hg
    have hderiv :=
      signedToPositiveWeightsLM.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt τ hscaled
    have hderiv' : HasDerivAt (fun τ' => signedToPositiveWeights ((w ε) (2 * τ')))
        (signedToPositiveWeights ((2 : ℝ) • dlnVectorField M r lambda (2 * τ) ((w ε) (2 * τ))))
        τ :=
      hderiv
    have heq := posDlnVectorField_signedToPositiveWeights_eq M r lambda hM (2 * τ) τ ((w ε) (2 * τ))
    have hsmul : signedToPositiveWeights
        ((2 : ℝ) • dlnVectorField M r lambda (2 * τ) ((w ε) (2 * τ))) =
        (2 : ℝ) • signedToPositiveWeights (dlnVectorField M r lambda (2 * τ) ((w ε) (2 * τ))) :=
      signedToPositiveWeightsLM.map_smul (2 : ℝ) _
    rw [hsmul, heq] at hderiv'
    exact hderiv'

omit [Fintype ι] in
/--
The nondegeneracy condition on signed initialization is exactly nonzero
coordinates for the augmented positive initialization.

Informal proof reference: `docs/Lasso.md`, Section 5.2.
-/
lemma signed_initialization_nondegenerate_iff
    (β γ : EuclideanSpace ℝ ι) :
    NonzeroCoordinates (signedToPositiveInitialization β γ) ↔
      ∀ i, β i ≠ γ i ∧ β i ≠ -γ i := by
  -- Proof sketch (Section 5.2):
  -- The augmented initialization is (u+v)/2 and (u-v)/2.
  -- These components are non-zero if and only if (u+v) ≠ 0 and (u-v) ≠ 0.
  -- This is equivalent to u ≠ -v and u ≠ v.
  constructor
  · intro h i
    have h1 := h (Sum.inl i)
    have h2 := h (Sum.inr i)
    rw [signedToPositiveInitialization_apply_inl] at h1
    rw [signedToPositiveInitialization_apply_inr] at h2
    constructor
    · intro heq; exact h2 (by rw [heq]; ring)
    · intro heq; exact h1 (by rw [heq]; ring)
  · intro h j
    cases j with
    | inl i =>
      rw [signedToPositiveInitialization_apply_inl]
      intro heq
      exact (h i).2 (by linarith)
    | inr i =>
      rw [signedToPositiveInitialization_apply_inr]
      intro heq
      exact (h i).1 (by linarith)

/--
The signed-lasso deviation from monotonicity used in Theorem 2.2.
This matches Eq. (2.3): it applies the negative-variation penalty separately to
the positive and negative parts of `z_i(μ) = μ x_i(μ)`.
-/
noncomputable def signedZDownward (x_lasso : ℝ → EuclideanSpace ℝ ι) (μ : ℝ) :
    ℝ :=
  ∑ i,
    ∫ u in (0 : ℝ)..μ,
      (1 + u) *
        (max 0 (-deriv (fun u' => max (u' * x_lasso u' i) 0) u) +
          max 0 (-deriv (fun u' => max (-(u' * x_lasso u' i)) 0) u))

/-! ## Signed-lasso main theorems -/

/--
Theorem 2.2: an approximate connection to the lasso minimum in the general case.

Informal proof reference: `docs/Lasso.md`, Section 5.2.2.  This declaration now
appears after both `dln_dynamics_reduction` and `lasso_objective_reduction`,
matching the proof sketch.
-/
theorem lasso_connection_approx
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ)
    (β γ : EuclideanSpace ℝ ι)
    (w : ℝ → ℝ → WithLp 2 (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι))
    (hdata : ProblemData M r lambda)
    (hβγ : ∀ i, β i ≠ γ i ∧ β i ≠ -γ i)
    (hw : ∀ ε > 0, dlnGradientFlow M r lambda ε β γ (w ε))
    (x_lasso : ℝ → EuclideanSpace ℝ ι)
    (hx_lasso : ∀ μ > 0, IsLassoMinimizer M r lambda μ (x_lasso μ))
    (h_regular : LocallyAbsolutelyContinuousOnPositiveCompacts x_lasso) :
    ∃ C > 0, ∀ s > 0, ∀ δ > 0, ∀ᶠ ε in 𝓝[>] 0,
      lassoObjective M r lambda s (averageTrajectory (w ε) (timeFromRescaled ε s))
      ≤ lassoMin M r lambda s +
        C * suboptimalityGap lambda s (signedZDownward x_lasso s) + δ := by
  -- Proof sketch (Section 5.2.2 from `docs/Lasso.md`):
  -- By `dln_dynamics_reduction`, the signed dynamics map to positive dynamics
  -- on the augmented system.
  -- By `lasso_objective_reduction`, the lasso objective exactly equals the
  -- positive lasso objective on `augmentedMatrix`.
  -- Thus, applying `pos_lasso_connection_approx` to `u_pos` yields the result.
  sorry

omit [Fintype ι] in
/--
Coordinatewise nonnegativity of the positive-flow time average, for nonnegative
times.  Since `posEffectiveParameter u v` is nonnegative for every `v`
(`posEffectiveParameter_nonnegative`), its average over `[0, t]` is nonnegative
for `t ≥ 0`, by `intervalIntegral.integral_nonneg`.
-/
private lemma posAverageTrajectory_nonneg
    (u : ℝ → EuclideanSpace ℝ ι) (t : ℝ) (ht : 0 ≤ t) :
    Nonnegative (posAverageTrajectory u t) := by
  intro j
  dsimp [posAverageTrajectory, euclideanOf]
  refine mul_nonneg (div_nonneg zero_le_one ht) ?_
  exact intervalIntegral.integral_nonneg ht
    (fun v _ => posEffectiveParameter_nonnegative u v j)

/--
Theorem 2.1: under monotonicity, the signed average trajectory exactly connects
to the lasso minimum.

Informal proof reference: `docs/Lasso.md`, Section 5.2.1.  The earlier skeleton
required an extra `h_regular`; this version follows the paper-level theorem
statement and leaves regularity to the positive monotone theorem plus reductions.

Informal proof (Section 5.2.1): write `x = x_lasso`, `y(μ) = signedCanonicalSplit (x μ)
= (x(μ)₊, x(μ)₋)`.  By Lemma 5.1(2) (`lasso_minimizer_to_augmented_positive_minimizer`),
`y(μ)` minimizes the augmented positive lasso; by the vanishing-near-zero argument for
`z(μ) = μ x(μ)` (`signedCanonicalSplit_scaled_monotonicity`), `μ ↦ μ y(μ)` is
coordinatewise nondecreasing on `(0,∞)`.  The signed-to-positive dynamics reduction
(`dln_dynamics_reduction`) shows `u_pos ε τ = signedToPositiveWeights (w ε (2τ))` is a
positive DLN flow for the augmented data from the augmented initialization
(`signedToPositiveInitialization β γ`, nondegenerate by
`signed_initialization_nondegenerate_iff` since `hβγ` holds).  Applying
`pos_lasso_connection_monotone` to this augmented system gives
`positiveLassoObjective_aug(posAverageTrajectory u_pos ...) → posLassoMin_aug`, and
`posLassoMin_aug = lassoMin` by Lemma 5.1(3) (`lasso_min_eq_augmented_pos_lasso_min`).
Since `averageTrajectory (w ε) = splitDifference (posAverageTrajectory u_pos ...)`
(`signed_average_eq_split_positive_average`, matching the time scalings via
`posTimeFromRescaled_eq_half_timeFromRescaled`), Lemma 5.1(1)
(`lasso_split_objective_le`) bounds the signed objective above by the augmented
positive objective, while `lassoMin ≤` any signed objective value trivially (it is an
infimum).  The signed objective is thus squeezed between the constant `lassoMin` and a
sequence converging to `lassoMin`, giving the result. See Sec. 5.2.1 of
<https://arxiv.org/abs/2509.18766>.
-/
theorem lasso_connection_monotone
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ)
    (β γ : EuclideanSpace ℝ ι)
    (s : ℝ) (hs : 0 < s)
    (w : ℝ → ℝ → WithLp 2 (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι))
    (hdata : ProblemData M r lambda)
    (hβγ : ∀ i, β i ≠ γ i ∧ β i ≠ -γ i)
    (hw : ∀ ε > 0, dlnGradientFlow M r lambda ε β γ (w ε))
    (x_lasso : ℝ → EuclideanSpace ℝ ι)
    (hx_lasso : ∀ μ > 0, IsLassoMinimizer M r lambda μ (x_lasso μ))
    (h_monotone : ∀ i,
      MonotoneOn (fun μ => μ * x_lasso μ i) (Set.Ioi 0) ∨
        AntitoneOn (fun μ => μ * x_lasso μ i) (Set.Ioi 0)) :
    Tendsto
      (fun ε =>
        lassoObjective M r lambda s (averageTrajectory (w ε) (timeFromRescaled ε s)))
      (𝓝[>] 0) (𝓝 (lassoMin M r lambda s)) := by
  set y : ℝ → EuclideanSpace ℝ (ι ⊕ ι) := fun μ => signedCanonicalSplit (x_lasso μ) with hy_def
  set u_pos : ℝ → ℝ → EuclideanSpace ℝ (ι ⊕ ι) :=
    fun ε τ => signedToPositiveWeights ((w ε) (2 * τ)) with hu_pos_def
  have hpenalty : ∀ μ : ℝ, 0 < μ → 0 ≤ lambda + 1 / μ := by
    intro μ hμ
    have h1 := hdata.lambda_nonneg
    have h2 : (0 : ℝ) < 1 / μ := by positivity
    linarith
  have hdata_aug : ProblemData (augmentedMatrix M) (augmentedVector r) lambda :=
    augmented_problem_data M r lambda hdata
  have hβ_aug : NonzeroCoordinates (signedToPositiveInitialization β γ) :=
    (signed_initialization_nondegenerate_iff β γ).mpr hβγ
  have hu_aug : ∀ ε > 0, posDlnGradientFlow (augmentedMatrix M) (augmentedVector r) lambda ε
      (signedToPositiveInitialization β γ) (u_pos ε) :=
    fun ε hε => dln_dynamics_reduction M r lambda hdata β γ w ε hε (hw ε hε)
  have hy_pos : ∀ μ > 0,
      IsPositiveLassoMinimizer (augmentedMatrix M) (augmentedVector r) lambda μ (y μ) :=
    fun μ hμ => lasso_minimizer_to_augmented_positive_minimizer M r lambda μ (x_lasso μ)
      (hpenalty μ hμ) (hx_lasso μ hμ)
  have h_monotone_aug : ∀ j : ι ⊕ ι, MonotoneOn (fun μ => μ * y μ j) (Set.Ioi 0) :=
    signedCanonicalSplit_scaled_monotonicity M r lambda x_lasso hdata hx_lasso h_monotone
  have h_pos_tendsto :=
    pos_lasso_connection_monotone (augmentedMatrix M) (augmentedVector r) lambda
      (signedToPositiveInitialization β γ) s hs u_pos hdata_aug hβ_aug hu_aug y hy_pos
      h_monotone_aug
  have h_min_eq :
      posLassoMin (augmentedMatrix M) (augmentedVector r) lambda s = lassoMin M r lambda s :=
    (lasso_min_eq_augmented_pos_lasso_min M r lambda s (hpenalty s hs)).symm
  rw [h_min_eq] at h_pos_tendsto
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_pos_tendsto ?_ ?_
  · -- `lassoMin M r lambda s` lower-bounds every value of the signed objective, since
    -- `lassoMin` is the infimum of `lassoObjective` and `x_lasso s` witnesses the
    -- boundedness needed to apply `ciInf_le`.
    refine Filter.Eventually.of_forall (fun ε => ?_)
    have hbdd : BddBelow (Set.range (lassoObjective M r lambda s)) :=
      ⟨lassoObjective M r lambda s (x_lasso s), by
        rintro _ ⟨z, rfl⟩
        exact isMinOn_iff.mp (hx_lasso s hs) z (Set.mem_univ z)⟩
    exact ciInf_le hbdd _
  · -- For `ε` small enough that `log(1/ε) > 0`, the signed average trajectory equals the
    -- difference of the augmented positive trajectory's two halves
    -- (`signed_average_eq_split_positive_average`), and Lemma 5.1(1)
    -- (`lasso_split_objective_le`) bounds its signed objective by the augmented positive
    -- objective.
    filter_upwards [show Set.Ioo (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) from by
      rw [mem_nhdsGT_iff_exists_Ioo_subset]
      exact ⟨1, Set.mem_Ioi.mpr one_pos, fun _ hx => hx⟩] with ε hε
    obtain ⟨hε_pos, hε_lt_one⟩ := hε
    have hlog_pos : 0 < Real.log (1 / ε) :=
      Real.log_pos (one_lt_one_div hε_pos hε_lt_one)
    have ht_pos : 0 < posTimeFromRescaled ε s := by
      dsimp [posTimeFromRescaled]
      exact mul_pos (div_pos hs (by norm_num)) hlog_pos
    have hy_nonneg : Nonnegative (posAverageTrajectory (u_pos ε) (posTimeFromRescaled ε s)) :=
      posAverageTrajectory_nonneg (u_pos ε) (posTimeFromRescaled ε s) ht_pos.le
    have heq : averageTrajectory (w ε) (timeFromRescaled ε s) =
        splitDifference (posAverageTrajectory (u_pos ε) (posTimeFromRescaled ε s)) := by
      rw [signed_average_eq_split_positive_average (w ε) (timeFromRescaled ε s),
        ← posTimeFromRescaled_eq_half_timeFromRescaled]
    rw [heq]
    exact lasso_split_objective_le M r lambda s
      (posAverageTrajectory (u_pos ε) (posTimeFromRescaled ε s)) hy_nonneg (hpenalty s hs)

end Lasso

end
