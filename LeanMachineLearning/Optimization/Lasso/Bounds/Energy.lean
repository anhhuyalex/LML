/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.Lasso.Definitions
public import LeanMachineLearning.Optimization.Lasso.Bounds.Delta

/-!
# Energy bounds for positive Lasso dynamics

This file develops the differential and integral energy estimates used to control the positive
Lasso trajectory.
-/

@[expose] public section

namespace Lasso

open Filter Topology
variable {ι : Type*} [Fintype ι]
set_option linter.unusedFintypeInType false

/--
Helper lemma for `positive_energy_differential_inequality`.
Bounds the first term of the product rule derivative.

Informal proof reference: `docs/Lasso.md`, Section 4.6 (text after Eq. (4.15)).
The derivative of `(1 / (1 + τ * lambda)) • w τ` is bounded in norm by `‖r‖_M†`
according to Lemma 4.11 (`ParametricLCPDualRegular`). By Cauchy-Schwarz, its inner
product with `zε τ - z τ` is bounded by `‖r‖_M† * sqrt(2 * Δᵋ(τ))`.
-/
lemma dual_path_derivative_inner_bound
    (M Mdagger : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ)
    (w z zε : ℝ → EuclideanSpace ℝ ι)
    (hM_psd : IsPositiveSemidefinite M)
    (hdual : ParametricLCPDualRegular M Mdagger r lambda w) (τ : ℝ)
    (hτ_nonneg : 0 ≤ τ) :
    inner ℝ (deriv (fun σ => (1 / (1 + σ * lambda)) • w σ) τ) (zε τ - z τ)
    ≤ pseudoInverseSeminorm Mdagger r * Real.sqrt (2 * pathDelta M zε z τ) := by
  -- Let `d` be the derivative of the scaled dual path at time `τ`
  set d := deriv (scaledDualPath lambda w) τ with hd_def
  -- Let `v` be the difference of the approximate and exact trajectories at time `τ`
  set v := zε τ - z τ with hv_def
  -- Symmetry of M follows from PSD
  have hM_symm : M.IsSymm := IsPositiveSemidefinite.get_symm hM_psd
  -- `d` is in the range of `M` (from the dual regularity hypothesis)
  have hd_in_span : InMatrixSpan M d :=
    hdual.scaled_derivative_in_span τ hτ_nonneg
  rcases hd_in_span with ⟨u, hu_eq⟩
  -- `d = M u`
  have hd_eq_Mu : d = matVec M u := hu_eq.symm
  -- The `M†` seminorm of `d` is bounded by that of `r`
  have h_seminorm_bound : pseudoInverseSeminorm Mdagger d ≤ pseudoInverseSeminorm Mdagger r :=
    hdual.scaled_derivative_bound τ hτ_nonneg
  -- Nonnegativity of the M-quadratic forms (from PSD)
  have h_Mu_nonneg : 0 ≤ inner ℝ u (matVec M u) :=
    IsPositiveSemidefinite.get_nonneg hM_psd u
  have h_Mv_nonneg : 0 ≤ inner ℝ v (matVec M v) :=
    IsPositiveSemidefinite.get_nonneg hM_psd v
  -- Cauchy-Schwarz for the M-semi-inner product: |⟨u, M v⟩|² ≤ ⟨u, M u⟩ · ⟨v, M v⟩
  have h_cauchy_sq : inner ℝ u (matVec M v) ^ 2 ≤ inner ℝ u (matVec M u) * inner ℝ v (matVec M v) := by
    set a := inner ℝ u (matVec M u) with ha
    set b := inner ℝ u (matVec M v) with hb
    set c := inner ℝ v (matVec M v) with hc
    have hc_nonneg : 0 ≤ c := by rw [hc]; exact h_Mv_nonneg
    -- For all real `t`, the quadratic `a + 2·b·t + c·t²` is nonnegative
    -- because `⟨u + t·v, M(u + t·v)⟩ ≥ 0` (PSD property)
    have h_quad_nonneg (t : ℝ) : 0 ≤ a + 2 * b * t + c * t ^ 2 := by
      have h_psd := IsPositiveSemidefinite.get_nonneg hM_psd (u + t • v)
      have h_expand : inner ℝ (u + t • v) (matVec M (u + t • v)) = a + 2 * b * t + c * t ^ 2 := by
        dsimp [a, b, c]
        rw [matVec_add, matVec_smul_eq]
        simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
          add_assoc, mul_assoc]
        rw [inner_matVec_comm_of_isSymm M hM_symm v u]
        rw [real_inner_comm (matVec M v) u]
        ring
      rw [← h_expand]
      exact h_psd
    -- Discriminant argument: a + 2bt + ct² ≥ 0 for all t implies b² ≤ a·c
    by_cases hc0 : c = 0
    · -- If c = 0, then ∀t, a + 2bt ≥ 0, forcing b = 0
      have hb0 : b = 0 := by
        by_contra! hb0
        -- Choose t = -(a+1)/(2b), which makes a + 2bt = -1 < 0
        have h_neg : a + 2 * b * (-(a + 1) / (2 * b)) = -1 := by
          field_simp [hb0]
          ring
        have h_ge := h_quad_nonneg (-(a + 1) / (2 * b))
        rw [hc0] at h_ge
        have h_simp : a + 2 * b * (-(a + 1) / (2 * b)) + 0 * (-(a + 1) / (2 * b)) ^ 2 = a + 2 * b * (-(a + 1) / (2 * b)) := by ring
        rw [h_simp] at h_ge
        rw [h_neg] at h_ge
        linarith
      rw [hc0, hb0]
      norm_num
    · -- c ≠ 0, so c > 0 (since c ≥ 0 by PSD)
      have hc_pos : 0 < c := lt_of_le_of_ne hc_nonneg (Ne.symm hc0)
      -- Take t = -b/c and plug into the quadratic
      have h_simplified : a + 2 * b * (-b / c) + c * (-b / c) ^ 2 = a - b ^ 2 / c := by
        field_simp [hc0]
        ring
      have hq := h_quad_nonneg (-b / c)
      rw [h_simplified] at hq
      -- From 0 ≤ a - b²/c, multiply by c > 0 to get a·c ≥ b²
      have hq_mul : 0 ≤ (a - b ^ 2 / c) * c := mul_nonneg hq (le_of_lt hc_pos)
      have h_mul_simp : (a - b ^ 2 / c) * c = a * c - b ^ 2 := by
        calc
          (a - b ^ 2 / c) * c = a * c - (b ^ 2 / c) * c := by ring
          _ = a * c - b ^ 2 := by rw [div_mul_cancel₀ _ hc0]
      rw [h_mul_simp] at hq_mul
      linarith
  -- From the squared Cauchy-Schwarz, derive the non-squared form using square roots
  have h_cauchy_abs : |inner ℝ u (matVec M v)| ≤
      Real.sqrt (inner ℝ u (matVec M u)) * Real.sqrt (inner ℝ v (matVec M v)) := by
    calc
      |inner ℝ u (matVec M v)| = Real.sqrt ((inner ℝ u (matVec M v)) ^ 2) := by
        rw [Real.sqrt_sq_eq_abs]
      _ ≤ Real.sqrt (inner ℝ u (matVec M u) * inner ℝ v (matVec M v)) :=
        Real.sqrt_le_sqrt h_cauchy_sq
      _ = Real.sqrt (inner ℝ u (matVec M u)) * Real.sqrt (inner ℝ v (matVec M v)) := by
        rw [Real.sqrt_mul h_Mu_nonneg]
  -- Relate `inner ℝ d v` to `inner ℝ u (matVec M v)` using `d = M u` and symmetry
  have h_inner_eq : inner ℝ d v = inner ℝ u (matVec M v) := by
    rw [hd_eq_Mu]
    -- inner_matVec_comm_of_isSymm gives inner ℝ u (matVec M v) = inner ℝ (matVec M u) v
    -- we need inner ℝ (matVec M u) v = inner ℝ u (matVec M v), so use the symmetric version
    rw [← inner_matVec_comm_of_isSymm M hM_symm u v]
  -- Relate `pseudoInverseSeminorm Mdagger d` to `sqrt(⟨u, M u⟩)` via the pseudoinverse identity
  have h_seminorm_d_eq : pseudoInverseSeminorm Mdagger d =
      Real.sqrt (inner ℝ u (matVec M u)) := by
    rw [pseudoInverseSeminorm, hd_eq_Mu]
    have h_inner_eq_sq : inner ℝ (matVec M u) (matVec Mdagger (matVec M u)) =
        inner ℝ u (matVec M u) :=
      pseudoInverse_inner_prop M Mdagger hM_symm
        (hdual.inverse_spec.range_inverse) u
    rw [h_inner_eq_sq]
    -- `max 0 (inner ℝ u (matVec M u)) = inner ℝ u (matVec M u)` since it's nonnegative
    have h_max : max 0 (inner ℝ u (matVec M u)) = inner ℝ u (matVec M u) :=
      max_eq_right h_Mu_nonneg
    rw [h_max]
  -- Relate `Real.sqrt (2 * pathDelta M zε z τ)` to `sqrt(⟨v, M v⟩)`
  have h_sqrt_pathDelta : Real.sqrt (2 * pathDelta M zε z τ) =
      Real.sqrt (inner ℝ v (matVec M v)) := by
    rw [pathDelta, matrixSeminormSq, hv_def]
    ring
  -- Bound `inner ℝ d v` by its absolute value
  have h_le_abs : inner ℝ d v ≤ |inner ℝ d v| := by
    by_cases h_nonneg : 0 ≤ inner ℝ d v
    · rw [abs_of_nonneg h_nonneg]
    · rw [abs_of_nonpos (by linarith)]
      linarith
  -- Assemble the main inequality chain
  calc
    inner ℝ d v ≤ |inner ℝ d v| := h_le_abs
    _ = |inner ℝ u (matVec M v)| := by rw [h_inner_eq]
    _ ≤ Real.sqrt (inner ℝ u (matVec M u)) * Real.sqrt (inner ℝ v (matVec M v)) := h_cauchy_abs
    _ = pseudoInverseSeminorm Mdagger d * Real.sqrt (inner ℝ v (matVec M v)) := by
      rw [h_seminorm_d_eq]
    _ = pseudoInverseSeminorm Mdagger d * Real.sqrt (2 * pathDelta M zε z τ) := by
      rw [h_sqrt_pathDelta]
    _ ≤ pseudoInverseSeminorm Mdagger r * Real.sqrt (2 * pathDelta M zε z τ) :=
      mul_le_mul_of_nonneg_right h_seminorm_bound (Real.sqrt_nonneg _)
  -- Finally, `deriv (fun σ => (1 / (1 + σ * lambda)) • w σ) τ = deriv (scaledDualPath lambda w) τ`
  -- by definition of `scaledDualPath`, so the goal `inner ℝ d v ≤ ...` matches


/--
Helper lemma for `positive_energy_differential_inequality`.
Shows that the algebraic sum of the remaining product rule terms is exactly bounded by
the complementarity bound from `positive_delta_differential_inequality`.
We also assert that `C` is at least `‖r‖_M†` so that it can bound both parts simultaneously.

Informal proof reference: `docs/Lasso.md`, Section 4.6, Eq. (4.14) and Eq. (789).
The product rule on `Eᵋ(τ)/(1+τ*λ)` yields terms involving `w(τ)` and `(zε - z)'`, and
the derivative of `Δᵋ(τ)`. Their sum algebraically simplifies to exactly the first four
complementarity defect terms analyzed in Eq. (4.14). These defect terms are uniformly
bounded by `C * [ 1/log(1/ε) * (1 + (z↑)') + (z↓)' ]` as established by the global bound
in `positive_delta_differential_inequality`.
-/
lemma energy_complementarity_bound
    (M Mdagger : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ)
    (β : EuclideanSpace ℝ ι) (s : ℝ) (hs : 0 < s)
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
    ∃ C > 0, pseudoInverseSeminorm Mdagger r ≤ C ∧ ∀ δ > 0, ∀ᶠ ε in 𝓝[>] 0,
      ∀ τ ∈ Set.Icc (0 : ℝ) s,
        deriv
          (fun σ =>
            (1 / (1 + σ * lambda)) *
              (inner ℝ (w σ)
                  (posIntegratedTrajectoryRescaled ε (u ε) σ - scaledPrimalPath x_lasso σ) +
                pathDelta M (fun ρ => posIntegratedTrajectoryRescaled ε (u ε) ρ)
                  (scaledPrimalPath x_lasso) σ)) τ -
        inner ℝ (deriv (fun σ => (1 / (1 + σ * lambda)) • w σ) τ)
          (posIntegratedTrajectoryRescaled ε (u ε) τ - scaledPrimalPath x_lasso τ)
        ≤ C *
          (1 / Real.log (1 / ε) * (1 + deriv (positiveZUpward x_lasso) τ) +
            deriv (positiveZDownward x_lasso) τ) + δ := by
  sorry

/--
Section 4.6 energy differential inequality for
`Eᵋ(s)=<w(s),zᵋ(s)-z(s)>+Δᵋ(s)`.

Informal proof reference: `docs/Lasso.md`, Section 4.6, Eq. (806).
The derivative of the scaled energy expands by the product rule. The first term is
controlled by the dual-path derivative bound from Lemma 4.11 and the Cauchy-Schwarz
inequality (yielding `‖r‖_M† * ‖zᵋ(s) - z(s)‖_M = ‖r‖_M† * sqrt(2 * Δᵋ(s))`).
The remaining terms precisely match the complementarity defects analyzed in Eq. (4.14),
which are bounded globally by `positive_delta_differential_inequality`.
Summing these bounds gives the final total differential inequality.
-/
theorem positive_energy_differential_inequality
    (M Mdagger : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ)
    (β : EuclideanSpace ℝ ι) (s : ℝ) (hs : 0 < s)
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
    ∃ C > 0, ∀ δ > 0, ∀ᶠ ε in 𝓝[>] 0,
      ∀ τ ∈ Set.Icc (0 : ℝ) s,
        deriv
          (fun σ =>
            (1 / (1 + σ * lambda)) *
              (inner ℝ (w σ)
                  (posIntegratedTrajectoryRescaled ε (u ε) σ - scaledPrimalPath x_lasso σ) +
                pathDelta M (fun ρ => posIntegratedTrajectoryRescaled ε (u ε) ρ)
                  (scaledPrimalPath x_lasso) σ)) τ
        ≤ C *
          (Real.sqrt (2 * pathDelta M (fun ρ => posIntegratedTrajectoryRescaled ε (u ε) ρ)
              (scaledPrimalPath x_lasso) τ) +
            1 / Real.log (1 / ε) * (1 + deriv (positiveZUpward x_lasso) τ) +
            deriv (positiveZDownward x_lasso) τ) + δ := by
  obtain ⟨C, hC_pos, hC_ge, h_bound⟩ := energy_complementarity_bound M Mdagger r lambda β s hs u
    hdata hβ hu x_lasso hx_lasso w hdual hdual_selected h_regular
  use C, hC_pos
  intro δ hδ
  filter_upwards [h_bound δ hδ] with ε hε τ hτ
  have h_comp := hε τ hτ
  have h_dual := dual_path_derivative_inner_bound M Mdagger r lambda w
    (scaledPrimalPath x_lasso) (fun ρ => posIntegratedTrajectoryRescaled ε (u ε) ρ)
    hdata.psd hdual τ hτ.1
  let Δ := pathDelta M (fun ρ => posIntegratedTrajectoryRescaled ε (u ε) ρ)
    (scaledPrimalPath x_lasso) τ
  have h_sqrt_nonneg := Real.sqrt_nonneg (2 * Δ)
  have h_dual' : inner ℝ (deriv (fun σ => (1 / (1 + σ * lambda)) • w σ) τ)
      (posIntegratedTrajectoryRescaled ε (u ε) τ - scaledPrimalPath x_lasso τ)
      ≤ C * Real.sqrt (2 * Δ) := by
    calc
      inner ℝ (deriv (fun σ => (1 / (1 + σ * lambda)) • w σ) τ)
        (posIntegratedTrajectoryRescaled ε (u ε) τ - scaledPrimalPath x_lasso τ)
      ≤ pseudoInverseSeminorm Mdagger r * Real.sqrt (2 * Δ) := h_dual
      _ ≤ C * Real.sqrt (2 * Δ) := mul_le_mul_of_nonneg_right hC_ge h_sqrt_nonneg
  have h_sum := add_le_add h_dual' h_comp
  calc
    deriv
      (fun σ =>
        (1 / (1 + σ * lambda)) *
          (inner ℝ (w σ)
              (posIntegratedTrajectoryRescaled ε (u ε) σ - scaledPrimalPath x_lasso σ) +
            pathDelta M (fun ρ => posIntegratedTrajectoryRescaled ε (u ε) ρ)
              (scaledPrimalPath x_lasso) σ)) τ
    = inner ℝ (deriv (fun σ => (1 / (1 + σ * lambda)) • w σ) τ)
        (posIntegratedTrajectoryRescaled ε (u ε) τ - scaledPrimalPath x_lasso τ) +
      (deriv
        (fun σ =>
          (1 / (1 + σ * lambda)) *
            (inner ℝ (w σ)
                (posIntegratedTrajectoryRescaled ε (u ε) σ - scaledPrimalPath x_lasso σ) +
              pathDelta M (fun ρ => posIntegratedTrajectoryRescaled ε (u ε) ρ)
                (scaledPrimalPath x_lasso) σ)) τ -
        inner ℝ (deriv (fun σ => (1 / (1 + σ * lambda)) • w σ) τ)
          (posIntegratedTrajectoryRescaled ε (u ε) τ - scaledPrimalPath x_lasso τ)) := by ring
    _ ≤ C * Real.sqrt (2 * Δ) +
        (C * (1 / Real.log (1 / ε) * (1 + deriv (positiveZUpward x_lasso) τ) +
          deriv (positiveZDownward x_lasso) τ) + δ) := h_sum
    _ = C * (Real.sqrt (2 * Δ) +
          1 / Real.log (1 / ε) * (1 + deriv (positiveZUpward x_lasso) τ) +
          deriv (positiveZDownward x_lasso) τ) + δ := by ring

/--
Helper lemma: The initial positive energy $E^\varepsilon(0)$ is exactly zero.

Informal proof:
The energy is defined as $E^\varepsilon(s) =
\langle w(s), z^\varepsilon(s) - z(s) \rangle + \Delta^\varepsilon(s)$.
At $s=0$, the scaled trajectory $z^\varepsilon(0)$ is $0$ because the unscaled trajectory
$u^\varepsilon(t)$ has initial condition $u^\varepsilon(0) = \sqrt{\varepsilon}\alpha$,
which means $x^\varepsilon(0) = \varepsilon \alpha^2$.
When integrating $x^\varepsilon$ from $0$ to $0$, we get $0$. Thus $z^\varepsilon(0) = 0$.
Similarly, the lasso minimizer at $\mu=0$ is $x(0) = 0$, so $z(0) = 0$.
Since $z^\varepsilon(0) - z(0) = 0$, both the inner product and the $\Delta$ term
(which is $\frac{1}{2}\|0\|_M^2$) vanish.
Therefore, $E^\varepsilon(0) = 0$.
-/
lemma initial_positive_energy_zero
    (M : Matrix ι ι ℝ) (ε : ℝ) (u : ℝ → EuclideanSpace ℝ ι)
    (x_lasso : ℝ → EuclideanSpace ℝ ι) (w : ℝ → EuclideanSpace ℝ ι) :
    inner ℝ (w 0) (posIntegratedTrajectoryRescaled ε u 0 - scaledPrimalPath x_lasso 0) +
      pathDelta M (fun ρ => posIntegratedTrajectoryRescaled ε u ρ)
        (scaledPrimalPath x_lasso) 0 = 0 := by
  have ht0 : posTimeFromRescaled ε 0 = 0 := by dsimp [posTimeFromRescaled]; ring
  have hz_int : posIntegratedTrajectory u 0 = 0 := by
    ext i; simp [posIntegratedTrajectory, euclideanOf]
  have h_diff_zero : posIntegratedTrajectoryRescaled ε u 0 - scaledPrimalPath x_lasso 0 = 0 := by
    simp [posIntegratedTrajectoryRescaled, scaledPrimalPath, ht0, hz_int]
  rw [h_diff_zero, inner_zero_right, zero_add]
  exact pathDelta_zero M ε u x_lasso

/--
Helper lemma: The positive lasso objective gap is exactly $1/s^2$ times
the energy $E^\varepsilon(s)$.

Informal proof reference: `docs/Lasso.md`, Eq. (782).
By the second-order Taylor expansion of the quadratic function $g_s(x) = \operatorname{Lasso}(x, s)$
over the non-negative orthant (where $\|x\|_1 = \langle \mathbb{1}, x \rangle$), we have:
$g_s(x) - g_s(y) = \langle \nabla g_s(y), x - y \rangle + \frac{1}{2}\|x - y\|_M^2$.
At the minimizer $y = x(s) = z(s)/s$, the gradient is $\nabla g_s(x(s)) = v(s) = w(s)/s$.
Substituting $x = \bar{x}^\varepsilon(s) = z^\varepsilon(s)/s$, the objective difference becomes:
$\frac{1}{s^2} \left[ \langle w(s), z^\varepsilon(s) - z(s) \rangle +
  \frac{1}{2}\|z^\varepsilon(s) - z(s)\|_M^2 \right]$,
which is exactly $\frac{1}{s^2} E^\varepsilon(s)$.
To formally prove this in Lean, apply `positiveLassoObjective_eq` to both $x$ and $y$,
subtract them, and use `quadratic_expansion` from `LCP.lean` to group the quadratic forms.
-/
lemma positiveLassoObjective_eq_energy
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ) (s : ℝ) (_hs : 0 < s)
    (z zε : EuclideanSpace ℝ ι) (w : EuclideanSpace ℝ ι)
    (hx_nonneg : Nonnegative (s⁻¹ • z)) (hxE_nonneg : Nonnegative (s⁻¹ • zε))
    (hw_eq : matVec M (s⁻¹ • z) + lcpQ r lambda s = s⁻¹ • w)
    (hM_symm : M.IsSymm) :
    positiveLassoObjective M r lambda s (s⁻¹ • zε) - positiveLassoObjective M r lambda s (s⁻¹ • z) =
      s⁻¹ ^ 2 * (inner ℝ w (zε - z) + (1 / 2 : ℝ) * inner ℝ (zε - z) (matVec M (zε - z))) := by
  rw [positiveLassoObjective_eq M r lambda s (s⁻¹ • zε) hxE_nonneg,
    positiveLassoObjective_eq M r lambda s (s⁻¹ • z) hx_nonneg,
    quadratic_expansion M (lcpQ r lambda s) (s⁻¹ • z) (s⁻¹ • zε) hM_symm, hw_eq]
  have h_sub : s⁻¹ • zε - s⁻¹ • z = s⁻¹ • (zε - z) := (smul_sub s⁻¹ zε z).symm
  rw [h_sub, matVec_smul_eq, real_inner_smul_left, real_inner_smul_left, real_inner_smul_right,
    real_inner_smul_right]
  ring

end Lasso
