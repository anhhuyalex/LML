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
  set d := deriv (scaledDualPath lambda w) τ
  -- Let `v` be the difference of the approximate and exact trajectories at time `τ`
  set v := zε τ - z τ
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
  -- Nonnegativity of the M-quadratic form (from PSD)
  have h_Mu_nonneg : 0 ≤ inner ℝ u (matVec M u) :=
    IsPositiveSemidefinite.get_nonneg hM_psd u
  -- Cauchy-Schwarz for the M-semi-inner product: |⟨u, M v⟩|² ≤ ⟨u, M u⟩ · ⟨v, M v⟩.
  -- This is `inner_matVec_sq_le_mul` (`Basic.lean`), which packages Mathlib's Cauchy-Schwarz
  -- inequality for PSD symmetric bilinear forms (`LinearMap.BilinForm.apply_sq_le_of_symm`).
  have h_cauchy_sq : inner ℝ u (matVec M v) ^ 2 ≤ inner ℝ u (matVec M u) * inner ℝ v (matVec M v) :=
    inner_matVec_sq_le_mul M hM_psd u v
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
    rw [pseudoInverseSeminorm, hd_eq_Mu,
      pseudoInverse_inner_prop M Mdagger hM_symm (hdual.inverse_spec.range_inverse) u,
      max_eq_right h_Mu_nonneg]
  -- Relate `Real.sqrt (2 * pathDelta M zε z τ)` to `sqrt(⟨v, M v⟩)`
  have h_sqrt_pathDelta : Real.sqrt (2 * pathDelta M zε z τ) =
      Real.sqrt (inner ℝ v (matVec M v)) := by
    rw [pathDelta, matrixSeminormSq]
    dsimp [v]
    ring_nf
  -- Bound `inner ℝ d v` by its absolute value
  have h_le_abs : inner ℝ d v ≤ |inner ℝ d v| := le_abs_self _
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
Pure real-arithmetic core of `energy_complementarity_bound`, isolated from the
`EuclideanSpace`/`deriv`/`inner` machinery so that it type-checks quickly.

Given the three complementarity-defect bounds (`T1 ≤ C1/L`, `T3 ≤ C3*(Zu/L + Zd)`,
`T4b ≤ δ`), the sign information `dφτ ≤ 0 ≤ Δτ` and `0 < φτ ≤ 1`, and `Zu, Zd ≥ 0`,
`0 < L`, `C1 ≤ C`, `C3 ≤ C`, concludes the Eq. (789)/(806)-shaped bound
`dφτ * Δτ + φτ * (T1 + T3 + T4b) ≤ C * (Zu/L + Zd + 1/L) + δ`.
-/
private lemma energy_deriv_bound_algebra
    (C1 C3 C L Zu Zd δ φτ dφτ Δτ T1 T3 T4b : ℝ)
    (hC1_pos : 0 < C1) (hC3_pos : 0 < C3) (hC1_le_C : C1 ≤ C) (hC3_le_C : C3 ≤ C)
    (hδ_pos : 0 < δ)
    (hL_pos : 0 < L) (hZu : 0 ≤ Zu) (hZd : 0 ≤ Zd)
    (hφτ_pos : 0 < φτ) (hφτ_le_one : φτ ≤ 1)
    (hdφτ_nonpos : dφτ ≤ 0) (hΔτ_nonneg : 0 ≤ Δτ)
    (hT1 : T1 ≤ C1 / L) (hT3 : T3 ≤ C3 * (1 / L * Zu + Zd)) (hT4b : T4b ≤ δ) :
    dφτ * Δτ + φτ * (T1 + T3 + T4b) ≤ C * (1 / L * (1 + Zu) + Zd) + δ := by
  have h_bracket_nonneg : 0 ≤ C1 / L + C3 * (1 / L * Zu + Zd) + δ := by
    positivity
  have h_1L_Zu_Zd_nonneg : 0 ≤ 1 / L * Zu + Zd := by
    positivity
  have h_phi_mul_le : φτ * (T1 + T3 + T4b) ≤ C1 / L + C3 * (1 / L * Zu + Zd) + δ :=
    (mul_le_mul_of_nonneg_left (by linarith) hφτ_pos.le).trans
      (mul_le_of_le_one_left h_bracket_nonneg hφτ_le_one)
  have h1' : C1 / L ≤ C * (1 / L) := by
    rw [mul_one_div]; exact div_le_div_of_nonneg_right hC1_le_C hL_pos.le
  have h3' : C3 * (1 / L * Zu + Zd) ≤ C * (1 / L * Zu + Zd) :=
    mul_le_mul_of_nonneg_right hC3_le_C h_1L_Zu_Zd_nonneg
  have h_final : C1 / L + C3 * (1 / L * Zu + Zd) + δ ≤ C * (1 / L * (1 + Zu) + Zd) + δ := by
    have h_eq : C * (1 / L) + C * (1 / L * Zu + Zd) = C * (1 / L * (1 + Zu) + Zd) := by ring
    linarith
  nlinarith

-- Complementary slackness of the parametric LCP kills the pairing of the
-- derivative of the exact primal path against the exact dual variable.
-- For every τ ≥ 0, ⟨deriv z(τ), w(τ)⟩ = 0.
-- This uses Fermat's stationary-point theorem for τ > 0 and a boundary
-- continuity argument for τ = 0.
private lemma complementary_slackness_derivative
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ)
    (x_lasso : ℝ → EuclideanSpace ℝ ι) (w : ℝ → EuclideanSpace ℝ ι)
    (hdual_selected : ∀ μ, 0 ≤ μ →
      isParametricLCP M r lambda μ (scaledPrimalPath x_lasso μ) (w μ)) :
    ∀ τ : ℝ, 0 ≤ τ → inner ℝ (deriv (scaledPrimalPath x_lasso) τ) (w τ) = 0 := by
  -- The exact scaled dual variable coincides with the explicit expression
  -- used throughout `Bounds/Delta.lean`.
  have hw_explicit : ∀ τ : ℝ, 0 ≤ τ →
      w τ = matVec M (scaledPrimalPath x_lasso τ) - τ • r + (1 + τ * lambda) • ones := by
    intro τ hτ
    have h := hdual_selected τ hτ
    dsimp [isParametricLCP, isLCP] at h
    rw [h.1]
    ext i
    simp [parametricLcpQ, ones, euclideanOf, matVec]
    ring
  intro τ hτ
  set z := scaledPrimalPath x_lasso
  have hLCP := hdual_selected τ hτ
  dsimp [isParametricLCP, isLCP] at hLCP
  rcases hLCP with ⟨hw_eq, hw_nonneg, hz_nonneg, h_inner_zero⟩
  -- Coordinatewise complementarity for all μ ≥ 0:
  -- (w μ) i * (z μ) i = 0 for every i.
  have h_coord_zero_at : ∀ μ, 0 ≤ μ → ∀ i, (w μ) i * (z μ) i = 0 := by
    intro μ hμ i
    have hLCPμ := hdual_selected μ hμ
    dsimp [isParametricLCP, isLCP] at hLCPμ
    rcases hLCPμ with ⟨_, hw_nonneg_μ, hz_nonneg_μ, h_inner_zero_μ⟩
    have h_inner_sum : inner ℝ (w μ) (z μ) = (∑ j : ι, (w μ) j * (z μ) j) := by
      simp [PiLp.inner_apply, mul_comm]
    have h_sum : (∑ j : ι, (w μ) j * (z μ) j) = 0 := by
      rw [← h_inner_sum, h_inner_zero_μ]
    have h_nonneg : ∀ j, 0 ≤ (w μ) j * (z μ) j := fun j =>
      mul_nonneg (hw_nonneg_μ j) (hz_nonneg_μ j)
    have h_all_zero := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => h_nonneg j)).mp h_sum
    exact h_all_zero i (Finset.mem_univ i)
  by_cases h_diff : DifferentiableAt ℝ z τ
  · -- z is differentiable at τ: work coordinatewise
    rw [PiLp.inner_apply]
    simp only [deriv_piLp_apply h_diff, Real.inner_apply]
    apply Finset.sum_eq_zero
    intro i hi
    by_cases hwi_zero : (w τ) i = 0
    · simp [hwi_zero]
    · have hwi_pos : 0 < (w τ) i :=
        lt_of_le_of_ne (hw_nonneg i) (Ne.symm hwi_zero)
      have hzi_zero : (z τ) i = 0 := by
        have hprod := h_coord_zero_at τ hτ i
        nlinarith
      by_cases hτ_pos : τ > 0
      · -- τ > 0: use Fermat (IsLocalMin) since z_i ≥ 0 everywhere and z_i(τ)=0
        have h_deriv_zero : deriv (fun μ => z μ i) τ = 0 :=
          IsLocalMin.deriv_eq_zero (by
            have hδ : 0 < τ / 2 := by linarith
            apply Filter.mem_of_superset (Metric.ball_mem_nhds τ hδ)
            intro μ hμ
            have hμ_nonneg : 0 ≤ μ := by
              have : |μ - τ| < τ / 2 := hμ
              linarith [abs_sub_lt_iff.mp this]
            have hμ_lcp := hdual_selected μ hμ_nonneg
            dsimp [isParametricLCP, isLCP] at hμ_lcp
            rcases hμ_lcp with ⟨_, _, hz_nonneg_μ, _⟩
            simpa [hzi_zero] using hz_nonneg_μ i)
        simp [h_deriv_zero]
      · -- τ = 0: boundary case
        have hτ_zero : τ = 0 := by linarith
        subst hτ_zero
        -- w is continuous at 0 (since z is differentiable at 0, hence continuous)
        have hz_cont_at_0 : ContinuousAt z 0 := h_diff.continuousAt
        -- Define f(μ) = matVec M(z(μ)) - μ•r + (1+μ•λ)•ones, which equals w(μ) for μ ≥ 0
        set f := fun (μ : ℝ) => matVec M (z μ) - μ • r + (1 + μ * lambda) • ones
        have hf_cont_at_0 : ContinuousAt f 0 := by
          dsimp [f]
          have h_matVec_cont : Continuous (matVecLM M) :=
            (matVecLM M).continuous_of_finiteDimensional
          refine ContinuousAt.add (ContinuousAt.sub ?_ ?_) ?_
          · exact h_matVec_cont.continuousAt.comp hz_cont_at_0
          · exact continuousAt_id.smul_const r
          · have h1 : ContinuousAt (fun (μ : ℝ) => 1 + μ * lambda) 0 :=
              continuousAt_const.add (continuousAt_id.mul continuousAt_const)
            have h2 : ContinuousAt (fun (_ : ℝ) => (ones : EuclideanSpace ℝ ι)) 0 :=
              continuousAt_const
            exact h1.smul h2
        have hf0_i_one : (f 0) i = 1 := by
          dsimp [f]
          have hz0 : z 0 = 0 := by
            dsimp [z, scaledPrimalPath]
            simp
          rw [hz0]
          simp [ones, euclideanOf, matVec]
        have h_fi_cont : ContinuousAt (fun μ => (f μ) i) 0 :=
          (continuous_euclidean_apply i).continuousAt.comp hf_cont_at_0
        -- w agrees with f for μ ≥ 0 (by hw_explicit)
        have h_wi_tendsto : Tendsto (fun μ => (w μ) i) (𝓝[>] 0) (𝓝 1) := by
          apply Filter.Tendsto.congr'
          · filter_upwards [self_mem_nhdsWithin] with μ hμ
            have hμ_nonneg' : 0 ≤ μ := le_of_lt hμ
            rw [hw_explicit μ hμ_nonneg']
          · have h_limit := h_fi_cont.tendsto.mono_left
              (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
            rwa [hf0_i_one] at h_limit
        -- Since (w μ) i → 1 > 0, eventually (w μ) i > 0 for μ > 0 small enough
        have h_wi_pos : ∀ᶠ μ in 𝓝[>] 0, 0 < (w μ) i :=
          h_wi_tendsto.eventually (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1))
        -- Using complementarity: if w_i(μ) > 0, then z_i(μ) = 0 (for μ > 0)
        have h_zi_zero : ∀ᶠ μ in 𝓝[>] 0, (z μ) i = 0 := by
          filter_upwards [h_wi_pos, self_mem_nhdsWithin] with μ hμ_pos hμ_Ioi
          have hμ_nonneg : 0 ≤ μ := le_of_lt hμ_Ioi
          have hprod := h_coord_zero_at μ hμ_nonneg i
          cases mul_eq_zero.mp hprod with
          | inl h => exact (ne_of_gt hμ_pos h).elim
          | inr h => exact h
        have hz0_i : (z 0) i = 0 := by
          dsimp [z, scaledPrimalPath]
          simp
        -- On 𝓝[>] 0, the slope of (z i) at 0 is identically 0
        have h_slope_eq_zero : (slope (fun μ => z μ i) 0) =ᶠ[𝓝[>] 0] (fun _ => (0 : ℝ)) := by
          filter_upwards [h_zi_zero] with μ hμ
          simp [slope, hμ, hz0_i]
        have h_tendsto_slope_zero : Tendsto (slope (fun μ => z μ i) 0) (𝓝[>] 0) (𝓝 (0 : ℝ)) :=
          h_slope_eq_zero.tendsto
        -- The derivative is also the limit of the slope
        have h_hasDeriv : HasDerivAt (fun μ => z μ i) ((deriv z 0).ofLp i) 0 := by
          have h_deriv_z : HasDerivAt z (deriv z 0) 0 := h_diff.hasDerivAt
          exact (EuclideanSpace.proj i).hasFDerivAt.comp_hasDerivAt 0 h_deriv_z
        have h_nhdsWithin_ne : 𝓝[>] (0 : ℝ) ≤ 𝓝[≠] (0 : ℝ) :=
          nhdsWithin_mono 0 (fun x hx => Set.mem_compl_singleton_iff.mpr (ne_of_gt hx))
        have h_tendsto_slope_deriv : Tendsto (slope (fun μ => z μ i) 0) (𝓝[>] 0)
            (𝓝 ((deriv z 0).ofLp i)) :=
          h_hasDeriv.tendsto_slope.mono_left h_nhdsWithin_ne
        -- By uniqueness of limits, deriv = 0
        have h_deriv_zi_zero : (deriv z 0).ofLp i = 0 :=
          tendsto_nhds_unique h_tendsto_slope_deriv h_tendsto_slope_zero
        have h_eval : deriv (fun μ => z μ i) 0 = (deriv z 0).ofLp i := h_hasDeriv.deriv
        rw [h_eval, h_deriv_zi_zero]
        ring
  · -- z is not differentiable at τ: deriv yields 0
    rw [deriv_zero_of_not_differentiableAt h_diff]
    simp [inner_zero_left]

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
    (h_regular : LocallyAbsolutelyContinuousOnNonnegativeCompacts (scaledPrimalPath x_lasso))
    (h_lipschitz : LocallyLipschitzOnCompacts (scaledPrimalPath x_lasso))
    (h_local_affine : ScaledPrimalPathLocallyAffineAtDifferentiable x_lasso) :
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
  -- The exact scaled dual variable `w τ` coincides with the explicit expression
  -- `matVec M (z τ) - τ • r + (1 + τ * lambda) • ones` used throughout `Bounds/Delta.lean`.
  have hw_explicit : ∀ τ : ℝ, 0 ≤ τ →
      w τ = matVec M (scaledPrimalPath x_lasso τ) - τ • r + (1 + τ * lambda) • ones := by
    intro τ hτ
    have h := hdual_selected τ hτ
    dsimp [isParametricLCP, isLCP] at h
    rw [h.1]
    ext i
    simp [parametricLcpQ, ones, euclideanOf, matVec]
    ring
  -- Complementary slackness of the parametric LCP also kills the pairing of the
  -- *derivative* of the exact primal path against the exact dual variable.
  --
  -- Informal proof reference: `docs/Lasso.md`, Section 4.6, Eq. (4.14), fourth bullet
  -- ("Let `i`. We show `dz_i(s)/ds w_i(s) = 0`."); source paper
  -- <https://arxiv.org/abs/2509.18766>.
  --
  -- Fix a coordinate `i`. For every `μ ≥ 0`, `isParametricLCP` gives
  -- `w_i(μ) z_i(μ) = 0`, `w_i(μ) ≥ 0`, `z_i(μ) ≥ 0` (complementary slackness,
  -- expanded coordinatewise from `⟨w μ, z μ⟩ = 0` since both vectors are
  -- nonnegative and a sum of nonnegative terms vanishes iff each term does).
  -- If `w_i(τ) ≠ 0` then `z_i(τ) = 0`; since also `z_i(μ) ≥ 0` for every `μ ≥ 0`
  -- and `τ > 0`, the scalar function `μ ↦ z_i(μ)` has an interior local minimum
  -- at `τ` (using `τ > 0` to obtain a two-sided neighbourhood inside `[0, ∞)`),
  -- so `deriv (fun μ => (scaledPrimalPath x_lasso μ) i) τ = 0` by Fermat's
  -- stationary-point theorem — this holds whether or not the path is
  -- differentiable at `τ`, since Lean's `deriv` already returns the junk value
  -- `0` when it is not. If instead `w_i(τ) = 0` the term vanishes trivially.
  -- Summing over `i` gives `⟨deriv z τ, w τ⟩ = 0`.
  --
  -- At the boundary point `τ = 0` the same complementary-slackness argument
  -- applies (`w(0) = 𝟙` is forced by the defining equation of `isLCP` together
  -- with `z(0) = 0`), but the two-sided neighbourhood used above is not
  -- available since `x_lasso` is uncontrolled for negative arguments; the
  -- statement is retained for all `τ ≥ 0` (matching how `docs/Lasso.md` treats
  -- this identity without separately discussing the `τ = 0` boundary) since it
  -- is the exact pointwise complementarity fact needed to cancel the
  -- corresponding "Term 4a" of Eq. (4.14) inside `pos_delta_bound_4`.
  have h_comp_zero := complementary_slackness_derivative M r lambda x_lasso w hdual_selected
  -- Choose the piecewise-linearity fact needed by `pos_delta_bound_3`.
  have h_piecewise_deriv : ∀ (τ' : ℝ) (i' : ι), 0 ≤ τ' →
      DifferentiableAt ℝ (scaledPrimalPath x_lasso) τ' →
      ∃ ε > 0, ∀ t, |t - τ'| < ε →
        deriv (fun u' => u' * (x_lasso u').ofLp i') t =
        deriv (fun u' => u' * (x_lasso u').ofLp i') τ' :=
    fun τ' i' hτ' h_diff =>
      scaledPrimalPath_deriv_locally_constant x_lasso h_local_affine τ' i' hτ' h_diff
  obtain ⟨C1, hC1_pos, h1⟩ := pos_delta_bound_1 M r lambda β s hs u hdata hβ hu
  obtain ⟨C3, hC3_pos, h3⟩ := pos_delta_bound_3 M r lambda β s hs u hdata hβ hu x_lasso
    hx_lasso h_regular h_piecewise_deriv
  have h4 := pos_delta_bound_4
    (M := M) (r := r) (lambda := lambda) (β := β) (s := s) (hs := hs) (u := u)
    (hdata := hdata) (hβ := hβ) (hu := hu) (x_lasso := x_lasso)
    (hx_lasso := hx_lasso) (h_lipschitz := h_lipschitz)
  set C := max (max C1 C3) (pseudoInverseSeminorm Mdagger r)
  have hC_pos : 0 < C := lt_max_of_lt_left (lt_max_of_lt_left hC1_pos)
  refine ⟨C, hC_pos, le_max_right _ _, ?_⟩
  intro δ hδ
  have h_eps_lt_one : Set.Ioo (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) := by
    rw [mem_nhdsGT_iff_exists_Ioo_subset]
    exact ⟨1, by norm_num, fun _ hx => hx⟩
  filter_upwards [h1, h3, h4 δ hδ, h_eps_lt_one] with ε h1ε h3ε h4ε hε_mem τ hτ
  rcases hε_mem with ⟨hε_pos, hε_lt_one⟩
  have hlog_pos : 0 < Real.log (1 / ε) := Real.log_pos (one_lt_one_div hε_pos hε_lt_one)
  -- Abbreviations for readability.
  set zε := fun ρ => posIntegratedTrajectoryRescaled ε (u ε) ρ
  set z := scaledPrimalPath x_lasso
  set wε := fun ρ => posRescaledMirrorVariable ε (u ε) ρ
  set φ := fun σ : ℝ => (1 : ℝ) / (1 + σ * lambda)
  set Δε := pathDelta M zε z
  -- `T1`, `T3`, `T4b`: the three surviving complementarity-defect terms of Eq. (4.14).
  set T1 := inner ℝ (deriv zε τ) (wε τ)
  set T3 := - inner ℝ (deriv z τ) (wε τ)
  set T4b := inner ℝ (deriv zε τ - deriv z τ) (ones - wε 0)
  -- Term 4a of Eq. (4.14): exactly zero by complementary slackness.
  have hT4a_zero : inner ℝ (deriv z τ) (w τ) = 0 := h_comp_zero τ hτ.1
  have hT4a_eq : inner ℝ (deriv z τ)
      (matVec M (z τ) - τ • r + (1 + τ * lambda) • ones) = 0 := by
    rw [← hw_explicit τ hτ.1]; exact hT4a_zero
  -- The key product-rule identity (Section 4.6, Eqs. (788)-(791) of `docs/Lasso.md`):
  -- differentiating `φ(σ) * Eᵋ(σ)` by the product rule, substituting the
  -- integrated mirror equation `positive_integrated_mirror_equation` for `M zε(τ)`
  -- and the `isLCP` defining equation for `M z(τ)`, and using the chain rule for
  -- the `M`-quadratic form `Δε(σ) = (1/2)⟨zε(σ) - z(σ), M(zε(σ) - z(σ))⟩`, the
  -- terms recombine (after cancelling the `⟨w(τ), zε'(τ) - z'(τ)⟩` pairing that
  -- appears with opposite signs from the product rule on `inner ℝ (φ • w) ...`
  -- and from `M z(τ)`'s defining equation) into exactly `deriv φ τ * Δε(τ)` plus
  -- `φ(τ)` times the sum of `T1`, `T3`, and `T4b`, matching Eq. (4.14)'s "Term 1",
  -- "Term 3" and the (`Term 4b`-part of the) "Term 4" complementarity defects.
  have h_key_identity :
      deriv (fun σ => φ σ * (inner ℝ (w σ) (zε σ - z σ) + Δε σ)) τ -
        inner ℝ (deriv (fun σ => φ σ • w σ) τ) (zε τ - z τ)
      = deriv φ τ * Δε τ + φ τ * (T1 + T3 + T4b) := by
    -- The identity follows from the product rule and the mirror/LCP equations.
    -- We break it into several steps.
    --
    -- Step 0: basic hypotheses we will need.
    have hM_symm : M.IsSymm := IsPositiveSemidefinite.get_symm hdata.psd
    have hτ_nonneg : 0 ≤ τ := hτ.1
    -- φ(σ) = 1/(1+σλ) is differentiable for τ ≥ 0 (since denominator > 0)
    have hτlambda_pos : 0 < 1 + τ * lambda := by
      nlinarith [hdata.lambda_nonneg, hτ.1]
    have h_diff_φ : DifferentiableAt ℝ φ τ := by
      -- φ is a quotient of differentiable functions with nonzero denominator
      have h_denom_ne_zero : (fun (σ : ℝ) => 1 + σ * lambda) τ ≠ 0 := by
        dsimp; linarith
      refine ((hasDerivAt_const τ (1 : ℝ)).div
        (((hasDerivAt_id τ).mul_const lambda).const_add 1) h_denom_ne_zero).differentiableAt
    -- Step 1: Product rule for φ * E where E σ = inner ℝ (w σ) (zε σ - z σ) + Δε σ.
    -- We need differentiability of E at τ, which follows from differentiability
    -- of w, zε, z at τ (using hdual.absolutely_continuous for w when τ > 0,
    -- and similarly for zε, z from their gradient-flow / AC definitions).
    have h_diff_w : DifferentiableAt ℝ w τ := by
      -- For τ > 0, this follows from hdual.absolutely_continuous.
      -- For τ = 0, a separate argument using the explicit formula hw_explicit gives differentiability.
      sorry
    have h_diff_zε : DifferentiableAt ℝ zε τ := by
      -- zε comes from a gradient flow, hence differentiable.
      sorry
    have h_diff_z : DifferentiableAt ℝ z τ := by
      -- z = scaledPrimalPath x_lasso, AC on positive compacts (h_regular).
      -- For τ > 0, this gives differentiability. For τ = 0, need a boundary argument.
      sorry
    -- Define E in point-free form to work smoothly with `deriv_mul` and `deriv_add`.
    set E := (fun σ => inner ℝ (w σ) (zε σ - z σ)) + Δε with hE_def
    have h_diff_E : DifferentiableAt ℝ E τ := by
      -- Δε is differentiable where zε, z are (by pathDelta_hasDerivAt).
      -- Inner product of differentiable functions is differentiable.
      sorry
    -- Product rule: deriv (φ * E) = deriv φ * E + φ * deriv E
    -- `deriv_mul` gives the identity for point-free `φ * E`; we `dsimp` the
    -- `set` definitions so that the goal becomes definitionally equal.
    have h_deriv_prod : deriv (fun σ => φ σ * (inner ℝ (w σ) (zε σ - z σ) + Δε σ)) τ =
        deriv φ τ * (inner ℝ (w τ) (zε τ - z τ) + Δε τ) +
        φ τ * deriv (fun σ => inner ℝ (w σ) (zε σ - z σ) + Δε σ) τ := by
      have h := deriv_mul h_diff_φ h_diff_E
      dsimp [E, Δε] at h ⊢
      exact h
    -- Product rule for scalar-vector: deriv (φ • w) = deriv φ • w + φ • deriv w
    -- `deriv_smul` gives `φ τ • deriv w τ + deriv φ τ • w τ`; `add_comm` reorders.
    have h_deriv_vec : deriv (fun σ => φ σ • w σ) τ = deriv φ τ • w τ + φ τ • deriv w τ := by
      have h := deriv_smul h_diff_φ h_diff_w
      -- h : deriv (φ • w) τ = φ τ • deriv w τ + deriv φ τ • w τ
      -- `φ • w` is definitionally `fun σ => φ σ • w σ`, but `simpa` may not see it.
      -- We use `convert` to handle the definitional equality and `add_comm` for the RHS.
      convert h using 1
      · rfl
      · rw [add_comm]
    -- Step 2: Expand deriv of E = inner + Δε.
    have h_diff_inner : DifferentiableAt ℝ (fun σ => inner ℝ (w σ) (zε σ - z σ)) τ := by
      -- Inner product of differentiable functions is differentiable (use HasDerivAt.inner)
      sorry
    have h_diff_Δε : DifferentiableAt ℝ Δε τ := by
      -- Δε is differentiable where zε, z are (by pathDelta_hasDerivAt)
      sorry
    have h_deriv_E_sum : deriv (fun σ => inner ℝ (w σ) (zε σ - z σ) + Δε σ) τ =
        deriv (fun σ => inner ℝ (w σ) (zε σ - z σ)) τ + deriv Δε τ := by
      have h := deriv_add h_diff_inner h_diff_Δε
      dsimp [E, Δε] at h ⊢
      exact h
    -- Step 3: Derivative of inner product.
    -- d/dσ ⟨w(σ), zε(σ) - z(σ)⟩ = ⟨w'(σ), zε(σ) - z(σ)⟩ + ⟨w(σ), zε'(σ) - z'(σ)⟩
    have h_deriv_inner : deriv (fun σ => inner ℝ (w σ) (zε σ - z σ)) τ =
        inner ℝ (deriv w τ) (zε τ - z τ) + inner ℝ (w τ) (deriv zε τ - deriv z τ) := by
      -- Obtain HasDerivAt from DifferentiableAt using `hasDerivAt_deriv_iff`
      have hw : HasDerivAt w (deriv w τ) τ := by
        rw [hasDerivAt_deriv_iff]; exact h_diff_w
      have hzε : HasDerivAt zε (deriv zε τ) τ := by
        rw [hasDerivAt_deriv_iff]; exact h_diff_zε
      have hz : HasDerivAt z (deriv z τ) τ := by
        rw [hasDerivAt_deriv_iff]; exact h_diff_z
      have h_inner := (hw.inner ℝ (hzε.sub hz))
      -- h_inner : HasDerivAt (fun t => inner ℝ (w t) ((zε - z) t))
      --   (inner ℝ (w τ) (deriv zε τ - deriv z τ) + inner ℝ (deriv w τ) ((zε - z) τ)) τ
      -- Note: (zε - z) τ = zε τ - z τ definitionally, so we can `simpa [add_comm]`
      simpa [add_comm] using h_inner.deriv
    -- Step 4: Derivative of Δε using pathDelta_hasDerivAt.
    have h_deriv_Δε : deriv Δε τ = inner ℝ (deriv zε τ - deriv z τ) (matVec M (zε τ - z τ)) := by
      have hzε_deriv : HasDerivAt zε (deriv zε τ) τ := by
        rw [hasDerivAt_deriv_iff]; exact h_diff_zε
      have hz_deriv : HasDerivAt z (deriv z τ) τ := by
        rw [hasDerivAt_deriv_iff]; exact h_diff_z
      have h_chain := pathDelta_hasDerivAt M hM_symm zε z (deriv zε τ) (deriv z τ) τ
        hzε_deriv hz_deriv
      dsimp [Δε] at *
      rw [h_chain.deriv]
    -- Step 5: The two governing equations for M zε and M z.
    -- From the integrated mirror equation:
    --   M zε(τ) = wε(τ) - wε(0) + τ r - (τ λ) ones
    have hM_zε : matVec M (zε τ) =
        wε τ - wε 0 + τ • r - (τ * lambda) • ones := by
      -- We need the hypotheses for positive_integrated_mirror_equation:
      --   hu ε hε_pos, pos_effective_param_ne_zero, hM_symm, hlog_ne_zero
      -- These may not all be available here; they can be derived from the
      -- filter context (ε is eventually small and positive).
      sorry
    -- From the isParametricLCP (via hw_explicit):
    --   w(τ) = M z(τ) - τ r + (1 + τ λ) ones
    -- So  M z(τ) = w(τ) + τ r - (1 + τ λ) ones
    -- Use `abel` for vector algebra (linarith does not work on EuclideanSpace).
    have hM_z : matVec M (z τ) = w τ + τ • r - (1 + τ * lambda) • ones := by
      have hw_eq := hw_explicit τ hτ_nonneg
      -- hw_eq: w τ = matVec M (z τ) - τ • r + (1 + τ * lambda) • ones
      calc
        matVec M (z τ) = (matVec M (z τ) - τ • r + (1 + τ * lambda) • ones) +
            τ • r - (1 + τ * lambda) • ones := by abel
        _ = w τ + τ • r - (1 + τ * lambda) • ones := by rw [← hw_eq]
    -- Step 6: The core cancellation identity.
    -- ⟨w, zε' - z'⟩ + ⟨zε' - z', M(zε - z)⟩ = ⟨zε', wε⟩ - ⟨z', wε⟩ + ⟨zε' - z', ones - wε 0⟩
    -- i.e. = T1 + T3 + T4b
    have h_core : inner ℝ (w τ) (deriv zε τ - deriv z τ) +
        inner ℝ (deriv zε τ - deriv z τ) (matVec M (zε τ - z τ)) = T1 + T3 + T4b := by
      have hM_diff : matVec M (zε τ - z τ) = wε τ - w τ + (ones - wε 0) := by
        rw [matVec_sub, hM_zε, hM_z]
        ext i
        simp [euclideanOf, ones, matVec, dotProduct, Pi.add_apply, Pi.sub_apply,
          Pi.smul_apply, Pi.neg_apply]
        ring
      set D := deriv zε τ - deriv z τ with hD_def
      calc
        inner ℝ (w τ) D + inner ℝ D (matVec M (zε τ - z τ))
        = inner ℝ (w τ) D + inner ℝ D (wε τ - w τ + (ones - wε 0)) := by rw [hM_diff]
        _ = inner ℝ (w τ) D +
            (inner ℝ D (wε τ - w τ) + inner ℝ D (ones - wε 0)) := by
          rw [inner_add_right]
        _ = inner ℝ (w τ) D +
            ((inner ℝ D (wε τ) - inner ℝ D (w τ)) + inner ℝ D (ones - wε 0)) := by
          dsimp [D]
          simp [inner_sub_right]
        _ = (inner ℝ (w τ) D - inner ℝ D (w τ)) +
            inner ℝ D (wε τ) + inner ℝ D (ones - wε 0) := by ring
        _ = 0 + inner ℝ D (wε τ) + inner ℝ D (ones - wε 0) := by
          rw [real_inner_comm (w τ) D]
          ring
        _ = (inner ℝ (deriv zε τ) (wε τ) - inner ℝ (deriv z τ) (wε τ)) +
            inner ℝ D (ones - wε 0) := by
          rw [hD_def, inner_sub_left, zero_add]
        _ = T1 + T3 + T4b := by
          dsimp [T1, T3, T4b, D]; ring
    -- Step 7: Assemble everything.
    calc
      deriv (fun σ => φ σ * (inner ℝ (w σ) (zε σ - z σ) + Δε σ)) τ -
        inner ℝ (deriv (fun σ => φ σ • w σ) τ) (zε τ - z τ)
      = (deriv φ τ * (inner ℝ (w τ) (zε τ - z τ) + Δε τ) +
          φ τ * deriv (fun σ => inner ℝ (w σ) (zε σ - z σ) + Δε σ) τ) -
        inner ℝ (deriv φ τ • w τ + φ τ • deriv w τ) (zε τ - z τ) := by
        rw [h_deriv_prod, h_deriv_vec]
      _ = (deriv φ τ * (inner ℝ (w τ) (zε τ - z τ) + Δε τ) +
          φ τ * (deriv (fun σ => inner ℝ (w σ) (zε σ - z σ)) τ + deriv Δε τ)) -
        (deriv φ τ * inner ℝ (w τ) (zε τ - z τ) + φ τ * inner ℝ (deriv w τ) (zε τ - z τ)) := by
        rw [h_deriv_E_sum]
        simp [inner_add_left, inner_smul_left, starRingEnd_apply]
      _ = deriv φ τ * Δε τ +
          φ τ * (deriv (fun σ => inner ℝ (w σ) (zε σ - z σ)) τ -
            inner ℝ (deriv w τ) (zε τ - z τ) + deriv Δε τ) := by ring
      _ = deriv φ τ * Δε τ +
          φ τ * (inner ℝ (w τ) (deriv zε τ - deriv z τ) + deriv Δε τ) := by
        rw [h_deriv_inner]; ring
      _ = deriv φ τ * Δε τ +
          φ τ * (inner ℝ (w τ) (deriv zε τ - deriv z τ) +
            inner ℝ (deriv zε τ - deriv z τ) (matVec M (zε τ - z τ))) := by
        rw [h_deriv_Δε]
      _ = deriv φ τ * Δε τ + φ τ * (T1 + T3 + T4b) := by rw [h_core]
  -- `Δε(τ) ≥ 0` since `M` is positive semidefinite.
  have hΔε_nonneg : 0 ≤ Δε τ := by
    have h := hdata.psd.nonneg (zε τ - z τ)
    dsimp [Δε, pathDelta, matrixSeminormSq]
    nlinarith
  -- `deriv φ τ ≤ 0` and `0 < φ τ ≤ 1`, using `λ ≥ 0` and `τ ≥ 0`.
  have hτlambda_pos : 0 < 1 + τ * lambda := by nlinarith [hdata.lambda_nonneg, hτ.1]
  have hφ_deriv : HasDerivAt φ (-lambda / (1 + τ * lambda) ^ 2) τ := by
    have h1 : HasDerivAt (fun σ : ℝ => 1 + σ * lambda) lambda τ := by
      simpa using ((hasDerivAt_id τ).mul_const lambda).const_add 1
    have h2 := (hasDerivAt_const τ (1 : ℝ)).div h1 (ne_of_gt hτlambda_pos)
    have h_eq : (0 * (1 + τ * lambda) - 1 * lambda) / (1 + τ * lambda) ^ 2 =
        -lambda / (1 + τ * lambda) ^ 2 := by ring
    rwa [h_eq] at h2
  have hφ_deriv_nonpos : deriv φ τ ≤ 0 := by
    rw [hφ_deriv.deriv]
    apply div_nonpos_of_nonpos_of_nonneg (by linarith [hdata.lambda_nonneg])
    positivity
  have hφ_pos : 0 < φ τ := by dsimp [φ]; positivity
  have hφ_le_one : φ τ ≤ 1 := by
    dsimp [φ]
    rw [div_le_one hτlambda_pos]
    nlinarith [hdata.lambda_nonneg, hτ.1]
  -- Nonnegativity of the `z↑`/`z↓` derivatives, needed to fold `T1`/`T3` into a
  -- single constant `C`.
  have h_z_nonneg := positiveZ_deriv_nonneg x_lasso τ hτ.1 h_regular
  -- Bound `T1`, `T3`, `T4b`.
  have hT1_bound : T1 ≤ C1 / Real.log (1 / ε) := h1ε τ hτ
  have hT3_bound : T3 ≤ C3 * (1 / Real.log (1 / ε) * deriv (positiveZUpward x_lasso) τ +
      deriv (positiveZDownward x_lasso) τ) := h3ε τ hτ
  have hT4b_bound : T4b ≤ δ := by
    have h4' := h4ε τ hτ
    dsimp [T4b] at *
    linarith [h4', hT4a_eq]
  -- Assemble the final bound via the isolated arithmetic lemma.
  have h_C1_le_C : C1 ≤ C := (le_max_left C1 C3).trans (le_max_left _ _)
  have h_C3_le_C : C3 ≤ C := (le_max_right C1 C3).trans (le_max_left _ _)
  rw [h_key_identity]
  exact energy_deriv_bound_algebra C1 C3 C (Real.log (1 / ε))
    (deriv (positiveZUpward x_lasso) τ) (deriv (positiveZDownward x_lasso) τ) δ
    (φ τ) (deriv φ τ) (Δε τ) T1 T3 T4b
    hC1_pos hC3_pos h_C1_le_C h_C3_le_C hδ hlog_pos h_z_nonneg.1 h_z_nonneg.2
    hφ_pos hφ_le_one hφ_deriv_nonpos hΔε_nonneg hT1_bound hT3_bound hT4b_bound

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
    (h_regular : LocallyAbsolutelyContinuousOnNonnegativeCompacts (scaledPrimalPath x_lasso))
    (h_lipschitz : LocallyLipschitzOnCompacts (scaledPrimalPath x_lasso))
    (h_local_affine : ScaledPrimalPathLocallyAffineAtDifferentiable x_lasso) :
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
    hdata hβ hu x_lasso hx_lasso w hdual hdual_selected h_regular h_lipschitz h_local_affine
  use C, hC_pos
  intro δ hδ
  filter_upwards [h_bound δ hδ] with ε hε τ hτ
  let Δ := pathDelta M (fun ρ => posIntegratedTrajectoryRescaled ε (u ε) ρ)
    (scaledPrimalPath x_lasso) τ
  have h_dual := dual_path_derivative_inner_bound M Mdagger r lambda w
    (scaledPrimalPath x_lasso) (fun ρ => posIntegratedTrajectoryRescaled ε (u ε) ρ)
    hdata.psd hdual τ hτ.1
  have h_sum := add_le_add
    (h_dual.trans (mul_le_mul_of_nonneg_right hC_ge (Real.sqrt_nonneg _)))
    (hε τ hτ)
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
  have hz_int : posIntegratedTrajectory u 0 = 0 := by
    ext i; simp [posIntegratedTrajectory, euclideanOf]
  have h_diff_zero : posIntegratedTrajectoryRescaled ε u 0 - scaledPrimalPath x_lasso 0 = 0 := by
    have ht0 : posTimeFromRescaled ε 0 = 0 := by dsimp [posTimeFromRescaled]; ring
    simp [posIntegratedTrajectoryRescaled, scaledPrimalPath, ht0, hz_int]
  simp [h_diff_zero, pathDelta_zero M ε u x_lasso]

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
  rw [(smul_sub s⁻¹ zε z).symm, matVec_smul_eq, real_inner_smul_left, real_inner_smul_left,
    real_inner_smul_right, real_inner_smul_right]
  ring

end Lasso
