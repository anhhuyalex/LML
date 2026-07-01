/-
Copyright (c) 2025 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.ConvexOpt.StationaryPoints

/-!
# Smooth+convex convergence rates (Theorems 7.3 and 7.4)

This file proves convergence bounds for gradient descent and gradient flow when the
objective is both `β`-smooth **and** convex (Telgarsky 2021, §7.1.2).

The key innovation in the presentation is the use of an **arbitrary reference point** `z`
instead of a minimizer.  This is essential for applications (e.g., margin maximization)
where no minimizer exists.

## Strategy

Both proofs telescope a potential function.

**GD (Theorem 7.3):** The potential is `‖wᵢ - z‖²`.  Expanding the step and using
convexity + the descent lemma gives
  `‖w_{i+1} - z‖² ≤ ‖wᵢ - z‖² + 2/β · (f(z) - f(w_{i+1}))`.
Summing over `i < t` and using monotone decrease of `f(wᵢ)` yields the bound.

**GF (Theorem 7.4):** The potential is `½‖w(s) - z‖²`.  Differentiating and using convexity gives
  `d/ds (½‖w(s) - z‖²) ≤ f(z) - f(w(s))`.
Integrating over `[0, t]` and using monotone decrease of `f(w(s))` yields the bound.

## Main results

| Name | Statement |
|------|-----------|
| `ConvexOpt.gd_convex_potential_step` | Per-step potential decrease for GD |
| `ConvexOpt.gd_convex_convergence` | Theorem 7.3: `f(wₜ) - f(z) ≤ β/2t · ‖w₀ - z‖²` |
| `ConvexOpt.gf_convex_convergence` | Theorem 7.4: `f(w(t)) - f(z) ≤ ‖w(0) - z‖²/(2t)` |

-/

@[expose] public section

open Real MeasureTheory Filter Set

namespace ConvexOpt

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-! ### GD smooth+convex: potential step (auxiliary lemma) -/

/-- For one gradient descent step on a `β`-smooth convex function with `η = 1/β`,
the squared distance to any reference point `z` satisfies
  `‖w' - z‖² ≤ ‖w - z‖² + 2/β · (f(z) - f(w'))`. -/
lemma gd_convex_potential_step {f : E → ℝ} {β : ℝ} (hβ : 0 < β)
    (hf : BetaSmooth f β) (hcvx : IsConvex f)
    (w z : E) :
    let w' := w - β⁻¹ • gradient f w
    ‖w' - z‖ ^ 2 ≤ ‖w - z‖ ^ 2 + 2 / β * (f z - f w') := by
  intro w'
  -- Expand ‖w' - z‖² = ‖w - z - β⁻¹ • ∇f(w)‖²
  have hexp : ‖w' - z‖ ^ 2 = ‖w - z‖ ^ 2
      - 2 * β⁻¹ * inner ℝ (gradient f w) (w - z)
      + (β⁻¹)^2 * ‖gradient f w‖ ^ 2 := by
    dsimp [w']
    calc
      ‖(w - β⁻¹ • gradient f w) - z‖ ^ 2
          = ‖(w - z) - (β⁻¹ • gradient f w)‖ ^ 2 := by abel_nf
      _ = ‖w - z‖ ^ 2 - 2 * inner ℝ (w - z) (β⁻¹ • gradient f w) + ‖β⁻¹ • gradient f w‖ ^ 2 := by
        rw [norm_sub_sq_real]
      _ = ‖w - z‖ ^ 2 - 2 * inner ℝ (w - z) (β⁻¹ • gradient f w) + (β⁻¹)^2 * ‖gradient f w‖ ^ 2 := by
        have hnorm : ‖β⁻¹ • gradient f w‖ ^ 2 = (β⁻¹)^2 * ‖gradient f w‖ ^ 2 := by
          calc
            ‖β⁻¹ • gradient f w‖ ^ 2 = (‖β⁻¹‖ * ‖gradient f w‖) ^ 2 := by rw [norm_smul]
            _ = (|β⁻¹| * ‖gradient f w‖) ^ 2 := by rw [Real.norm_eq_abs]
            _ = (β⁻¹ * ‖gradient f w‖) ^ 2 := by rw [abs_of_pos (inv_pos.mpr hβ)]
            _ = (β⁻¹)^2 * ‖gradient f w‖ ^ 2 := by ring
        rw [hnorm]
      _ = ‖w - z‖ ^ 2 - 2 * (β⁻¹ * inner ℝ (w - z) (gradient f w)) + (β⁻¹)^2 * ‖gradient f w‖ ^ 2 := by
        simp [inner_smul_right]
      _ = ‖w - z‖ ^ 2 - 2 * β⁻¹ * inner ℝ (gradient f w) (w - z) + (β⁻¹)^2 * ‖gradient f w‖ ^ 2 := by
        rw [real_inner_comm (w - z) (gradient f w)]
        ring
  rw [hexp]
  -- By convexity: ⟪∇f(w), w - z⟫ ≥ f(w) - f(z), so -⟨∇f(w), w - z⟩ ≤ f(z) - f(w)
  have hcvx_ineq : inner ℝ (gradient f w) (w - z) ≥ f w - f z := by
    have h := hcvx w z
    -- h : f w + inner ℝ (gradient f w) (z - w) ≤ f z
    have hinner : inner ℝ (gradient f w) (z - w) = -inner ℝ (gradient f w) (w - z) := by
      rw [inner_sub_right (gradient f w) z w, inner_sub_right (gradient f w) w z]
      ring
    rw [hinner] at h
    linarith
  -- By descent: (β⁻¹)² ‖∇f(w)‖² ≤ 2β⁻¹(f(w) - f(w'))
  have hpos_inv : 0 < β⁻¹ := inv_pos.mpr hβ
  have hpos_two_inv : 0 ≤ 2 * β⁻¹ := by nlinarith
  have hdescent : (β⁻¹)^2 * ‖gradient f w‖ ^ 2 ≤ 2 * β⁻¹ * (f w - f w') := by
    have hstep := gd_descent_step hβ hf w
    -- hstep : f w' ≤ f w - (2 * β)⁻¹ * ‖gradient f w‖ ^ 2
    have hdiff : f w - f w' ≥ (2 * β)⁻¹ * ‖gradient f w‖ ^ 2 := by linarith
    have hcalc : 2 * β⁻¹ * ((2 * β)⁻¹ * ‖gradient f w‖ ^ 2) = (β⁻¹)^2 * ‖gradient f w‖ ^ 2 := by
      ring
    have hineq : 2 * β⁻¹ * (f w - f w') ≥ 2 * β⁻¹ * ((2 * β)⁻¹ * ‖gradient f w‖ ^ 2) := by
      nlinarith
    rw [hcalc] at hineq
    exact hineq
  rw [div_eq_mul_inv]
  have hneg : -2 * β⁻¹ * inner ℝ (gradient f w) (w - z) ≤ 2 * β⁻¹ * (f z - f w) := by
    have htemp : inner ℝ (gradient f w) (w - z) ≥ f w - f z := hcvx_ineq
    nlinarith
  have hsum : -2 * β⁻¹ * inner ℝ (gradient f w) (w - z) + (β⁻¹)^2 * ‖gradient f w‖ ^ 2 ≤ 2 * β⁻¹ * (f z - f w') := by
    nlinarith
  nlinarith

/-! ### GD smooth+convex convergence (Theorem 7.3) -/

/-- **Theorem 7.3** (Telgarsky 2021, Theorem 7.3).

On a `β`-smooth convex function with GD step size `η = 1/β`, for any reference point `z ∈ E`:
  `f(wₜ) - f(z) ≤ β/(2t) · (‖w₀ - z‖² - ‖wₜ - z‖²) ≤ β/(2t) · ‖w₀ - z‖²`.

Setting `z = argmin f` (when it exists) recovers the classical `O(β ‖w₀ - w*‖² / t)` rate. -/
theorem gd_convex_convergence {f : E → ℝ} {β : ℝ} (hβ : 0 < β)
    (hf : BetaSmooth f β) (hcvx : IsConvex f) (w₀ z : E) {t : ℕ} (ht : 0 < t) :
    f (gdIterate f (fun _ => β⁻¹) w₀ t) - f z ≤
    β / (2 * t) * (‖w₀ - z‖ ^ 2 - ‖gdIterate f (fun _ => β⁻¹) w₀ t - z‖ ^ 2) := by
  sorry

/-- The final iterate bound: `f(wₜ) - f(z) ≤ β‖w₀ - z‖² / (2t)`. -/
theorem gd_convex_convergence_simplified {f : E → ℝ} {β : ℝ} (hβ : 0 < β)
    (hf : BetaSmooth f β) (hcvx : IsConvex f) (w₀ z : E) {t : ℕ} (ht : 0 < t) :
    f (gdIterate f (fun _ => β⁻¹) w₀ t) - f z ≤ β * ‖w₀ - z‖ ^ 2 / (2 * t) := by
  have h := gd_convex_convergence hβ hf hcvx w₀ z ht
  have hsq := sq_nonneg ‖gdIterate f (fun _ => β⁻¹) w₀ t - z‖
  have ht_pos : 0 < (t : ℝ) := by exact_mod_cast ht
  have hβ_nonneg : 0 ≤ β := hβ.le
  have h_coeff_nonneg : 0 ≤ β / (2 * (t : ℝ)) := by positivity
  have h_sub : ‖w₀ - z‖ ^ 2 - ‖gdIterate f (fun _ => β⁻¹) w₀ t - z‖ ^ 2 ≤ ‖w₀ - z‖ ^ 2 := by nlinarith
  have h_mul : β / (2 * (t : ℝ)) * (‖w₀ - z‖ ^ 2 - ‖gdIterate f (fun _ => β⁻¹) w₀ t - z‖ ^ 2) ≤
      β / (2 * (t : ℝ)) * ‖w₀ - z‖ ^ 2 := by
    nlinarith
  have h_eq : β / (2 * (t : ℝ)) * ‖w₀ - z‖ ^ 2 = β * ‖w₀ - z‖ ^ 2 / (2 * (t : ℝ)) := by ring
  rw [h_eq] at h_mul
  have h_trans : f (gdIterate f (fun _ => β⁻¹) w₀ t) - f z ≤ β * ‖w₀ - z‖ ^ 2 / (2 * (t : ℝ)) := by
    linarith
  simpa using h_trans

/-! ### GF smooth+convex convergence (Theorem 7.4) -/

/-- **Theorem 7.4** (Telgarsky 2021, Theorem 7.4).

For a convex function `f` and gradient flow trajectory `w(t)`, for any reference point `z`:
  `t · f(w(t)) + ½‖w(t) - z‖² ≤ t · f(z) + ½‖w(0) - z‖²`.

In particular, `f(w(t)) - f(z) ≤ ‖w(0) - z‖² / (2t)`.

The GF bound is sharper than GD by a factor of `β` (no smoothness constant needed),
which corresponds to the "arc length units" observation: GD with step `1/β` takes
`t/β` units of arc length, while GF takes `t`. -/
theorem gf_convex_convergence {f : E → ℝ} {w₀ : E} {w : ℝ → E}
    (hf : Differentiable ℝ f) (hcvx : IsConvex f) (hw : GFTrajectory f w₀ w)
    (z : E) {t : ℝ} (ht : 0 < t) :
    t * f (w t) + (1 / 2) * ‖w t - z‖ ^ 2 ≤ t * f z + (1 / 2) * ‖w 0 - z‖ ^ 2 := by
  sorry

/-- Simplified form: `f(w(t)) - f(z) ≤ ‖w(0) - z‖² / (2t)`. -/
theorem gf_convex_convergence_simplified {f : E → ℝ} {w₀ : E} {w : ℝ → E}
    (hf : Differentiable ℝ f) (hcvx : IsConvex f) (hw : GFTrajectory f w₀ w)
    (z : E) {t : ℝ} (ht : 0 < t) :
    f (w t) - f z ≤ ‖w 0 - z‖ ^ 2 / (2 * t) := by
  have h := gf_convex_convergence hf hcvx hw z ht
  have hsq := sq_nonneg ‖w t - z‖
  have hsub : ‖w 0 - z‖ ^ 2 - ‖w t - z‖ ^ 2 ≤ ‖w 0 - z‖ ^ 2 := by nlinarith
  have h_mid : t * (f (w t) - f z) ≤ (1/2 : ℝ) * (‖w 0 - z‖ ^ 2 - ‖w t - z‖ ^ 2) := by linarith
  have h_mid' : t * (f (w t) - f z) ≤ (1/2 : ℝ) * ‖w 0 - z‖ ^ 2 := by linarith
  have h_final : f (w t) - f z ≤ ((1/2 : ℝ) * ‖w 0 - z‖ ^ 2) / t := by
    rw [mul_comm] at h_mid'
    exact (le_div_iff₀ ht).mpr h_mid'
  -- Now simplify ((1/2) * A) / t = A / (2 * t)
  have h_div_simp : ((1/2 : ℝ) * ‖w 0 - z‖ ^ 2) / t = ‖w 0 - z‖ ^ 2 / (2 * t) := by ring
  rw [h_div_simp] at h_final
  exact h_final

end ConvexOpt

end
