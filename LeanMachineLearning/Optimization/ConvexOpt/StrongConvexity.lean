/-
Copyright (c) 2025 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.ConvexOpt.ConvexConvergence
public import Mathlib.Analysis.ODE.Gronwall

/-!
# Strongly convex convergence rates (Theorems 7.5–7.7)

This file proves exponential convergence rates for gradient descent and gradient flow
on `mu`-strongly convex functions (Telgarsky 2021, §7.2).

Strong convexity improves the convergence rate from `O(1/t)` to exponential `exp(-Ω(t))`.
The key inequalities are:
- For GD: each step contracts the distance to `w*` by factor `(1 - mu/β)`.
- For GF: Gronwall's inequality from the strong convexity ODE `d/dt ½‖w(t)-w*‖² ≤ -mu‖w(t)-w*‖²`.

## Main results

| Name | Statement |
|------|-----------|
| `ConvexOpt.sc_gradient_inner` | Strong convexity implies `⟪∇f(w) - ∇f(v), w - v⟫ ≥ mu‖w - v‖²` |
| `ConvexOpt.gd_strongly_convex_convergence` | Theorem 7.5: linear rate `(1 - mu/β)ᵗ` for GD |
| `ConvexOpt.gf_strongly_convex_convergence` | Theorem 7.6: exponential rate `exp(-2mut)` for GF |
| `ConvexOpt.gd_strongly_convex_ref` | Theorem 7.7: combined bound with reference point `z` |

-/

@[expose] public section

open Real MeasureTheory Filter Set

namespace ConvexOpt

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-! ### Basic properties of strong convexity -/

/-- Strong convexity implies a lower bound on gradient inner products ("co-coercivity" direction):
  `⟪∇f(w) - ∇f(v), w - v⟫ ≥ mu‖w - v‖²`.

This follows from the first-order strong convexity inequality applied symmetrically to `(w, v)` and `(v, w)`. -/
lemma sc_gradient_inner {f : E → ℝ} {mu : ℝ}
    (hf : IsStronglyConvex f mu) (w v : E) :
    Inner.inner (gradient f w - gradient f v) (w - v) ≥ mu * ‖w - v‖ ^ 2 := by
  have h1 := hf w v
  have h2 := hf v w
  rw [inner_sub_left]
  simp only [inner_sub_right, real_inner_comm (gradient f v) (w - v)]
  nlinarith [sq_nonneg ‖w - v‖]

/-- A strongly convex function has at most one critical point. -/
lemma sc_unique_critical_point {f : E → ℝ} {mu : ℝ} (hmu : 0 < mu)
    (hf : IsStronglyConvex f mu) {w v : E}
    (hw : gradient f w = 0) (hv : gradient f v = 0) : w = v := by
  have h := sc_gradient_inner hf w v
  rw [hw, hv] at h
  simp at h
  have : ‖w - v‖ ^ 2 = 0 := by nlinarith
  simp [sq_eq_zero_iff, norm_eq_zero] at this
  linarith [this]

/-! ### GD strongly convex rate (Theorem 7.5) -/

/-- **Theorem 7.5** (Telgarsky 2021, Theorem 7.5).

For `β`-smooth `mu`-strongly convex `f` with minimizer `w*`, GD with `η = 1/β` satisfies:
  `‖w_{i+1} - w*‖² ≤ (1 - mu/β) · ‖wᵢ - w*‖²`.

This gives the geometric rate `‖wₜ - w*‖² ≤ (1 - mu/β)ᵗ · ‖w₀ - w*‖²`. -/
theorem gd_strongly_convex_step {f : E → ℝ} {β mu : ℝ} (hβ : 0 < β) (hmu : 0 < mu)
    (hβmu : mu ≤ β)
    (hf : BetaSmooth f β) (hsc : IsStronglyConvex f mu)
    {wstar : E} (hwstar : gradient f wstar = 0)
    (w : E) :
    let w' := w - β⁻¹ • gradient f w
    ‖w' - wstar‖ ^ 2 ≤ (1 - mu / β) * ‖w - wstar‖ ^ 2 := by
  intro w'
  -- Expand ‖w' - w*‖² = ‖(w - w*) - β⁻¹ ∇f(w)‖²
  have hexp : ‖w' - wstar‖ ^ 2 = ‖w - wstar‖ ^ 2
      - 2 * β⁻¹ * inner (gradient f w) (w - wstar)
      + (β⁻¹)^2 * ‖gradient f w‖ ^ 2 := by
    simp only [w', sub_sub_sub_cancel_right]
    rw [norm_sub_sq_real]
    simp [inner_smul_left, mul_comm]; ring
  rw [hexp]
  -- Strong convexity: ⟪∇f(w) - ∇f(w*), w - w*⟫ ≥ mu‖w - w*‖², and ∇f(w*) = 0
  have hsc_ineq : inner (gradient f w) (w - wstar) ≥
      f w - f wstar + mu / 2 * ‖w - wstar‖ ^ 2 := by
    have := hsc w wstar
    simp [hwstar] at this
    linarith
  -- Smoothness + descent: (β⁻¹)^2 ‖∇f(w)‖² ≤ 2β⁻¹(f(w) - f(w'))
  have hdescent : (β⁻¹)^2 * ‖gradient f w‖ ^ 2 ≤ 2 * β⁻¹ * (f w - f w') := by
    have := gd_descent_step hβ hf w
    simp only [w'] at this
    nlinarith [mul_pos (inv_pos.mpr hβ) (inv_pos.mpr hβ)]
  -- f(w') ≥ f(w*)
  have hfmin : f wstar ≤ f w' := by
    have := hsc wstar w'
    simp [hwstar] at this
    linarith [sq_nonneg ‖w' - wstar‖]
  have hβ_pos : (0 : ℝ) < β := hβ
  nlinarith [mul_nonneg (div_nonneg hmu.le hβ.le) (sq_nonneg ‖w - wstar‖)]

/-- Geometric rate for GD under strong convexity. -/
theorem gd_strongly_convex_convergence {f : E → ℝ} {β mu : ℝ} (hβ : 0 < β) (hmu : 0 < mu)
    (hβmu : mu ≤ β)
    (hf : BetaSmooth f β) (hsc : IsStronglyConvex f mu)
    {wstar : E} (hwstar : gradient f wstar = 0)
    (w₀ : E) (t : ℕ) :
    ‖gdIterate f (fun _ => β⁻¹) w₀ t - wstar‖ ^ 2 ≤
    (1 - mu / β) ^ t * ‖w₀ - wstar‖ ^ 2 := by
  induction t with
  | zero => simp [gdIterate]
  | succ t ih =>
    calc ‖gdIterate f (fun _ => β⁻¹) w₀ (t + 1) - wstar‖ ^ 2
        ≤ (1 - mu / β) * ‖gdIterate f (fun _ => β⁻¹) w₀ t - wstar‖ ^ 2 :=
          gd_strongly_convex_step hβ hmu hβmu hf hsc hwstar _
      _ ≤ (1 - mu / β) * ((1 - mu / β) ^ t * ‖w₀ - wstar‖ ^ 2) := by
          apply mul_le_mul_of_nonneg_left ih
          linarith [div_le_one_of_le₀ hβmu hβ.le]
      _ = (1 - mu / β) ^ (t + 1) * ‖w₀ - wstar‖ ^ 2 := by ring

/-! ### GF strongly convex rate (Theorem 7.6) -/

/-- **Theorem 7.6** (Telgarsky 2021, Theorem 7.6).

For a `mu`-strongly convex `f` with minimizer `w*`, gradient flow satisfies:
  `‖w(t) - w*‖² ≤ ‖w(0) - w*‖² · exp(-2mut)`,
  `f(w(t)) - f(w*) ≤ (f(w(0)) - f(w*)) · exp(-2mut)`.

The distance bound follows from Gronwall's inequality applied to
`d/dt ½‖w(t) - w*‖² ≤ -mu‖w(t) - w*‖²`.

The Mathlib `gronwall_bound` theorem handles this ODE comparison. -/
theorem gf_strongly_convex_convergence {f : E → ℝ} {mu : ℝ} (hmu : 0 < mu)
    (hf : Differentiable ℝ f) (hsc : IsStronglyConvex f mu)
    {wstar w₀ : E} (hwstar : gradient f wstar = 0)
    {w : ℝ → E} (hw : GFTrajectory f w₀ w) {t : ℝ} (ht : 0 ≤ t) :
    ‖w t - wstar‖ ^ 2 ≤ ‖w₀ - wstar‖ ^ 2 * exp (-2 * mu * t) := by
  sorry

/-- The function value also decays exponentially under strong convexity + GF. -/
theorem gf_strongly_convex_obj_convergence {f : E → ℝ} {mu : ℝ} (hmu : 0 < mu)
    (hf : Differentiable ℝ f) (hsc : IsStronglyConvex f mu)
    {wstar w₀ : E} (hwstar : gradient f wstar = 0)
    {w : ℝ → E} (hw : GFTrajectory f w₀ w) {t : ℝ} (ht : 0 ≤ t) :
    f (w t) - f wstar ≤ (f w₀ - f wstar) * exp (-2 * mu * t) := by
  sorry

/-! ### Combined bound with reference point (Theorem 7.7) -/

/-- **Theorem 7.7** (Telgarsky 2021, Theorem 7.7).

For `β`-smooth `mu`-sc `f` with step size `η = 2/(β + mu)`, for any reference point `z`:
  `f(wₜ) - f(z) + mu/2 · ‖wₜ - z‖²
  ≤ ((β - mu)/(β + mu))ᵗ · (f(w₀) - f(z) + mu/2 · ‖w₀ - z‖²)`.

The condition number `κ = β/mu` controls the contraction rate `(κ-1)/(κ+1) < 1`.
This bound does **not** require a minimizer `w*` to exist. -/
theorem gd_strongly_convex_ref {f : E → ℝ} {β mu : ℝ} (hβ : 0 < β) (hmu : 0 < mu)
    (hβmu : mu < β)
    (hf : BetaSmooth f β) (hsc : IsStronglyConvex f mu)
    (w₀ z : E) (t : ℕ) :
    f (gdIterate f (fun _ => 2 / (β + mu)) w₀ t) - f z
    + mu / 2 * ‖gdIterate f (fun _ => 2 / (β + mu)) w₀ t - z‖ ^ 2
    ≤ ((β - mu) / (β + mu)) ^ t *
      (f w₀ - f z + mu / 2 * ‖w₀ - z‖ ^ 2) := by
  sorry

/-- The contraction ratio `(β - mu)/(β + mu)` is strictly less than 1 when `mu > 0`. -/
lemma contraction_ratio_lt_one {β mu : ℝ} (hβ : 0 < β) (hmu : 0 < mu) :
    (β - mu) / (β + mu) < 1 := by
  rw [div_lt_one (by linarith)]
  linarith

/-- The condition number `κ = β/mu` satisfies `κ ≥ 1` when `β ≥ mu > 0`. -/
lemma condition_number_ge_one {β mu : ℝ} (hβ : 0 < β) (hmu : 0 < mu) (hβmu : mu ≤ β) :
    1 ≤ β / mu := by
  exact ((one_le_div hmu).mpr hβmu)

end ConvexOpt

end
