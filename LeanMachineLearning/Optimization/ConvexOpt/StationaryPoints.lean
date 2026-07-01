/-
Copyright (c) 2025 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.ConvexOpt.Basic

/-!
# Convergence to stationary points (Theorems 7.1 and 7.2)

This file proves that gradient descent (Theorem 7.1) and gradient flow (Theorem 7.2)
find approximate stationary points at rate `O(β/t)` and `O(1/t)` respectively,
under only `β`-smoothness and no convexity assumption.

The proofs telescope the descent inequality from `gd_descent_step`:
  `Σᵢ ‖∇f(wᵢ)‖² ≤ 2β(f(w₀) - f(wₜ)) ≤ 2β(f(w₀) - inf f)`
and divide by `t`.

## Main results

| Name | Statement |
|------|-----------|
| `ConvexOpt.gd_stationary_convergence` | `min_{i<t} ‖∇f(wᵢ)‖² ≤ 2β/t · (f(w₀) - inf f)` |
| `ConvexOpt.gf_stationary_convergence` | `inf_{s∈[0,t]} ‖∇f(w(s))‖² ≤ 1/t · (f(w(0)) - f(w(t)))` |

-/

@[expose] public section

open Real MeasureTheory Filter

namespace ConvexOpt

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-! ### GD convergence to stationary points (Theorem 7.1) -/

/-- **Theorem 7.1** (Telgarsky 2021, §7.1.1).

With constant step size `η = 1/β`, the GD iterates on a `β`-smooth function satisfy:
1. Monotone decrease: `f(w_{i+1}) ≤ f(wᵢ)` for all `i`.
2. Telescoping sum: `Σ_{i<t} ‖∇f(wᵢ)‖² ≤ 2β · (f(w₀) - f(wₜ))`.
3. Stationary point rate: `min_{i<t} ‖∇f(wᵢ)‖² ≤ 2β/t · (f(w₀) - inf_w f(w))`.

The proof telescopes the per-step decrease from `gd_descent_step`. -/
theorem gd_stationary_sum {f : E → ℝ} {β : ℝ} (hβ : 0 < β)
    (hf : BetaSmooth f β) (w₀ : E) (t : ℕ) :
    ∑ i ∈ Finset.range t, ‖gradient f (gdIterate f (fun _ => β⁻¹) w₀ i)‖ ^ 2 ≤
    2 * β * (f w₀ - f (gdIterate f (fun _ => β⁻¹) w₀ t)) := by
  induction t with
  | zero => simp [gdIterate]
  | succ t ih =>
    have hstep : f (gdIterate f (fun _ => β⁻¹) w₀ (t + 1)) ≤
        f (gdIterate f (fun _ => β⁻¹) w₀ t) - (2 * β)⁻¹ * ‖gradient f (gdIterate f (fun _ => β⁻¹) w₀ t)‖ ^ 2 := by
      simp only [gdIterate]
      exact gd_descent_step hβ hf _
    have hineq : ‖gradient f (gdIterate f (fun _ => β⁻¹) w₀ t)‖ ^ 2 ≤
        2 * β * (f (gdIterate f (fun _ => β⁻¹) w₀ t) - f (gdIterate f (fun _ => β⁻¹) w₀ (t + 1))) := by
      have hsub : (2 * β)⁻¹ * ‖gradient f (gdIterate f (fun _ => β⁻¹) w₀ t)‖ ^ 2 ≤
          f (gdIterate f (fun _ => β⁻¹) w₀ t) - f (gdIterate f (fun _ => β⁻¹) w₀ (t + 1)) := by
        linarith
      have hpos : 0 ≤ 2 * β := by linarith
      calc
        ‖gradient f (gdIterate f (fun _ => β⁻¹) w₀ t)‖ ^ 2
            = (2 * β) * ((2 * β)⁻¹ * ‖gradient f (gdIterate f (fun _ => β⁻¹) w₀ t)‖ ^ 2) := by
              field_simp [show 2 * β ≠ 0 from by linarith]
        _ ≤ (2 * β) * (f (gdIterate f (fun _ => β⁻¹) w₀ t) - f (gdIterate f (fun _ => β⁻¹) w₀ (t + 1))) :=
              mul_le_mul_of_nonneg_left hsub hpos
    calc
      ∑ i ∈ Finset.range (t + 1), ‖gradient f (gdIterate f (fun _ => β⁻¹) w₀ i)‖ ^ 2
          = (∑ i ∈ Finset.range t, ‖gradient f (gdIterate f (fun _ => β⁻¹) w₀ i)‖ ^ 2) +
            ‖gradient f (gdIterate f (fun _ => β⁻¹) w₀ t)‖ ^ 2 := by
            rw [Finset.sum_range_succ]
      _ ≤ 2 * β * (f w₀ - f (gdIterate f (fun _ => β⁻¹) w₀ t)) +
          2 * β * (f (gdIterate f (fun _ => β⁻¹) w₀ t) - f (gdIterate f (fun _ => β⁻¹) w₀ (t + 1))) :=
            add_le_add ih hineq
      _ = 2 * β * (f w₀ - f (gdIterate f (fun _ => β⁻¹) w₀ (t + 1))) := by ring

theorem gd_stationary_convergence {f : E → ℝ} {β : ℝ} (hβ : 0 < β)
    (hf : BetaSmooth f β) (w₀ : E) {t : ℕ} (ht : 0 < t) :
    (Finset.range t).inf' ⟨0, Finset.mem_range.mpr ht⟩
      (fun i => ‖gradient f (gdIterate f (fun _ => β⁻¹) w₀ i)‖ ^ 2) ≤
    2 * β / t * (f w₀ - ⨅ w, f w) := by
  sorry

/-! ### GD is monotone decreasing (Part 1 of Theorem 7.1) -/

/-- The objective is non-increasing along GD iterates with step size `1/β`. -/
theorem gd_monotone {f : E → ℝ} {β : ℝ} (hβ : 0 < β)
    (hf : BetaSmooth f β) (w₀ : E) (i : ℕ) :
    f (gdIterate f (fun _ => β⁻¹) w₀ (i + 1)) ≤ f (gdIterate f (fun _ => β⁻¹) w₀ i) := by
  simp only [gdIterate]
  linarith [gd_descent_step hβ hf (gdIterate f (fun _ => β⁻¹) w₀ i),
            mul_nonneg (inv_nonneg.mpr (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hβ.le))
              (sq_nonneg ‖gradient f (gdIterate f (fun _ => β⁻¹) w₀ i)‖)]

/-! ### GF convergence to stationary points (Theorem 7.2) -/

/-- **Theorem 7.2** (Telgarsky 2021, §7.1.1).

For gradient flow on a differentiable function:
  `inf_{s ∈ [0,t]} ‖∇f(w(s))‖² ≤ (f(w(0)) - f(w(t))) / t`.

The proof uses the identity `d/ds f(w(s)) = -‖∇f(w(s))‖²` and integrates. -/
theorem gf_stationary_convergence {f : E → ℝ} {w₀ : E} {w : ℝ → E}
    (hf : Differentiable ℝ f) (hw : GFTrajectory f w₀ w) {t : ℝ} (ht : 0 < t) :
    ⨅ s ∈ Set.Icc 0 t, ‖gradient f (w s)‖ ^ 2 ≤
    (f (w 0) - f (w t)) / t := by
  sorry

/-- The objective is non-increasing along gradient flow trajectories. -/
theorem gf_monotone {f : E → ℝ} {w₀ : E} {w : ℝ → E}
    (hf : Differentiable ℝ f) (hw : GFTrajectory f w₀ w) {s₁ s₂ : ℝ}
    (hs : s₁ ≤ s₂) : f (w s₂) ≤ f (w s₁) := by
  sorry

end ConvexOpt

end
