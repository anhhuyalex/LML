/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Scalar linear ODEs with a continuous coefficient

A solution of `f' = a f` on `ℝ` with `a` continuous is `f t = f 0 * exp (∫₀ᵗ a)`.  The proof
multiplies by the integrating factor `exp (-∫₀ᵗ a)`, whose product with `f` has zero derivative.

## Main declarations

* `eq_mul_exp_intervalIntegral_of_hasDerivAt`: the explicit solution.
-/

@[expose] public section

/-- **Explicit solution of a scalar linear ODE.**  If `a` is continuous and `f' τ = a τ * f τ` for
every `τ`, then `f t = f 0 * exp (∫₀ᵗ a)`.  In particular `f` vanishes nowhere unless `f 0 = 0`. -/
theorem eq_mul_exp_intervalIntegral_of_hasDerivAt {a f : ℝ → ℝ} (ha : Continuous a)
    (hf : ∀ τ, HasDerivAt f (a τ * f τ) τ) (t : ℝ) :
    f t = f 0 * Real.exp (∫ s in (0 : ℝ)..t, a s) := by
  set I : ℝ → ℝ := fun τ => ∫ s in (0 : ℝ)..τ, a s with hI
  have hI_deriv : ∀ τ, HasDerivAt I (a τ) τ := fun τ =>
    intervalIntegral.integral_hasDerivAt_right (ha.intervalIntegrable _ _)
      (ha.stronglyMeasurableAtFilter _ _) ha.continuousAt
  have hφ : ∀ τ, HasDerivAt (fun s => f s * Real.exp (-I s)) 0 τ := fun τ => by
    have h := (hf τ).mul (hI_deriv τ).neg.exp
    convert h using 1
    ring
  have hconst := is_const_of_deriv_eq_zero (fun τ => (hφ τ).differentiableAt)
    (fun τ => (hφ τ).deriv) t 0
  have h0 : I 0 = 0 := by simp [hI]
  simp only [h0, neg_zero, Real.exp_zero, mul_one] at hconst
  rw [← hconst, mul_assoc, ← Real.exp_add]
  change f t = f t * Real.exp (-I t + I t)
  rw [neg_add_cancel, Real.exp_zero, mul_one]
