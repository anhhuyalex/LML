/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.Gradient.Basic

/-!
# Gradient of a constant multiple

Mathlib has `HasFDerivAt.const_mul` and `fderiv_const_smul` (which need differentiability), but no
statement for `gradient`. The lemma below needs no differentiability hypothesis: for `c ≠ 0` a
function and its multiple by `c` are differentiable at the same points, and off those points both
gradients vanish.
-/

@[expose] public section

open scoped Gradient

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- The gradient of a constant multiple is the multiple of the gradient. -/
lemma gradient_const_mul (c : ℝ) (g : F → ℝ) (x : F) :
    ∇ (fun y => c * g y) x = c • ∇ g x := by
  by_cases hc : c = 0
  · simp [hc]
  by_cases hg : DifferentiableAt ℝ g x
  · have h : HasGradientAt (fun y => c * g y) (c • ∇ g x) x := by
      rw [hasGradientAt_iff_hasFDerivAt, map_smul]
      have h0 : HasFDerivAt g (InnerProductSpace.toDual ℝ F (∇ g x)) x :=
        hasGradientAt_iff_hasFDerivAt.1 hg.hasGradientAt
      exact h0.const_mul c
    exact h.gradient
  · have h2 : ¬ DifferentiableAt ℝ (fun y => c * g y) x := fun h =>
      hg (by simpa [← mul_assoc, hc] using h.const_mul c⁻¹)
    simp [gradient_eq_zero_of_not_differentiableAt hg, gradient_eq_zero_of_not_differentiableAt h2]
