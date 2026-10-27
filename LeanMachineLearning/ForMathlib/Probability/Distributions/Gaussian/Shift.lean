/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Shifting a standard Gaussian (Cameron-Martin for one variable)

Also: the standard Gaussian charges every nonempty open set.

For `z ~ N(0, 1)` and `a : ℝ`, `𝔼 f(z + a) = 𝔼 [f(z) exp(a z - a²/2)]`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory

/-- **Gaussian shift as a change of density:** `𝔼 f(z + a) = 𝔼 [f(z) e^{a z - a²/2}]` for
`z ~ N(0, 1)`. -/
theorem integral_gaussianReal_add_const_eq (f : ℝ → ℝ) (a : ℝ) :
    ∫ z, f (z + a) ∂(gaussianReal 0 1) =
      ∫ u, f u * Real.exp (a * u - a ^ 2 / 2) ∂(gaussianReal 0 1) := by
  have h1 : ∫ z, f (z + a) ∂(gaussianReal 0 1) = ∫ u, f u ∂(gaussianReal a 1) := by
    rw [← (measurableEmbedding_addRight a).integral_map f, gaussianReal_map_add_const, zero_add]
  rw [h1, integral_gaussianReal_eq_integral_smul one_ne_zero,
    integral_gaussianReal_eq_integral_smul one_ne_zero]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only [gaussianPDFReal_def, smul_eq_mul]
  have : Real.exp (-(u - a) ^ 2 / (2 * (1 : NNReal))) =
      Real.exp (-(u - 0) ^ 2 / (2 * (1 : NNReal))) * Real.exp (a * u - a ^ 2 / 2) := by
    rw [← Real.exp_add]
    congr 1
    push_cast
    ring
  rw [this]
  ring

/-- Every nonempty open set has positive standard Gaussian measure. -/
instance : (gaussianReal 0 1).IsOpenPosMeasure :=
  ⟨fun _ hU hne h0 =>
    (hU.measure_pos volume hne).ne' (gaussianReal_absolutelyContinuous' 0 one_ne_zero h0)⟩

end ProbabilityTheory
