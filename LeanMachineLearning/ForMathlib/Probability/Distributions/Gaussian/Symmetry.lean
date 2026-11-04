/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Real

/-! # Sign symmetry of centered Gaussian integrals -/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory

/-- A centered Gaussian integral of a function of a scaled variable depends only on
the absolute value of the scale. This holds for arbitrary variance and Banach-valued functions. -/
theorem integral_gaussianReal_abs_mul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : NNReal) (F : ℝ → E) (a : ℝ) :
    ∫ z : ℝ, F (|a| * z) ∂gaussianReal 0 v =
      ∫ z : ℝ, F (a * z) ∂gaussianReal 0 v := by
  by_cases ha : 0 ≤ a
  · rw [abs_of_nonneg ha]
  · rw [abs_of_neg (lt_of_not_ge ha)]
    have hm : MeasurePreserving (fun z : ℝ => -z) (gaussianReal 0 v) (gaussianReal 0 v) :=
      ⟨measurable_neg, by rw [gaussianReal_map_neg, neg_zero]⟩
    have h := hm.integral_comp (Homeomorph.neg ℝ).measurableEmbedding (fun z => F (a * z))
    simpa only [neg_mul, mul_neg] using h

end ProbabilityTheory
