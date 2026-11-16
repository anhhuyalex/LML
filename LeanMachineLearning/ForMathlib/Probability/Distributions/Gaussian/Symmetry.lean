/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Real

/-! # Sign symmetry of centered Gaussians

Sign-symmetric integrals, and the probability `1 / 2` of the nonnegative half-line. -/

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

/-- **A nondegenerate centered Gaussian charges the nonnegative half-line with mass `1 / 2`.**
By sign symmetry `Iio 0` and `Ioi 0` have the same mass, and a single point is null. -/
theorem gaussianReal_Ici_zero {v : NNReal} (hv : v ≠ 0) :
    gaussianReal 0 v (Set.Ici 0) = 2⁻¹ := by
  have := nullSingletonClass_gaussianReal (μ := 0) hv
  have hneg : (gaussianReal 0 v).map (fun x : ℝ => -x) = gaussianReal 0 v := by
    rw [gaussianReal_map_neg, neg_zero]
  have hIio : gaussianReal 0 v (Set.Iio 0) = gaussianReal 0 v (Set.Ici 0) := by
    calc gaussianReal 0 v (Set.Iio 0)
        = ((gaussianReal 0 v).map (fun x : ℝ => -x)) (Set.Iio 0) := by rw [hneg]
      _ = gaussianReal 0 v (Set.Ioi 0) := by
        rw [Measure.map_apply measurable_neg measurableSet_Iio]
        congr 1
        ext x
        simp
      _ = gaussianReal 0 v (Set.Ici 0) := Ioi_ae_eq_Ici.measure_eq
  have h1 : gaussianReal 0 v (Set.Ici 0) + gaussianReal 0 v (Set.Ici 0) = 1 := by
    nth_rewrite 2 [← hIio]
    rw [← Set.compl_Ici, measure_add_measure_compl measurableSet_Ici, measure_univ]
  rw [← two_mul] at h1
  calc gaussianReal 0 v (Set.Ici 0)
      = 2⁻¹ * (2 * gaussianReal 0 v (Set.Ici 0)) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul]
    _ = 2⁻¹ := by rw [h1, mul_one]

end ProbabilityTheory
