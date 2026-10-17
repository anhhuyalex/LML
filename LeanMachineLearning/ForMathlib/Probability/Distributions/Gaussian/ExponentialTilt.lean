/-
Copyright (c) 2026 LML contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML contributors
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Exponential tilting of the standard Gaussian

Tilting `N(0, 1)` by the density `exp (a g)` gives a multiple of `N(a, 1)`: the Cameron–Martin
formula in dimension one.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory

/-- The pointwise density identity behind exponential tilting: completing the square. -/
theorem gaussianPDF_zero_one_mul_exp (a x : ℝ) :
    gaussianPDF 0 1 x * ENNReal.ofReal (Real.exp (a * x)) =
      ENNReal.ofReal (Real.exp (a ^ 2 / 2)) * gaussianPDF a 1 x := by
  simp only [gaussianPDF, gaussianPDFReal]
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have he : a * x + (-(x - 0) ^ 2 / (2 * (1 : ℝ))) =
      a ^ 2 / 2 + (-(x - a) ^ 2 / (2 * (1 : ℝ))) := by ring
  simp only [NNReal.coe_one, mul_one] at *
  calc
    _ = (√(2 * Real.pi))⁻¹ * Real.exp (a * x + (-(x - 0) ^ 2 / 2)) := by
        rw [Real.exp_add]; ring
    _ = (√(2 * Real.pi))⁻¹ * Real.exp (a ^ 2 / 2 + (-(x - a) ^ 2 / 2)) := by rw [he]
    _ = _ := by rw [Real.exp_add]; ring

/-- Exponential tilting of a standard Gaussian, before normalizing: the resulting
measure has mean `a` and total mass `exp (a²/2)`. -/
theorem gaussianReal_withDensity_exp_mul (a : ℝ) :
    (gaussianReal 0 1).withDensity (fun g => ENNReal.ofReal (Real.exp (a * g))) =
      ENNReal.ofReal (Real.exp (a ^ 2 / 2)) • gaussianReal a 1 := by
  rw [gaussianReal_of_var_ne_zero (0 : ℝ) (one_ne_zero : (1 : NNReal) ≠ 0),
    gaussianReal_of_var_ne_zero a (one_ne_zero : (1 : NNReal) ≠ 0)]
  apply Measure.ext
  intro s hs
  rw [withDensity_apply _ hs, Measure.smul_apply, withDensity_apply _ hs,
    setLIntegral_withDensity_eq_setLIntegral_mul _ (by fun_prop) (by fun_prop) hs,
    smul_eq_mul, ← lintegral_const_mul _ (by fun_prop : Measurable (gaussianPDF a 1))]
  exact setLIntegral_congr_fun hs fun x _ => gaussianPDF_zero_one_mul_exp a x

end ProbabilityTheory
