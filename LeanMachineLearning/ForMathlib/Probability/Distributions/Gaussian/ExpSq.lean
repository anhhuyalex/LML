/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# The exponential of a Gaussian square

`𝔼 exp (l g²) = (1 - 2 l)^{-1/2}` for a standard Gaussian `g` and `l < 1 / 2`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory

/-- The standard Gaussian density times `exp (l x²)` is a multiple of `exp (-(1/2 - l) x²)`. -/
theorem gaussianPDFReal_zero_one_mul_exp_sq (l x : ℝ) :
    gaussianPDFReal 0 1 x * Real.exp (l * x ^ 2) =
      (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(1 / 2 - l) * x ^ 2) := by
  rw [gaussianPDFReal_def, mul_assoc, ← Real.exp_add]
  simp only [NNReal.coe_one, mul_one, sub_zero]
  congr 2
  ring

/-- **Gaussian square exponential moment:** for `l < 1 / 2`,
`∫ exp (l x²) d𝒩(0, 1) = (√(1 - 2 l))⁻¹`. -/
theorem integral_exp_mul_sq_gaussianReal {l : ℝ} (hl : l < 1 / 2) :
    ∫ x, Real.exp (l * x ^ 2) ∂(gaussianReal 0 1) = (Real.sqrt (1 - 2 * l))⁻¹ := by
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero]
  simp_rw [smul_eq_mul, gaussianPDFReal_zero_one_mul_exp_sq]
  rw [integral_const_mul, integral_gaussian]
  have h1 : 0 < 1 - 2 * l := by linarith
  have h2 : 0 < 1 / 2 - l := by linarith
  have e : Real.pi / (1 / 2 - l) = (2 * Real.pi) * (1 - 2 * l)⁻¹ := by
    field_simp
  rw [e, show (2 * Real.pi) * (1 - 2 * l)⁻¹ = (2 * Real.pi) / (1 - 2 * l) from
    (div_eq_mul_inv _ _).symm, Real.sqrt_div (by positivity), Real.sqrt_mul (by positivity)]
  have : 0 < Real.sqrt (1 - 2 * l) := Real.sqrt_pos.2 h1
  have : 0 < Real.sqrt 2 * Real.sqrt Real.pi := by positivity
  field_simp

/-- `exp (l x²)` is integrable against the standard Gaussian for `l < 1 / 2`. -/
theorem integrable_exp_mul_sq_gaussianReal {l : ℝ} (hl : l < 1 / 2) :
    Integrable (fun x : ℝ => Real.exp (l * x ^ 2)) (gaussianReal 0 1) := by
  rw [gaussianReal_of_var_ne_zero 0 one_ne_zero,
    integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF 0 1)
      (ae_of_all _ fun _ => gaussianPDF_lt_top)]
  have h : (fun x : ℝ => (gaussianPDF 0 1 x).toReal • Real.exp (l * x ^ 2)) =
      fun x => (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(1 / 2 - l) * x ^ 2) := by
    funext x
    rw [toReal_gaussianPDF, smul_eq_mul, gaussianPDFReal_zero_one_mul_exp_sq]
  simp_rw [h]
  exact (integrable_exp_neg_mul_sq (by linarith)).const_mul _

end ProbabilityTheory
