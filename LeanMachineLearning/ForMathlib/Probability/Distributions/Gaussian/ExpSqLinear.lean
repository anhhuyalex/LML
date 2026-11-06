/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Probability.Distributions.Gaussian.ExpSq

/-!
# The exponential of a Gaussian square plus a linear term

`𝔼 exp (l g² + c g) = (1 - 2 l)^{-1/2} exp (c² / (2 (1 - 2 l)))` for a standard Gaussian `g` and
`l < 1 / 2`. The proof completes the square in the Gaussian density.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory

/-- **Gaussian exponential of a quadratic:** for `l < 1 / 2`,
`∫ exp (l x² + c x) d𝒩(0, 1) = (√(1 - 2 l))⁻¹ exp (c² / (2 (1 - 2 l)))`. -/
theorem integral_exp_mul_sq_add_mul_gaussianReal {l : ℝ} (hl : l < 1 / 2) (c : ℝ) :
    ∫ x, Real.exp (l * x ^ 2 + c * x) ∂(gaussianReal 0 1) =
      (Real.sqrt (1 - 2 * l))⁻¹ * Real.exp (c ^ 2 / (2 * (1 - 2 * l))) := by
  have hu : 0 < 1 / 2 - l := by linarith
  have h1 : 0 < 1 - 2 * l := by linarith
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero]
  have hpt (x : ℝ) : gaussianPDFReal 0 1 x • Real.exp (l * x ^ 2 + c * x) =
      (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (c ^ 2 / (4 * (1 / 2 - l))) *
        Real.exp (-(1 / 2 - l) * (x - c / (2 * (1 / 2 - l))) ^ 2) := by
    rw [smul_eq_mul, gaussianPDFReal_def]
    simp only [NNReal.coe_one, mul_one, sub_zero]
    rw [mul_assoc, ← Real.exp_add, mul_assoc, ← Real.exp_add]
    congr 2
    field_simp
    ring
  simp_rw [hpt]
  rw [integral_const_mul, integral_sub_right_eq_self
    (fun x : ℝ => Real.exp (-(1 / 2 - l) * x ^ 2)) (c / (2 * (1 / 2 - l))), integral_gaussian]
  have e : Real.pi / (1 / 2 - l) = (2 * Real.pi) * (1 - 2 * l)⁻¹ := by field_simp
  have hs : 0 < Real.sqrt (1 - 2 * l) := Real.sqrt_pos.2 h1
  have hs2 : 0 < Real.sqrt 2 * Real.sqrt Real.pi := by positivity
  rw [e, show (2 * Real.pi) * (1 - 2 * l)⁻¹ = (2 * Real.pi) / (1 - 2 * l) from
    (div_eq_mul_inv _ _).symm, Real.sqrt_div (by positivity), Real.sqrt_mul (by positivity)]
  have e2 : c ^ 2 / (4 * (1 / 2 - l)) = c ^ 2 / (2 * (1 - 2 * l)) := by
    field_simp
    ring
  rw [e2]
  field_simp

/-- `exp (l x² + c x)` is integrable against the standard Gaussian for `l < 1 / 2`. -/
theorem integrable_exp_mul_sq_add_mul_gaussianReal {l : ℝ} (hl : l < 1 / 2) (c : ℝ) :
    Integrable (fun x : ℝ => Real.exp (l * x ^ 2 + c * x)) (gaussianReal 0 1) := by
  rw [gaussianReal_of_var_ne_zero 0 one_ne_zero,
    integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF 0 1)
      (ae_of_all _ fun _ => gaussianPDF_lt_top)]
  have h : (fun x : ℝ => (gaussianPDF 0 1 x).toReal • Real.exp (l * x ^ 2 + c * x)) =
      fun x => (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (c ^ 2 / (4 * (1 / 2 - l))) *
        Real.exp (-(1 / 2 - l) * (x - c / (2 * (1 / 2 - l))) ^ 2) := by
    funext x
    rw [toReal_gaussianPDF, smul_eq_mul, gaussianPDFReal_def]
    simp only [NNReal.coe_one, mul_one, sub_zero]
    have hu : 0 < 1 / 2 - l := by linarith
    have h1 : 1 - 2 * l ≠ 0 := by linarith
    have h2 : 1 - l * 2 ≠ 0 := by linarith
    rw [mul_assoc, ← Real.exp_add, mul_assoc, ← Real.exp_add]
    congr 2
    field_simp
    ring
  simp_rw [h]
  exact ((integrable_exp_neg_mul_sq (by linarith)).comp_sub_right _).const_mul _

end ProbabilityTheory
