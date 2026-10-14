/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Probability.Moments.GaussianExp
public import Mathlib.Probability.Moments.SubGaussian

/-!
# Exponential moments of `|X|` for sub-Gaussian variables

The truncation estimates of `SpinGlasses/AsymptoticGibbsApproximation.lean` need only the crude
bound `𝔼 exp (t |X|) ≤ 2 exp (c t² / 2)` (`HasSubgaussianMGF.integral_exp_abs_mul_le`) for the
coordinates of a Gaussian family, which in turn follows from the moment generating function of a
centered Gaussian with `𝔼 X² ≤ v` (`HasGaussianLaw.hasSubgaussianMGF_of_integral_sq_le`).
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- A centered Gaussian variable with second moment at most `v` is sub-Gaussian with parameter
`v`. -/
theorem HasGaussianLaw.hasSubgaussianMGF_of_integral_sq_le {Z : Ω → ℝ}
    (hZ : HasGaussianLaw Z μ) (h0 : ∫ ω, Z ω ∂μ = 0) {v : ℝ} (hv : ∫ ω, Z ω ^ 2 ∂μ ≤ v) :
    HasSubgaussianMGF Z v.toNNReal μ := by
  have hvar : Var[Z; μ] = ∫ ω, Z ω ^ 2 ∂μ := by
    rw [variance_of_integral_eq_zero hZ.aemeasurable h0]
  refine ⟨integrable_exp_mul_of_hasGaussianLaw hZ, fun t => ?_⟩
  rw [mgf, integral_exp_mul_of_hasGaussianLaw hZ, h0, mul_zero, zero_add, hvar]
  refine Real.exp_le_exp.2 ?_
  have : (∫ ω, Z ω ^ 2 ∂μ) ≤ (v.toNNReal : ℝ) := hv.trans (Real.le_coe_toNNReal v)
  nlinarith [sq_nonneg t]

/-- **Exponential moments of `|X|`.**  If `X` is measurable and sub-Gaussian with parameter `c`,
then `exp (t |X|)` is integrable and `𝔼 exp (t |X|) ≤ 2 exp (c t² / 2)`. -/
theorem HasSubgaussianMGF.integral_exp_abs_mul_le {X : Ω → ℝ} {c : ℝ≥0}
    (h : HasSubgaussianMGF X c μ) (hX : Measurable X) (t : ℝ) :
    Integrable (fun ω => Real.exp (t * |X ω|)) μ ∧
      ∫ ω, Real.exp (t * |X ω|) ∂μ ≤ 2 * Real.exp (c * t ^ 2 / 2) := by
  have hle : ∀ ω, Real.exp (t * |X ω|) ≤ Real.exp (t * X ω) + Real.exp ((-t) * X ω) := fun ω => by
    rcases le_total 0 (X ω) with hx | hx
    · rw [abs_of_nonneg hx]
      exact le_add_of_nonneg_right (Real.exp_pos _).le
    · rw [abs_of_nonpos hx, show t * -X ω = (-t) * X ω by ring]
      exact le_add_of_nonneg_left (Real.exp_pos _).le
  have hint : Integrable (fun ω => Real.exp (t * X ω) + Real.exp ((-t) * X ω)) μ :=
    (h.integrable_exp_mul t).add (h.integrable_exp_mul (-t))
  have hI : Integrable (fun ω => Real.exp (t * |X ω|)) μ :=
    hint.mono' (by fun_prop) (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact hle ω)
  refine ⟨hI, (integral_mono hI hint hle).trans ?_⟩
  rw [integral_add (h.integrable_exp_mul t) (h.integrable_exp_mul (-t))]
  have h1 := h.mgf_le t
  have h2 := h.mgf_le (-t)
  rw [mgf] at h1 h2
  rw [neg_sq] at h2
  linarith

/-- A sub-Gaussian variable is integrable. -/
theorem HasSubgaussianMGF.integrable_of_measurable {X : Ω → ℝ} {c : ℝ≥0}
    (h : HasSubgaussianMGF X c μ) (hX : Measurable X) : Integrable X μ := by
  refine ((h.integral_exp_abs_mul_le hX 1).1).mono' hX.aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, one_mul]
  linarith [Real.add_one_le_exp |X ω|, abs_nonneg (X ω)]

/-- `cosh X` is integrable for a sub-Gaussian `X`. -/
theorem HasSubgaussianMGF.integrable_two_cosh {X : Ω → ℝ} {c : ℝ≥0}
    (h : HasSubgaussianMGF X c μ) :
    Integrable (fun ω => 2 * Real.cosh (X ω)) μ := by
  have := (h.integrable_exp_mul 1).add (h.integrable_exp_mul (-1))
  refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
  simp only [Pi.add_apply, one_mul, neg_mul, Real.cosh_eq]
  ring

/-- `𝔼 2 cosh X ≤ 2 exp (c / 2)` for a sub-Gaussian `X` with parameter `c`. -/
theorem HasSubgaussianMGF.integral_two_cosh_le {X : Ω → ℝ} {c : ℝ≥0}
    (h : HasSubgaussianMGF X c μ) :
    ∫ ω, 2 * Real.cosh (X ω) ∂μ ≤ 2 * Real.exp (c / 2) := by
  have h1 := h.mgf_le 1
  have h2 := h.mgf_le (-1)
  rw [mgf] at h1 h2
  have : ∫ ω, 2 * Real.cosh (X ω) ∂μ =
      (∫ ω, Real.exp (1 * X ω) ∂μ) + ∫ ω, Real.exp ((-1) * X ω) ∂μ := by
    rw [← integral_add (h.integrable_exp_mul 1) (h.integrable_exp_mul (-1))]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    simp only [one_mul, neg_mul, Real.cosh_eq]
    ring
  rw [this]
  norm_num at h1 h2 ⊢
  linarith

/-- `𝔼 exp X ≤ exp (c / 2)` for a sub-Gaussian `X` with parameter `c`. -/
theorem HasSubgaussianMGF.integral_exp_le {X : Ω → ℝ} {c : ℝ≥0}
    (h : HasSubgaussianMGF X c μ) :
    ∫ ω, Real.exp (X ω) ∂μ ≤ Real.exp (c / 2) := by
  have := h.mgf_le 1
  rw [mgf] at this
  simpa using this

end ProbabilityTheory
