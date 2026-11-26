/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# The exponential of a Gaussian square

`𝔼 exp (l g²) = (1 - 2 l)^{-1/2}` for a standard Gaussian `g` and `l < 1 / 2`, and the bound
`𝔼 exp (l g²) ≤ 2` for a centred Gaussian `g` of variance `v` with `l v ≤ 1 / 4`, also for
`g = ∑ i, w i x i` a linear combination of independent standard Gaussians.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal

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

/-- For `g ~ 𝒩(0, v)` and `l v ≤ 1 / 4`, `𝔼 exp (l g²)` is finite and at most `2`. -/
theorem integral_exp_mul_sq_gaussianReal_le_two {l : ℝ} {v : ℝ≥0} (hlv : l * v ≤ 1 / 4) :
    Integrable (fun x : ℝ => Real.exp (l * x ^ 2)) (gaussianReal 0 v) ∧
      ∫ x, Real.exp (l * x ^ 2) ∂(gaussianReal 0 v) ≤ 2 := by
  have hmap : (gaussianReal 0 1).map (fun x => Real.sqrt v * x) = gaussianReal 0 v := by
    rw [gaussianReal_map_const_mul, mul_zero, mul_one]
    congr 1
    exact NNReal.eq (Real.sq_sqrt v.2)
  have hm : AEMeasurable (fun x : ℝ => Real.sqrt v * x) (gaussianReal 0 1) :=
    (measurable_id.const_mul _).aemeasurable
  have hg : Continuous fun x : ℝ => Real.exp (l * x ^ 2) := by fun_prop
  have e : (fun x => Real.exp (l * (Real.sqrt v * x) ^ 2)) =
      fun x => Real.exp (l * v * x ^ 2) := by
    funext x
    rw [mul_pow, Real.sq_sqrt v.coe_nonneg, mul_assoc]
  have hlt : l * v < 1 / 2 := hlv.trans_lt (by norm_num)
  rw [← hmap, integrable_map_measure hg.aestronglyMeasurable hm,
    integral_map hm hg.aestronglyMeasurable]
  refine ⟨?_, ?_⟩
  · change Integrable (fun x => Real.exp (l * (Real.sqrt v * x) ^ 2)) (gaussianReal 0 1)
    rw [e]
    exact integrable_exp_mul_sq_gaussianReal hlt
  · rw [e, integral_exp_mul_sq_gaussianReal hlt]
    have h1 : (1 / 4 : ℝ) ≤ 1 - 2 * (l * v) := by linarith
    have h2 : 1 / 2 ≤ Real.sqrt (1 - 2 * (l * v)) := by
      rw [show (1 / 2 : ℝ) = Real.sqrt (1 / 4) by
        rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt h1
    exact (inv_anti₀ (by norm_num) h2).trans_eq (by norm_num)

/-- A linear combination `∑ i, w i x i` of independent standard Gaussians is
`𝒩(0, ∑ i, w i²)`. -/
theorem map_pi_gaussianReal_sum_mul {ι : Type*} [Fintype ι] (w : ι → ℝ) :
    (Measure.pi fun _ : ι => gaussianReal 0 1).map (fun x => ∑ i, w i * x i) =
      gaussianReal 0 (∑ i, w i ^ 2).toNNReal := by
  set L : StrongDual ℝ (EuclideanSpace ℝ ι) := innerSL ℝ (WithLp.toLp 2 w) with hL
  have e : (fun x : ι → ℝ => ∑ i, w i * x i) = L ∘ WithLp.toLp 2 := by
    funext x
    simp only [hL, Function.comp_apply, innerSL_apply_apply, PiLp.inner_apply, RCLike.inner_apply,
      conj_trivial]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [e, ← Measure.map_map L.continuous.measurable (by fun_prop), map_pi_eq_stdGaussian,
    IsGaussian.map_eq_gaussianReal L, integral_strongDual_stdGaussian, variance_dual_stdGaussian]
  congr 2
  rw [hL, innerSL_apply_norm, EuclideanSpace.real_norm_sq_eq]

/-- `𝔼 exp (l (∑ i, w i x i)²) ≤ 2` for independent standard Gaussians `x i` and
`l ∑ i, w i² ≤ 1 / 4`. -/
theorem integral_exp_mul_sq_sum_pi_gaussianReal_le_two {ι : Type*} [Fintype ι] (w : ι → ℝ)
    {l : ℝ} (hlw : l * ∑ i, w i ^ 2 ≤ 1 / 4) :
    Integrable (fun x : ι → ℝ => Real.exp (l * (∑ i, w i * x i) ^ 2))
        (Measure.pi fun _ : ι => gaussianReal 0 1) ∧
      ∫ x, Real.exp (l * (∑ i, w i * x i) ^ 2) ∂(Measure.pi fun _ : ι => gaussianReal 0 1)
        ≤ 2 := by
  have hs : 0 ≤ ∑ i, w i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h := integral_exp_mul_sq_gaussianReal_le_two (l := l) (v := (∑ i, w i ^ 2).toNNReal)
    (by rwa [Real.coe_toNNReal _ hs])
  rw [← map_pi_gaussianReal_sum_mul] at h
  have hm : AEMeasurable (fun x : ι → ℝ => ∑ i, w i * x i)
      (Measure.pi fun _ : ι => gaussianReal 0 1) :=
    (Finset.measurable_sum _ fun i _ => (measurable_pi_apply i).const_mul _).aemeasurable
  have hg : Continuous fun x : ℝ => Real.exp (l * x ^ 2) := by fun_prop
  rw [integrable_map_measure hg.aestronglyMeasurable hm,
    integral_map hm hg.aestronglyMeasurable] at h
  exact h

end ProbabilityTheory
