/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.NTK.ChoSaulAngular
public import Mathlib.MeasureTheory.Integral.Gamma

/-!
# Polar-Coordinate Evaluation of the Cho-Saul Kernel

This file separates the two-dimensional standard Gaussian integrals into radial and angular
factors. The angular factors are supplied by `ChoSaulAngular`; the exported lemmas give the
ReLU and ReLU-indicator formulas for directions separated by an angle `theta`.
-/
@[expose] public section

open Real MeasureTheory MeasureTheory.Measure ProbabilityTheory Set

namespace NTK

lemma integral_prod_stdGaussian_eq_density (f : ℝ × ℝ → ℝ) :
    ∫ p, f p ∂((gaussianReal 0 1).prod (gaussianReal 0 1)) =
      ∫ p, gaussianPDFReal 0 1 p.1 * gaussianPDFReal 0 1 p.2 * f p := by
  rw [gaussianReal_of_var_ne_zero (0 : ℝ) (by norm_num : (1 : NNReal) ≠ 0)]
  rw [prod_withDensity₀ (measurable_gaussianPDF 0 1).aemeasurable
    (measurable_gaussianPDF 0 1).aemeasurable]
  rw [integral_withDensity_eq_integral_toReal_smul
    (show Measurable (fun p : ℝ × ℝ => gaussianPDF 0 1 p.1 * gaussianPDF 0 1 p.2) by
      fun_prop)
    (ae_of_all _ fun p => ENNReal.mul_lt_top (gaussianPDF_lt_top (x := p.1))
      (gaussianPDF_lt_top (x := p.2)))]
  simp only [ENNReal.toReal_mul, toReal_gaussianPDF, smul_eq_mul]
  rw [volume_eq_prod]

lemma integral_radial_gaussian_one :
    ∫ r in Set.Ioi (0 : ℝ), r * Real.exp (-(1 / 2 : ℝ) * r ^ 2) = 1 := by
  have h := integral_rpow_mul_exp_neg_mul_rpow
    (p := (2 : ℝ)) (q := (1 : ℝ)) (b := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
      (by norm_num)
  calc
    _ = ∫ r in Set.Ioi (0 : ℝ), r ^ (1 : ℝ) *
        Real.exp (-(1 / 2 : ℝ) * r ^ (2 : ℝ)) := by
          apply setIntegral_congr_fun measurableSet_Ioi
          intro r _
          norm_num [Real.rpow_one, Real.rpow_natCast]
    _ = (1 / 2 : ℝ) ^ (-(1 + 1 : ℝ) / 2) * (1 / 2) * Real.Gamma ((1 + 1) / 2) := h
    _ = 1 := by norm_num [Real.rpow_neg_one, Real.Gamma_one]

lemma integral_radial_gaussian_three :
    ∫ r in Set.Ioi (0 : ℝ), r ^ 3 * Real.exp (-(1 / 2 : ℝ) * r ^ 2) = 2 := by
  have h := integral_rpow_mul_exp_neg_mul_rpow
    (p := (2 : ℝ)) (q := (3 : ℝ)) (b := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
      (by norm_num)
  have hGamma : Real.Gamma 2 = 1 := by
    simp
  calc
    _ = ∫ r in Set.Ioi (0 : ℝ), r ^ (3 : ℝ) *
        Real.exp (-(1 / 2 : ℝ) * r ^ (2 : ℝ)) := by
          apply setIntegral_congr_fun measurableSet_Ioi
          intro r _
          norm_num [Real.rpow_natCast]
    _ = (1 / 2 : ℝ) ^ (-(3 + 1 : ℝ) / 2) * (1 / 2) * Real.Gamma ((3 + 1) / 2) := h
    _ = 2 := by norm_num [hGamma, Real.rpow_intCast]

lemma stdGaussian_density_polar (r phi : ℝ) :
    gaussianPDFReal 0 1 (r * Real.cos phi) *
        gaussianPDFReal 0 1 (r * Real.sin phi) =
      (1 / (2 * Real.pi)) * Real.exp (-(1 / 2 : ℝ) * r ^ 2) := by
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  calc
    _ = (Real.sqrt (2 * Real.pi))⁻¹ * (Real.sqrt (2 * Real.pi))⁻¹ *
        (Real.exp (-(r * Real.cos phi) ^ 2 / 2) *
          Real.exp (-(r * Real.sin phi) ^ 2 / 2)) := by ring
    _ = (Real.sqrt (2 * Real.pi))⁻¹ * (Real.sqrt (2 * Real.pi))⁻¹ *
        Real.exp (-(r * Real.cos phi) ^ 2 / 2 + -(r * Real.sin phi) ^ 2 / 2) := by
          rw [Real.exp_add]
    _ = (1 / (2 * Real.pi)) * Real.exp (-(1 / 2 : ℝ) * r ^ 2) := by
          have hcoeff : (Real.sqrt (2 * Real.pi))⁻¹ * (Real.sqrt (2 * Real.pi))⁻¹ =
              1 / (2 * Real.pi) := by
            rw [← mul_inv, Real.mul_self_sqrt (by positivity : 0 ≤ 2 * Real.pi)]
            simp [one_div]
          rw [hcoeff]
          have harg : -(r * Real.cos phi) ^ 2 / 2 + -(r * Real.sin phi) ^ 2 / 2 =
              -(1 / 2 : ℝ) * r ^ 2 := by
            nlinarith [Real.sin_sq_add_cos_sq phi]
          rw [harg]

private lemma relu_pos_mul_polar (c x : ℝ) (hc : 0 ≤ c) :
    relu (c * x) = c * relu x := by
  simp only [relu]
  rcases le_total 0 x with hx | hx
  · rw [max_eq_left hx, max_eq_left (mul_nonneg hc hx)]
  · rw [max_eq_right hx, mul_zero, max_eq_right (mul_nonpos_of_nonneg_of_nonpos hc hx)]

private lemma integral_prod_stdGaussian_relu_of_angular
    (theta : ℝ)
    (hangular :
      ∫ phi in Set.Ioo (-Real.pi) Real.pi,
        relu (Real.cos phi) * relu (Real.cos (phi - theta)) =
        (Real.sin theta + (Real.pi - theta) * Real.cos theta) / 2) :
    ∫ p, relu p.1 *
        relu (Real.cos theta * p.1 + Real.sin theta * p.2)
      ∂((gaussianReal 0 1).prod (gaussianReal 0 1)) =
      (Real.sin theta + (Real.pi - theta) * Real.cos theta) / (2 * Real.pi) := by
  rw [integral_prod_stdGaussian_eq_density]
  rw [← integral_comp_polarCoord_symm]
  rw [polarCoord_target]
  have hpullback :
      ∫ p in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi,
        p.1 • (gaussianPDFReal 0 1 (polarCoord.symm p).1 *
          gaussianPDFReal 0 1 (polarCoord.symm p).2 *
          (relu (polarCoord.symm p).1 *
            relu (Real.cos theta * (polarCoord.symm p).1 +
              Real.sin theta * (polarCoord.symm p).2))) =
      ∫ p in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi,
        ((1 / (2 * Real.pi)) *
          (p.1 ^ 3 * Real.exp (-(1 / 2 : ℝ) * p.1 ^ 2))) *
          (relu (Real.cos p.2) * relu (Real.cos (p.2 - theta))) := by
    apply setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo)
    intro p hp
    have hr : 0 ≤ p.1 := hp.1.le
    change p.1 * (gaussianPDFReal 0 1 (p.1 * Real.cos p.2) *
      gaussianPDFReal 0 1 (p.1 * Real.sin p.2) *
      (relu (p.1 * Real.cos p.2) *
        relu (Real.cos theta * (p.1 * Real.cos p.2) +
          Real.sin theta * (p.1 * Real.sin p.2)))) = _
    rw [stdGaussian_density_polar]
    rw [relu_pos_mul_polar p.1 (Real.cos p.2) hr]
    have hlinear : Real.cos theta * (p.1 * Real.cos p.2) +
        Real.sin theta * (p.1 * Real.sin p.2) = p.1 * Real.cos (p.2 - theta) := by
      rw [Real.cos_sub]
      ring
    rw [hlinear, relu_pos_mul_polar p.1 (Real.cos (p.2 - theta)) hr]
    ring
  rw [hpullback]
  calc
    ∫ p in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi,
        ((1 / (2 * Real.pi)) *
          (p.1 ^ 3 * Real.exp (-(1 / 2 : ℝ) * p.1 ^ 2))) *
          (relu (Real.cos p.2) * relu (Real.cos (p.2 - theta))) =
      (∫ r in Set.Ioi (0 : ℝ),
          (1 / (2 * Real.pi)) * (r ^ 3 * Real.exp (-(1 / 2 : ℝ) * r ^ 2))) *
        (∫ phi in Set.Ioo (-Real.pi) Real.pi,
          relu (Real.cos phi) * relu (Real.cos (phi - theta))) := by
            rw [← setIntegral_prod_mul, volume_eq_prod]
    _ = ((1 / (2 * Real.pi)) * 2) *
        ((Real.sin theta + (Real.pi - theta) * Real.cos theta) / 2) := by
          rw [integral_const_mul, integral_radial_gaussian_three, hangular]
    _ = (Real.sin theta + (Real.pi - theta) * Real.cos theta) /
        (2 * Real.pi) := by
          field_simp [Real.pi_ne_zero]

private lemma reluIndicator_pos_mul_polar (c x : ℝ) (hc : 0 < c) :
    reluIndicator (c * x) = reluIndicator x := by
  simp only [reluIndicator]
  rw [if_congr (mul_nonneg_iff_of_pos_left hc) rfl rfl]

private lemma integral_prod_stdGaussian_reluIndicator_of_angular
    (theta : ℝ)
    (hangular :
      ∫ phi in Set.Ioo (-Real.pi) Real.pi,
        reluIndicator (Real.cos phi) * reluIndicator (Real.cos (phi - theta)) =
        Real.pi - theta) :
    ∫ p, reluIndicator p.1 *
        reluIndicator (Real.cos theta * p.1 + Real.sin theta * p.2)
      ∂((gaussianReal 0 1).prod (gaussianReal 0 1)) =
      (Real.pi - theta) / (2 * Real.pi) := by
  rw [integral_prod_stdGaussian_eq_density]
  rw [← integral_comp_polarCoord_symm]
  rw [polarCoord_target]
  have hpullback :
      ∫ p in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi,
        p.1 • (gaussianPDFReal 0 1 (polarCoord.symm p).1 *
          gaussianPDFReal 0 1 (polarCoord.symm p).2 *
          (reluIndicator (polarCoord.symm p).1 *
            reluIndicator (Real.cos theta * (polarCoord.symm p).1 +
              Real.sin theta * (polarCoord.symm p).2))) =
      ∫ p in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi,
        ((1 / (2 * Real.pi)) *
          (p.1 * Real.exp (-(1 / 2 : ℝ) * p.1 ^ 2))) *
          (reluIndicator (Real.cos p.2) * reluIndicator (Real.cos (p.2 - theta))) := by
    apply setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo)
    intro p hp
    have hr : 0 < p.1 := hp.1
    change p.1 * (gaussianPDFReal 0 1 (p.1 * Real.cos p.2) *
      gaussianPDFReal 0 1 (p.1 * Real.sin p.2) *
      (reluIndicator (p.1 * Real.cos p.2) *
        reluIndicator (Real.cos theta * (p.1 * Real.cos p.2) +
          Real.sin theta * (p.1 * Real.sin p.2)))) = _
    rw [stdGaussian_density_polar]
    rw [reluIndicator_pos_mul_polar p.1 (Real.cos p.2) hr]
    have hlinear : Real.cos theta * (p.1 * Real.cos p.2) +
        Real.sin theta * (p.1 * Real.sin p.2) = p.1 * Real.cos (p.2 - theta) := by
      rw [Real.cos_sub]
      ring
    rw [hlinear, reluIndicator_pos_mul_polar p.1 (Real.cos (p.2 - theta)) hr]
    ring
  rw [hpullback]
  calc
    ∫ p in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi,
        ((1 / (2 * Real.pi)) *
          (p.1 * Real.exp (-(1 / 2 : ℝ) * p.1 ^ 2))) *
          (reluIndicator (Real.cos p.2) * reluIndicator (Real.cos (p.2 - theta))) =
      (∫ r in Set.Ioi (0 : ℝ),
          (1 / (2 * Real.pi)) * (r * Real.exp (-(1 / 2 : ℝ) * r ^ 2))) *
        (∫ phi in Set.Ioo (-Real.pi) Real.pi,
          reluIndicator (Real.cos phi) * reluIndicator (Real.cos (phi - theta))) := by
            rw [← setIntegral_prod_mul, volume_eq_prod]
    _ = (1 / (2 * Real.pi)) * (Real.pi - theta) := by
          rw [integral_const_mul, integral_radial_gaussian_one, hangular, mul_one]
    _ = (Real.pi - theta) / (2 * Real.pi) := by ring

/-- The ReLU product for two unit Gaussian projections separated by angle `theta`. -/
lemma integral_prod_stdGaussian_relu
    (theta : ℝ) (htheta0 : 0 ≤ theta) (hthetapi : theta ≤ Real.pi) :
    ∫ p, relu p.1 * relu (Real.cos theta * p.1 + Real.sin theta * p.2)
      ∂((gaussianReal 0 1).prod (gaussianReal 0 1)) =
      (Real.sin theta + (Real.pi - theta) * Real.cos theta) / (2 * Real.pi) :=
  integral_prod_stdGaussian_relu_of_angular theta
    (angular_relu_integral theta htheta0 hthetapi)

/-- The common-positive-halfspace probability for two unit Gaussian projections separated by
angle `theta`. -/
lemma integral_prod_stdGaussian_reluIndicator
    (theta : ℝ) (htheta0 : 0 ≤ theta) (hthetapi : theta ≤ Real.pi) :
    ∫ p, reluIndicator p.1 *
        reluIndicator (Real.cos theta * p.1 + Real.sin theta * p.2)
      ∂((gaussianReal 0 1).prod (gaussianReal 0 1)) =
      (Real.pi - theta) / (2 * Real.pi) :=
  integral_prod_stdGaussian_reluIndicator_of_angular theta
    (angular_indicator_integral theta htheta0 hthetapi)

private lemma continuous_relu_polar : Continuous relu :=
  continuous_id.max continuous_const

private lemma integral_stdGaussian_fin2_eq_prod
    (g : ℝ × ℝ → ℝ)
    (hg : AEStronglyMeasurable g
      (Measure.map (fun t : Fin 2 → ℝ => (t 0, t 1)) (gaussianRowMeasure 2))) :
    ∫ z : EuclideanSpace ℝ (Fin 2), g (z.ofLp 0, z.ofLp 1)
      ∂(stdGaussian (EuclideanSpace ℝ (Fin 2))) =
    ∫ p, g p ∂((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
  have hrow := integral_gaussianRowMeasure_eq_integral_stdGaussian
    (f := fun w : Fin 2 → ℝ => g (w 0, w 1))
  rw [← hrow]
  have hmap := map_pi_eval_two (d := 2) (by norm_num)
    (μ := fun _ : Fin 2 => gaussianReal 0 1)
  change Measure.map (fun t : Fin 2 → ℝ => (t 0, t 1)) (gaussianRowMeasure 2) =
      (gaussianReal 0 1).prod (gaussianReal 0 1) at hmap
  rw [← hmap, integral_map (by fun_prop) hg]

/-- Coordinate form of `integral_prod_stdGaussian_relu` on two-dimensional Euclidean Gaussian
space. -/
lemma integral_stdGaussian_relu_angle
    (theta : ℝ) (htheta0 : 0 ≤ theta) (hthetapi : theta ≤ Real.pi) :
    ∫ z : EuclideanSpace ℝ (Fin 2),
        relu (z.ofLp 0) *
          relu (Real.cos theta * z.ofLp 0 + Real.sin theta * z.ofLp 1)
      ∂(stdGaussian (EuclideanSpace ℝ (Fin 2))) =
      (Real.sin theta + (Real.pi - theta) * Real.cos theta) / (2 * Real.pi) := by
  have hmeas : AEStronglyMeasurable
      (fun p : ℝ × ℝ => relu p.1 *
        relu (Real.cos theta * p.1 + Real.sin theta * p.2))
      (Measure.map (fun t : Fin 2 → ℝ => (t 0, t 1)) (gaussianRowMeasure 2)) := by
    apply Continuous.aestronglyMeasurable
    exact (continuous_relu_polar.comp continuous_fst).mul
      (continuous_relu_polar.comp
        ((continuous_const.mul continuous_fst).add (continuous_const.mul continuous_snd)))
  calc
    _ = ∫ p, relu p.1 * relu (Real.cos theta * p.1 + Real.sin theta * p.2)
          ∂((gaussianReal 0 1).prod (gaussianReal 0 1)) :=
      integral_stdGaussian_fin2_eq_prod _ hmeas
    _ = _ := integral_prod_stdGaussian_relu theta htheta0 hthetapi

/-- Coordinate form of `integral_prod_stdGaussian_reluIndicator` on two-dimensional Euclidean
Gaussian space. -/
lemma integral_stdGaussian_reluIndicator_angle
    (theta : ℝ) (htheta0 : 0 ≤ theta) (hthetapi : theta ≤ Real.pi) :
    ∫ z : EuclideanSpace ℝ (Fin 2),
        reluIndicator (z.ofLp 0) *
          reluIndicator (Real.cos theta * z.ofLp 0 + Real.sin theta * z.ofLp 1)
      ∂(stdGaussian (EuclideanSpace ℝ (Fin 2))) =
      (Real.pi - theta) / (2 * Real.pi) := by
  have hmeas : AEStronglyMeasurable
      (fun p : ℝ × ℝ => reluIndicator p.1 *
        reluIndicator (Real.cos theta * p.1 + Real.sin theta * p.2))
      (Measure.map (fun t : Fin 2 → ℝ => (t 0, t 1)) (gaussianRowMeasure 2)) := by
    apply StronglyMeasurable.aestronglyMeasurable
    exact ((measurable_reluIndicator.comp measurable_fst).mul
      (measurable_reluIndicator.comp
        ((measurable_const.mul measurable_fst).add
          (measurable_const.mul measurable_snd)))).stronglyMeasurable
  calc
    _ = ∫ p, reluIndicator p.1 *
          reluIndicator (Real.cos theta * p.1 + Real.sin theta * p.2)
          ∂((gaussianReal 0 1).prod (gaussianReal 0 1)) :=
      integral_stdGaussian_fin2_eq_prod _ hmeas
    _ = _ := integral_prod_stdGaussian_reluIndicator theta htheta0 hthetapi

end NTK
