/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Analysis.SpecialFunctions.Hyperbolic
public import LeanMachineLearning.ForMathlib.MeasureTheory.Integral.ParametrizedL2
public import LeanMachineLearning.ForMathlib.Probability.Moments.GaussianPiExp
public import LeanMachineLearning.SpinGlasses.SKFixedPoint

/-!
# The fixed point of the SK equation is bounded away from zero when `h ≠ 0`

For `4 β² < 1`, every solution `q` of `q = 𝔼 tanh²(β √q z + h)` with `h ≠ 0` satisfies
`q ≥ (sinh |2h| / (cosh 2h + e^{1/2}))²` (`SpinGlasses.fixedPoint_lower_bound`).  Talagrand
(proof of Lemma 1.7.6) uses `q > 0` for `h ≠ 0` and says that the constant degenerates as
`h → 0`; here it is explicit and independent of `β`.

The proof symmetrizes `z ↦ -z`: `tanh (h + x) + tanh (h - x) = 2 sinh 2h / (cosh 2h + cosh 2x)`
(`Real.tanh_add_tanh_sub`), bounds `1/y ≥ 2/D - y/D²` (tangent line) and integrates with
`𝔼 cosh (2 s z) = e^{2 s²} ≤ e^{1/2}`; then `q = 𝔼 tanh² ≥ (𝔼 tanh)²` (Jensen).

## References

* M. Talagrand, *Spin Glasses: A Challenge for Mathematicians*, Vol. I, proof of Lemma 1.7.6.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace Real

/-- `tanh (h + x) + tanh (h - x) = 2 sinh (2 h) / (cosh (2 h) + cosh (2 x))`. -/
theorem tanh_add_tanh_sub (h x : ℝ) :
    Real.tanh (h + x) + Real.tanh (h - x) =
      2 * Real.sinh (2 * h) / (Real.cosh (2 * h) + Real.cosh (2 * x)) := by
  have h1 := Real.cosh_pos (h + x)
  have h2 := Real.cosh_pos (h - x)
  have hsum : Real.sinh (h + x) * Real.cosh (h - x) + Real.cosh (h + x) * Real.sinh (h - x) =
      Real.sinh (2 * h) := by
    rw [← Real.sinh_add]; ring_nf
  have hprod : Real.cosh (h + x) * Real.cosh (h - x) =
      (Real.cosh (2 * h) + Real.cosh (2 * x)) / 2 := by
    rw [Real.cosh_mul_cosh]; ring_nf
  have hc : 0 < Real.cosh (2 * h) + Real.cosh (2 * x) := by
    have := Real.cosh_pos (2 * h); have := Real.cosh_pos (2 * x); linarith
  rw [Real.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh, div_add_div _ _ h1.ne' h2.ne',
    show Real.sinh (h + x) * Real.cosh (h - x) + Real.cosh (h + x) * Real.sinh (h - x) =
      Real.sinh (2 * h) from hsum, hprod]
  field_simp

end Real

namespace SpinGlasses

/-- The tangent-line bound `1/y ≥ 2/D - y/D²` for `y, D > 0`. -/
theorem two_div_sub_div_sq_le_inv {y D : ℝ} (hy : 0 < y) (hD : 0 < D) :
    2 / D - y / D ^ 2 ≤ 1 / y := by
  rw [div_sub_div _ _ hD.ne' (by positivity), div_le_div_iff₀ (by positivity) hy]
  nlinarith [sq_nonneg (y - D), mul_pos hD hD, mul_pos hy hD]

/-- For `h > 0` and `s² ≤ 1/4`, `𝔼 tanh (s z + h) ≥ sinh 2h / (cosh 2h + e^{1/2})`. -/
theorem integral_tanh_affine_lower {s h : ℝ} (hh : 0 < h) (hs : s ^ 2 ≤ 1 / 4) :
    Real.sinh (2 * h) / (Real.cosh (2 * h) + Real.exp (1 / 2)) ≤
      ∫ z : ℝ, Real.tanh (s * z + h) ∂(gaussianReal 0 1) := by
  set γ : Measure ℝ := gaussianReal 0 1 with hγ
  set D : ℝ := Real.cosh (2 * h) + Real.exp (1 / 2) with hD
  have hDpos : 0 < D := by have := Real.cosh_pos (2 * h); positivity
  have hsinh : 0 < Real.sinh (2 * h) := Real.sinh_pos_iff.mpr (by linarith)
  have hint : ∀ t : ℝ, Integrable (fun z : ℝ => Real.tanh (t * z + h)) γ := fun t =>
    (integrable_const (1 : ℝ)).mono' (continuous_tanh_affine t h).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs]; exact (Real.abs_tanh_lt_one _).le)
  -- symmetrization
  have hneg : ∫ z : ℝ, Real.tanh (s * z + h) ∂γ = ∫ z : ℝ, Real.tanh (h - s * z) ∂γ := by
    have hmap : γ.map (fun x : ℝ => -x) = γ := by
      simpa [hγ] using (gaussianReal_map_neg (μ := (0 : ℝ)) (v := 1))
    conv_lhs => rw [← hmap]
    rw [integral_map (by fun_prop) (continuous_tanh_affine s h).aestronglyMeasurable]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only [mul_neg]; ring_nf
  have hsym : ∫ z : ℝ, Real.tanh (s * z + h) ∂γ =
      ∫ z : ℝ, Real.sinh (2 * h) / (Real.cosh (2 * h) + Real.cosh (2 * (s * z))) ∂γ := by
    have h2 : 2 * ∫ z : ℝ, Real.tanh (s * z + h) ∂γ =
        ∫ z : ℝ, (Real.tanh (h + s * z) + Real.tanh (h - s * z)) ∂γ := by
      rw [integral_add, two_mul]
      · congr 1
        exact integral_congr_ae (Filter.Eventually.of_forall fun z => by simp [add_comm])
      · exact (hint s).congr (Filter.Eventually.of_forall fun z => by simp [add_comm])
      · simpa [sub_eq_add_neg, neg_mul, add_comm] using hint (-s)
    have h3 : ∫ z : ℝ, (Real.tanh (h + s * z) + Real.tanh (h - s * z)) ∂γ =
        2 * ∫ z : ℝ, Real.sinh (2 * h) / (Real.cosh (2 * h) + Real.cosh (2 * (s * z))) ∂γ := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      simp only []
      rw [Real.tanh_add_tanh_sub]; ring
    linarith
  rw [hsym]
  -- tangent-line lower bound and the Gaussian mean of `cosh (2 s z)`
  have hcosh : ∫ z : ℝ, Real.cosh (2 * (s * z)) ∂γ = Real.exp (2 * s ^ 2) := by
    have e1 := integral_exp_mul_gaussianReal_zero_one (2 * s)
    have e2 := integral_exp_mul_gaussianReal_zero_one (-(2 * s))
    have i1 := integrable_exp_mul_gaussianReal (μ := (0 : ℝ)) (v := 1) (2 * s)
    have i2 := integrable_exp_mul_gaussianReal (μ := (0 : ℝ)) (v := 1) (-(2 * s))
    have : ∫ z : ℝ, Real.cosh (2 * (s * z)) ∂γ =
        (∫ z : ℝ, Real.exp ((2 * s) * z) ∂γ + ∫ z : ℝ, Real.exp (-(2 * s) * z) ∂γ) / 2 := by
      rw [← integral_add i1 i2, ← integral_div]
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      simp only [Real.cosh_eq]
      ring_nf
    rw [this, e1, e2]
    have : (-(2 * s)) ^ 2 / 2 = (2 * s) ^ 2 / 2 := by ring
    rw [this]; ring_nf
  have hcoshint : Integrable (fun z : ℝ => Real.cosh (2 * (s * z))) γ := by
    have i1 := integrable_exp_mul_gaussianReal (μ := (0 : ℝ)) (v := 1) (2 * s)
    have i2 := integrable_exp_mul_gaussianReal (μ := (0 : ℝ)) (v := 1) (-(2 * s))
    refine ((i1.add i2).div_const 2).congr (Filter.Eventually.of_forall fun z => ?_)
    simp only [Real.cosh_eq, Pi.add_apply]; ring_nf
  have hbound : Real.exp (2 * s ^ 2) ≤ Real.exp (1 / 2) := Real.exp_le_exp.mpr (by linarith)
  have hRint : Integrable
      (fun z : ℝ => Real.sinh (2 * h) / (Real.cosh (2 * h) + Real.cosh (2 * (s * z)))) γ := by
    have h1 := Real.cosh_pos (2 * h)
    have h2 : ∀ z : ℝ, 0 < Real.cosh (2 * h) + Real.cosh (2 * (s * z)) := fun z => by
      have := Real.cosh_pos (2 * (s * z)); linarith
    refine (integrable_const (Real.sinh (2 * h) / Real.cosh (2 * h))).mono'
      (Continuous.aestronglyMeasurable (continuous_const.div (by fun_prop)
        fun z => (h2 z).ne')) (Filter.Eventually.of_forall fun z => ?_)
    have h2z := h2 z
    have h3 := Real.cosh_pos (2 * (s * z))
    rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
    exact div_le_div_of_nonneg_left hsinh.le h1 (by linarith)
  have hLint : Integrable (fun z : ℝ => Real.sinh (2 * h) *
      (2 / D - (Real.cosh (2 * h) + Real.cosh (2 * (s * z))) / D ^ 2)) γ :=
    ((integrable_const (2 / D)).sub
      (((integrable_const (Real.cosh (2 * h))).add hcoshint).div_const (D ^ 2))).const_mul _
  have hL : ∫ z : ℝ, Real.sinh (2 * h) *
      (2 / D - (Real.cosh (2 * h) + Real.cosh (2 * (s * z))) / D ^ 2) ∂γ =
      Real.sinh (2 * h) * (2 / D - (Real.cosh (2 * h) + Real.exp (2 * s ^ 2)) / D ^ 2) := by
    have hI1 : Integrable (fun z : ℝ =>
        (Real.cosh (2 * h) + Real.cosh (2 * (s * z))) / D ^ 2) γ :=
      ((integrable_const (Real.cosh (2 * h))).add hcoshint).div_const _
    rw [integral_const_mul, integral_sub (integrable_const _) hI1, integral_div (D ^ 2),
      integral_add (integrable_const _) hcoshint, hcosh]
    simp
  have hpt : ∀ z : ℝ, Real.sinh (2 * h) *
      (2 / D - (Real.cosh (2 * h) + Real.cosh (2 * (s * z))) / D ^ 2) ≤
      Real.sinh (2 * h) / (Real.cosh (2 * h) + Real.cosh (2 * (s * z))) := fun z => by
    have hy : 0 < Real.cosh (2 * h) + Real.cosh (2 * (s * z)) := by
      have := Real.cosh_pos (2 * h); have := Real.cosh_pos (2 * (s * z)); linarith
    calc _ ≤ Real.sinh (2 * h) * (1 / (Real.cosh (2 * h) + Real.cosh (2 * (s * z)))) :=
          mul_le_mul_of_nonneg_left (two_div_sub_div_sq_le_inv hy hDpos) hsinh.le
      _ = _ := by ring
  calc Real.sinh (2 * h) / D = Real.sinh (2 * h) * (2 / D - D / D ^ 2) := by
        field_simp; ring
    _ ≤ Real.sinh (2 * h) *
        (2 / D - (Real.cosh (2 * h) + Real.exp (2 * s ^ 2)) / D ^ 2) := by
        refine mul_le_mul_of_nonneg_left (sub_le_sub_left ?_ _) hsinh.le
        exact div_le_div_of_nonneg_right (by rw [hD]; linarith) (by positivity)
    _ = _ := hL.symm
    _ ≤ _ := integral_mono hLint hRint hpt

/-- **The fixed point is bounded away from zero when `h ≠ 0`.**  For `4 β² < 1` and
`q = 𝔼 tanh²(β √q z + h)`, `q ≥ (sinh |2h| / (cosh 2h + e^{1/2}))²`; the bound does not depend
on `β`. -/
theorem fixedPoint_lower_bound {β h q : ℝ} (hβ : 4 * β ^ 2 < 1)
    (hfix : ∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 2 ∂(gaussianReal 0 1) = q)
    (hh : h ≠ 0) :
    (Real.sinh (2 * |h|) / (Real.cosh (2 * h) + Real.exp (1 / 2))) ^ 2 ≤ q := by
  have hq := fixedPoint_mem_Icc hfix
  set s : ℝ := β * Real.sqrt q with hs
  have hs2 : s ^ 2 ≤ 1 / 4 := by
    have : s ^ 2 = β ^ 2 * q := by rw [hs, mul_pow, Real.sq_sqrt hq.1]
    rw [this]
    nlinarith [sq_nonneg β, hq.2]
  have hJ : (∫ z : ℝ, Real.tanh (s * z + h) ∂(gaussianReal 0 1)) ^ 2 ≤ q := by
    rw [← hfix]
    exact sq_integral_le_integral_sq (continuous_tanh_affine s h).measurable
      (integrable_tanh_sq_affine s h)
  rcases lt_or_gt_of_ne hh with hneg | hpos
  · -- `h < 0`: reflect `z ↦ -z` and `h ↦ -h`
    have h' : 0 < -h := by linarith
    have hlow := integral_tanh_affine_lower (s := -s) h' (by simpa using hs2)
    have hflip : ∫ z : ℝ, Real.tanh (s * z + h) ∂(gaussianReal 0 1) =
        -∫ z : ℝ, Real.tanh (-s * z + -h) ∂(gaussianReal 0 1) := by
      rw [← integral_neg]
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      simp only []
      rw [← Real.tanh_neg]; ring_nf
    rw [abs_of_neg hneg]
    rw [show Real.cosh (2 * -h) = Real.cosh (2 * h) by rw [mul_neg, Real.cosh_neg]] at hlow
    have hnn : 0 ≤ Real.sinh (2 * -h) / (Real.cosh (2 * h) + Real.exp (1 / 2)) := by
      have := Real.cosh_pos (2 * h)
      exact div_nonneg (Real.sinh_pos_iff.mpr (by linarith)).le (by positivity)
    calc _ ≤ (-∫ z : ℝ, Real.tanh (-s * z + -h) ∂(gaussianReal 0 1)) ^ 2 := by
          rw [neg_sq]; exact pow_le_pow_left₀ hnn hlow 2
      _ = _ := by rw [← hflip]
      _ ≤ q := hJ
  · have hlow := integral_tanh_affine_lower hpos hs2
    rw [abs_of_pos hpos]
    have hnn : 0 ≤ Real.sinh (2 * h) / (Real.cosh (2 * h) + Real.exp (1 / 2)) := by
      have := Real.cosh_pos (2 * h)
      exact div_nonneg (Real.sinh_pos_iff.mpr (by linarith)).le (by positivity)
    exact (pow_le_pow_left₀ hnn hlow 2).trans hJ

end SpinGlasses
