/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Analysis.Convex.Strong
public import Mathlib.MeasureTheory.Measure.Tilted
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import LeanMachineLearning.ForMathlib.Analysis.Convex.PrekopaLeindler
public import LeanMachineLearning.ForMathlib.MeasureTheory.Integral.ExpMoment
public import LeanMachineLearning.ForMathlib.Probability.Median
public import LeanMachineLearning.ForMathlib.Probability.Moments.SubGaussianSymmetrization

/-!
# Concentration for uniformly log-concave measures (Maurey)

Let `E` be a finite-dimensional real normed space with an additive Haar measure `μ₀`, let `C` be a
convex measurable set and `H` a potential which is uniformly midpoint convex on `C`:
`κ ‖(x - y) / 2‖² ≤ (H x + H y) / 2 - H ((x + y) / 2)` for `x, y ∈ C`. The probability measure
`μ = (μ₀.restrict C).tilted (-H)`, with density proportional to `exp (-H)` on `C`, then satisfies
dimension-free concentration inequalities (Talagrand, *Spin Glasses*, Vol. I, Theorem 3.1.4 and
Eq. (3.21)). The proof applies the Prékopa--Leindler inequality.

## Main declarations

* `MeasureTheory.lintegral_exp_infDist_sq_mul_le`: the unnormalized distance inequality.
* `MeasureTheory.integral_exp_infDist_sq_le_inv`: `∫ exp (κ d(x, B)² / 2) dμ ≤ 1 / μ B`.
* `MeasureTheory.integral_exp_sq_sub_median_le_four`: Eq. (3.19), around a median.
* `MeasureTheory.integral_exp_sq_sub_integral_le_four`: Eq. (3.16),
  `∫ exp (κ (f - ∫ f)² / (8 A²)) dμ ≤ 4` for `A`-Lipschitz `f`.
* `MeasureTheory.integral_sub_integral_pow_le_of_lipschitz`: Eq. (3.17),
  `∫ (f - ∫ f) ^ (2 k) dμ ≤ 4 (8 k A² / κ) ^ k`.
* `StrongConvexOn.midpoint_gap_le`: strong convexity implies the midpoint hypothesis.
-/

@[expose] public section

open Set Metric
open scoped ENNReal

/-- A `2 κ`-strongly convex function satisfies the uniform midpoint convexity inequality used for
log-concave concentration (Talagrand, Eq. (3.4)). -/
theorem StrongConvexOn.midpoint_gap_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {C : Set E} {H : E → ℝ} {κ : ℝ} (hH : StrongConvexOn C (2 * κ) H) {x y : E} (hx : x ∈ C)
    (hy : y ∈ C) :
    κ * ‖(1 / 2 : ℝ) • (x - y)‖ ^ 2 ≤ (H x + H y) / 2 - H ((1 / 2 : ℝ) • (x + y)) := by
  have h := hH.2 hx hy (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num)
  simp only [smul_eq_mul] at h
  rw [← smul_add] at h
  rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  nlinarith

namespace MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ₀ : Measure E} [μ₀.IsAddHaarMeasure] {C : Set E}
  {H : E → ℝ} {κ : ℝ}

/-- **Maurey's inequality, unnormalized form.** For `B ⊆ C`,
`(∫_C exp (κ d(x, B)² / 2 - H)) (∫_B exp (-H)) ≤ (∫_C exp (-H))²`. -/
theorem lintegral_exp_infDist_sq_mul_le (hC : Convex ℝ C) (hCm : MeasurableSet C)
    (hH : Measurable H) (hκ : 0 ≤ κ)
    (hconv : ∀ x ∈ C, ∀ y ∈ C,
      κ * ‖(1 / 2 : ℝ) • (x - y)‖ ^ 2 ≤ (H x + H y) / 2 - H ((1 / 2 : ℝ) • (x + y)))
    {B : Set E} (hBm : MeasurableSet B) (hBC : B ⊆ C) :
    (∫⁻ x in C, ENNReal.ofReal (Real.exp (κ / 2 * infDist x B ^ 2 - H x)) ∂μ₀) *
        (∫⁻ x in B, ENNReal.ofReal (Real.exp (-H x)) ∂μ₀) ≤
      (∫⁻ x in C, ENNReal.ofReal (Real.exp (-H x)) ∂μ₀) ^ 2 := by
  set W : E → ℝ≥0∞ := fun x => ENNReal.ofReal (Real.exp (-H x)) with hW
  set V : E → ℝ≥0∞ := fun x => ENNReal.ofReal (Real.exp (κ / 2 * infDist x B ^ 2 - H x)) with hV
  have hWm : Measurable W := (Real.measurable_exp.comp hH.neg).ennreal_ofReal
  have hVm : Measurable V := (Real.measurable_exp.comp
    ((((continuous_infDist_pt B).measurable.pow_const 2).const_mul _).sub hH)).ennreal_ofReal
  have hhalf : (1 - 1 / 2 : ℝ) = 1 / 2 := by norm_num
  have key := lintegral_prekopa_leindler_addHaar μ₀ (s := 1 / 2) (by norm_num) (by norm_num)
    (U := B.indicator W) (V := C.indicator V) (W := C.indicator W)
    (hWm.indicator hBm).aemeasurable (hVm.indicator hCm).aemeasurable
    (hWm.indicator hCm).aemeasurable fun x y => by
      rw [hhalf]
      by_cases hx : x ∈ B
      swap
      · simp [hx]
      by_cases hy : y ∈ C
      swap
      · simp [hy]
      have hmid : (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y ∈ C :=
        hC (hBC hx) hy (by norm_num) (by norm_num) (by norm_num)
      rw [indicator_of_mem hx, indicator_of_mem hy, indicator_of_mem hmid, hW, hV]
      simp only
      rw [ENNReal.ofReal_rpow_of_pos (Real.exp_pos _),
        ENNReal.ofReal_rpow_of_pos (Real.exp_pos _),
        ← ENNReal.ofReal_mul (Real.rpow_nonneg (Real.exp_pos _).le _), ← Real.exp_mul,
        ← Real.exp_mul, ← Real.exp_add]
      refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
      have h1 := hconv x (hBC hx) y hy
      rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2), smul_add] at h1
      have h2 : infDist y B ≤ ‖x - y‖ := by
        rw [← dist_eq_norm, dist_comm]
        exact infDist_le_dist_of_mem hx
      have h3 : infDist y B ^ 2 ≤ ‖x - y‖ ^ 2 := pow_le_pow_left₀ infDist_nonneg h2 2
      nlinarith [mul_le_mul_of_nonneg_left h3 hκ]
  rw [hhalf, lintegral_indicator hBm, lintegral_indicator hCm, lintegral_indicator hCm] at key
  have h2 := ENNReal.rpow_le_rpow key (by norm_num : (0 : ℝ) ≤ 2)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
    show (1 / 2 : ℝ) * 2 = 1 by norm_num, ENNReal.rpow_one, ENNReal.rpow_one,
    ENNReal.rpow_two] at h2
  rwa [mul_comm]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E]
  [μ₀.IsAddHaarMeasure] in
/-- The measure with density proportional to `exp (-H)` on `C` is concentrated on `C`. -/
theorem ae_mem_of_tilted_restrict (hCm : MeasurableSet C) :
    ∀ᵐ x ∂(μ₀.restrict C).tilted (fun x => -H x), x ∈ C :=
  (tilted_absolutelyContinuous _ _).ae_le (ae_restrict_mem hCm)

section Probability

variable (hC : Convex ℝ C) (hCm : MeasurableSet C) (hC0 : μ₀ C ≠ 0) (hH : Measurable H)
  (hint : IntegrableOn (fun x => Real.exp (-H x)) C μ₀)
  (hconv : ∀ x ∈ C, ∀ y ∈ C,
    κ * ‖(1 / 2 : ℝ) • (x - y)‖ ^ 2 ≤ (H x + H y) / 2 - H ((1 / 2 : ℝ) • (x + y)))

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E]
  [μ₀.IsAddHaarMeasure] in
include hC0 hint in
/-- The measure with density proportional to `exp (-H)` on `C` is a probability measure. -/
theorem isProbabilityMeasure_tilted_restrict :
    IsProbabilityMeasure ((μ₀.restrict C).tilted fun x => -H x) := by
  have : NeZero (μ₀.restrict C) := ⟨mt Measure.restrict_eq_zero.1 hC0⟩
  exact isProbabilityMeasure_tilted hint

include hC hCm hC0 hH hint hconv

/-- **Maurey's distance-to-set inequality** (Talagrand, Theorem 3.1.4, Eq. (3.14)):
`∫ exp (κ d(x, B)² / 2) dμ ≤ 1 / μ B` for the probability measure `μ` with density proportional to
`exp (-H)` on `C` and `B ⊆ C` of positive measure. -/
theorem integral_exp_infDist_sq_le_inv (hκ : 0 ≤ κ) {B : Set E} (hBm : MeasurableSet B)
    (hBC : B ⊆ C) (hB : 0 < ((μ₀.restrict C).tilted fun x => -H x).real B) :
    Integrable (fun x => Real.exp (κ / 2 * infDist x B ^ 2))
        ((μ₀.restrict C).tilted fun x => -H x) ∧
      ∫ x, Real.exp (κ / 2 * infDist x B ^ 2) ∂((μ₀.restrict C).tilted fun x => -H x) ≤
        (((μ₀.restrict C).tilted fun x => -H x).real B)⁻¹ := by
  have : NeZero (μ₀.restrict C) := ⟨mt Measure.restrict_eq_zero.1 hC0⟩
  have := isProbabilityMeasure_tilted_restrict hC0 hint
  set G := (μ₀.restrict C).tilted fun x => -H x with hG
  set Z : ℝ := ∫ x, Real.exp (-H x) ∂μ₀.restrict C with hZ
  have hZ0 : 0 < Z := integral_exp_pos hint
  set z : ℝ≥0∞ := ENNReal.ofReal Z⁻¹ with hz
  have hWm : Measurable fun x => ENNReal.ofReal (Real.exp (-H x)) :=
    (Real.measurable_exp.comp hH.neg).ennreal_ofReal
  have hF : Measurable fun x => Real.exp (κ / 2 * infDist x B ^ 2) :=
    Real.measurable_exp.comp (((continuous_infDist_pt B).measurable.pow_const 2).const_mul _)
  have hdens : ∀ x, ENNReal.ofReal (Real.exp (-H x) / Z) =
      z * ENNReal.ofReal (Real.exp (-H x)) := fun x => by
    rw [hz, ← ENNReal.ofReal_mul (inv_nonneg.2 hZ0.le), div_eq_inv_mul]
  have hI : ∫⁻ x, ENNReal.ofReal (Real.exp (κ / 2 * infDist x B ^ 2)) ∂G =
      z * ∫⁻ x in C, ENNReal.ofReal (Real.exp (κ / 2 * infDist x B ^ 2 - H x)) ∂μ₀ := by
    rw [hG, lintegral_tilted, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr fun x => ?_
    rw [← hZ, hdens, mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add,
      neg_add_eq_sub]
  have hGB : G B = z * ∫⁻ x in B, ENNReal.ofReal (Real.exp (-H x)) ∂μ₀ := by
    rw [hG, tilted_apply' _ _ hBm, Measure.restrict_restrict hBm, inter_eq_left.2 hBC, ← hZ,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact lintegral_congr fun x => hdens x
  have hZl : ∫⁻ x in C, ENNReal.ofReal (Real.exp (-H x)) ∂μ₀ = ENNReal.ofReal Z :=
    (ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun x => (Real.exp_pos _).le)).symm
  have hzZ : z * ENNReal.ofReal Z = 1 := by
    rw [hz, ← ENNReal.ofReal_mul (inv_nonneg.2 hZ0.le), inv_mul_cancel₀ hZ0.ne',
      ENNReal.ofReal_one]
  have hprod : (∫⁻ x, ENNReal.ofReal (Real.exp (κ / 2 * infDist x B ^ 2)) ∂G) * G B ≤ 1 := by
    rw [hI, hGB, mul_mul_mul_comm]
    refine (mul_le_mul_right (lintegral_exp_infDist_sq_mul_le (μ₀ := μ₀) hC hCm hH hκ hconv hBm
      hBC) _).trans_eq ?_
    rw [hZl, ← sq, ← mul_pow, hzZ, one_pow]
  have hGB0 : G B ≠ 0 := fun h => by simp [measureReal_def, h] at hB
  have hle : ∫⁻ x, ENNReal.ofReal (Real.exp (κ / 2 * infDist x B ^ 2)) ∂G ≤ (G B)⁻¹ :=
    ENNReal.le_inv_iff_mul_le.2 hprod
  have hfin : (G B)⁻¹ ≠ ∞ := ENNReal.inv_ne_top.2 hGB0
  have hnn : 0 ≤ᵐ[G] fun x => Real.exp (κ / 2 * infDist x B ^ 2) :=
    ae_of_all _ fun x => (Real.exp_pos _).le
  have hintF : Integrable (fun x => Real.exp (κ / 2 * infDist x B ^ 2)) G :=
    (lintegral_ofReal_ne_top_iff_integrable hF.aestronglyMeasurable hnn).1
      (ne_top_of_le_ne_top hfin hle)
  refine ⟨hintF, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hnn hF.aestronglyMeasurable, measureReal_def,
    ← ENNReal.toReal_inv]
  exact ENNReal.toReal_mono hfin hle

/-- **Concentration around a median** (Talagrand, Eq. (3.19)): if `f` is `A`-Lipschitz on `C`
and `m` is a median of `f`, then `∫ exp (κ (f - m)² / (2 A²)) dμ ≤ 4`. -/
theorem integral_exp_sq_sub_median_le_four (hκ : 0 ≤ κ) {f : E → ℝ} (hf : Measurable f) {A : ℝ}
    (hA : 0 < A) (hlip : ∀ x ∈ C, ∀ y ∈ C, |f x - f y| ≤ A * ‖x - y‖) {m : ℝ}
    (hlo : 1 / 2 ≤ ((μ₀.restrict C).tilted fun x => -H x).real {x | f x ≤ m})
    (hhi : 1 / 2 ≤ ((μ₀.restrict C).tilted fun x => -H x).real {x | m ≤ f x}) :
    Integrable (fun x => Real.exp (κ / (2 * A ^ 2) * (f x - m) ^ 2))
        ((μ₀.restrict C).tilted fun x => -H x) ∧
      ∫ x, Real.exp (κ / (2 * A ^ 2) * (f x - m) ^ 2)
        ∂((μ₀.restrict C).tilted fun x => -H x) ≤ 4 := by
  have := isProbabilityMeasure_tilted_restrict hC0 hint
  set G := (μ₀.restrict C).tilted fun x => -H x with hG
  have haeC : ∀ᵐ x ∂G, x ∈ C := ae_mem_of_tilted_restrict hCm
  have hhalf : ∀ S : Set E, 1 / 2 ≤ G.real S → 1 / 2 ≤ G.real (C ∩ S) := fun S hS => by
    have : G (C ∩ S) = G S := by
      rw [inter_comm]
      exact measure_inter_conull haeC
    rwa [measureReal_def, this]
  set Blo := C ∩ {x | f x ≤ m} with hBlo
  set Bhi := C ∩ {x | m ≤ f x} with hBhi
  have hBlom : MeasurableSet Blo := hCm.inter (measurableSet_le hf measurable_const)
  have hBhim : MeasurableSet Bhi := hCm.inter (measurableSet_le measurable_const hf)
  have hlo' : 1 / 2 ≤ G.real Blo := hhalf _ hlo
  have hhi' : 1 / 2 ≤ G.real Bhi := hhalf _ hhi
  have hdist : ∀ B : Set E, MeasurableSet B → B ⊆ C → 1 / 2 ≤ G.real B →
      Integrable (fun x => Real.exp (κ / 2 * infDist x B ^ 2)) G ∧
        ∫ x, Real.exp (κ / 2 * infDist x B ^ 2) ∂G ≤ 2 := fun B hBm hBC hB => by
    have h := integral_exp_infDist_sq_le_inv hC hCm hC0 hH hint hconv hκ hBm hBC
      (lt_of_lt_of_le (by norm_num) hB)
    refine ⟨h.1, h.2.trans ?_⟩
    rw [← hG]
    exact (inv_anti₀ (by norm_num) hB).trans_eq (by norm_num)
  have hlo2 := hdist Blo hBlom inter_subset_left hlo'
  have hhi2 := hdist Bhi hBhim inter_subset_left hhi'
  have hne : ∀ B : Set E, 1 / 2 ≤ G.real B → B.Nonempty := fun B hB => by
    refine nonempty_iff_ne_empty.2 fun h => ?_
    rw [h, measureReal_empty] at hB
    norm_num at hB
  -- the distance to a median level set dominates the deviation
  have hfar : ∀ (B : Set E), B.Nonempty → ∀ x, (∀ y ∈ B, |f x - m| ≤ A * dist x y) →
      κ / (2 * A ^ 2) * (f x - m) ^ 2 ≤ κ / 2 * infDist x B ^ 2 := fun B hB x h => by
    have h1 : |f x - m| / A ≤ infDist x B :=
      (le_infDist hB).2 fun y hy => (div_le_iff₀' hA).2 (h y hy)
    have h2 : (|f x - m| / A) ^ 2 ≤ infDist x B ^ 2 :=
      pow_le_pow_left₀ (div_nonneg (abs_nonneg _) hA.le) h1 2
    rw [div_pow, sq_abs] at h2
    have h3 := mul_le_mul_of_nonneg_left h2 (by linarith : (0 : ℝ) ≤ κ / 2)
    refine le_trans (le_of_eq ?_) h3
    field_simp
  have hpt : ∀ᵐ x ∂G, Real.exp (κ / (2 * A ^ 2) * (f x - m) ^ 2) ≤
      Real.exp (κ / 2 * infDist x Blo ^ 2) + Real.exp (κ / 2 * infDist x Bhi ^ 2) := by
    filter_upwards [haeC] with x hx
    rcases le_total m (f x) with h | h
    · refine le_add_of_le_of_nonneg (Real.exp_le_exp.2 (hfar Blo (hne _ hlo') x fun y hy => ?_))
        (Real.exp_pos _).le
      have hy2 : f y ≤ m := hy.2
      rw [abs_of_nonneg (sub_nonneg.2 h), dist_eq_norm]
      exact (sub_le_sub_left hy2 _).trans ((le_abs_self _).trans (hlip x hx y hy.1))
    · refine le_add_of_nonneg_of_le (Real.exp_pos _).le
        (Real.exp_le_exp.2 (hfar Bhi (hne _ hhi') x fun y hy => ?_))
      have hy2 : m ≤ f y := hy.2
      rw [abs_of_nonpos (sub_nonpos.2 h), neg_sub, dist_eq_norm]
      refine (sub_le_sub_right hy2 _).trans ((le_abs_self _).trans ?_)
      rw [abs_sub_comm]
      exact hlip x hx y hy.1
  have hsum := hlo2.1.add hhi2.1
  have hi : Integrable (fun x => Real.exp (κ / (2 * A ^ 2) * (f x - m) ^ 2)) G := by
    refine Integrable.mono' hsum (Real.measurable_exp.comp
      (((hf.sub_const m).pow_const 2).const_mul _)).aestronglyMeasurable ?_
    filter_upwards [hpt] with x hx
    rwa [Real.norm_of_nonneg (Real.exp_pos _).le]
  refine ⟨hi, (integral_mono_ae hi hsum hpt).trans ?_⟩
  rw [integral_add' hlo2.1 hhi2.1]
  linarith [hlo2.2, hhi2.2]

/-- **Gaussian concentration of Lipschitz functions under a uniformly log-concave measure**
(Talagrand, Theorem 3.1.4, Eq. (3.16)): `∫ exp (κ (f - ∫ f)² / (8 A²)) dμ ≤ 4`. -/
theorem integral_exp_sq_sub_integral_le_four (hκ : 0 < κ) {f : E → ℝ} (hf : Measurable f)
    {A : ℝ} (hA : 0 < A) (hlip : ∀ x ∈ C, ∀ y ∈ C, |f x - f y| ≤ A * ‖x - y‖) :
    Integrable (fun x => Real.exp (κ / (8 * A ^ 2) *
          (f x - ∫ y, f y ∂((μ₀.restrict C).tilted fun x => -H x)) ^ 2))
        ((μ₀.restrict C).tilted fun x => -H x) ∧
      ∫ x, Real.exp (κ / (8 * A ^ 2) *
          (f x - ∫ y, f y ∂((μ₀.restrict C).tilted fun x => -H x)) ^ 2)
        ∂((μ₀.restrict C).tilted fun x => -H x) ≤ 4 := by
  have := isProbabilityMeasure_tilted_restrict hC0 hint
  obtain ⟨m, hlo, hhi⟩ := ProbabilityTheory.exists_median
    ((μ₀.restrict C).tilted fun x => -H x) hf
  have hmed := integral_exp_sq_sub_median_le_four hC hCm hC0 hH hint hconv hκ.le hf hA hlip
    hlo hhi
  have h := ProbabilityTheory.integral_exp_mul_sq_sub_integral_le hf.aestronglyMeasurable
    (by positivity : 0 < κ / (2 * A ^ 2)) hmed.1
  have e : κ / (2 * A ^ 2) / 4 = κ / (8 * A ^ 2) := by ring
  rw [e] at h
  exact ⟨h.1, h.2.trans hmed.2⟩

/-- **Moments of Lipschitz functions under a uniformly log-concave measure** (Talagrand,
Theorem 3.1.4, Eq. (3.17)): `∫ (f - ∫ f) ^ (2 k) dμ ≤ 4 (8 k A² / κ) ^ k`, a bound which does not
depend on the dimension. Integrability is part of the conclusion. -/
theorem integral_sub_integral_pow_le_of_lipschitz (hκ : 0 < κ) {f : E → ℝ} (hf : Measurable f)
    {A : ℝ} (hA : 0 ≤ A) (hlip : ∀ x ∈ C, ∀ y ∈ C, |f x - f y| ≤ A * ‖x - y‖) (k : ℕ) :
    Integrable (fun x => (f x - ∫ y, f y ∂((μ₀.restrict C).tilted fun x => -H x)) ^ (2 * k))
        ((μ₀.restrict C).tilted fun x => -H x) ∧
      ∫ x, (f x - ∫ y, f y ∂((μ₀.restrict C).tilted fun x => -H x)) ^ (2 * k)
        ∂((μ₀.restrict C).tilted fun x => -H x) ≤ 4 * (8 * k * A ^ 2 / κ) ^ k := by
  have := isProbabilityMeasure_tilted_restrict hC0 hint
  set G := (μ₀.restrict C).tilted fun x => -H x with hG
  rcases hA.eq_or_lt with rfl | hA
  · -- a function with Lipschitz constant `0` is constant on `C`
    obtain ⟨x0, hx0⟩ : C.Nonempty := nonempty_of_measure_ne_zero hC0
    have hconst : ∀ᵐ x ∂G, f x = f x0 := by
      filter_upwards [ae_mem_of_tilted_restrict (μ₀ := μ₀) (H := H) hCm] with x hx
      have := hlip x hx x0 hx0
      rw [zero_mul, abs_nonpos_iff, sub_eq_zero] at this
      exact this
    have hmean : ∫ y, f y ∂G = f x0 := by
      rw [integral_congr_ae hconst, integral_const, probReal_univ, one_smul]
    have hz : (fun x => (f x - ∫ y, f y ∂G) ^ (2 * k)) =ᵐ[G] fun _ => (0 : ℝ) ^ (2 * k) := by
      filter_upwards [hconst] with x hx
      rw [hmean, hx, sub_self]
    refine ⟨(integrable_const _).congr hz.symm, ?_⟩
    rw [integral_congr_ae hz, integral_const, probReal_univ, one_smul]
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · norm_num
    · simp [hk.ne']
  have h := integral_exp_sq_sub_integral_le_four hC hCm hC0 hH hint hconv hκ hf hA hlip
  rw [← hG] at h
  set c : ℝ := κ / (8 * A ^ 2) with hc
  have hc0 : 0 < c := by positivity
  set e : ℝ := ∫ y, f y ∂G with he
  have hpt : ∀ x, (f x - e) ^ (2 * k) ≤ ((k : ℝ) / c) ^ k * Real.exp (c * (f x - e) ^ 2) :=
    fun x => by
      have h1 := Real.pow_le_natCast_pow_mul_exp
        (mul_nonneg hc0.le (sq_nonneg (f x - e))) k
      rw [mul_pow, ← pow_mul] at h1
      rw [div_pow, div_mul_eq_mul_div, le_div_iff₀' (pow_pos hc0 k)]
      exact h1
  have hdom : Integrable (fun x => ((k : ℝ) / c) ^ k * Real.exp (c * (f x - e) ^ 2)) G :=
    h.1.const_mul _
  have hi : Integrable (fun x => (f x - e) ^ (2 * k)) G := by
    refine Integrable.mono' hdom ((hf.sub_const e).pow_const _).aestronglyMeasurable
      (ae_of_all _ fun x => ?_)
    rw [Real.norm_of_nonneg ((even_two_mul k).pow_nonneg _)]
    exact hpt x
  refine ⟨hi, (integral_mono hi hdom hpt).trans ?_⟩
  rw [integral_const_mul]
  refine (mul_le_mul_of_nonneg_left h.2 (by positivity)).trans_eq ?_
  have : (k : ℝ) / c = 8 * k * A ^ 2 / κ := by
    rw [hc]
    field_simp
  rw [this, mul_comm]

/-- A Lipschitz function has finite moments of every even order under a uniformly log-concave
measure; in particular it is square integrable. -/
theorem memLp_two_of_lipschitz (hκ : 0 < κ) {f : E → ℝ} (hf : Measurable f) {A : ℝ}
    (hA : 0 ≤ A) (hlip : ∀ x ∈ C, ∀ y ∈ C, |f x - f y| ≤ A * ‖x - y‖) :
    MemLp f 2 ((μ₀.restrict C).tilted fun x => -H x) := by
  have := isProbabilityMeasure_tilted_restrict hC0 hint
  have h := (integral_sub_integral_pow_le_of_lipschitz hC hCm hC0 hH hint hconv hκ hf hA hlip 1).1
  have h2 : MemLp (fun x => f x - ∫ y, f y ∂((μ₀.restrict C).tilted fun x => -H x)) 2
      ((μ₀.restrict C).tilted fun x => -H x) :=
    (memLp_two_iff_integrable_sq (hf.sub_const _).aestronglyMeasurable).2 (by simpa using h)
  have h3 := h2.add (memLp_const (∫ y, f y ∂((μ₀.restrict C).tilted fun x => -H x)))
  have e : (fun x => f x - ∫ y, f y ∂((μ₀.restrict C).tilted fun x => -H x)) +
      (fun _ => ∫ y, f y ∂((μ₀.restrict C).tilted fun x => -H x)) = f := by
    funext x
    simp
  rwa [e] at h3

end Probability

end MeasureTheory
