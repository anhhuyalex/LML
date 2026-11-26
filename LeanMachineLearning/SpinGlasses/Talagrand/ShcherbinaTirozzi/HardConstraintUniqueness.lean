/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Probability.Distributions.Gaussian.MillsRatio
public import LeanMachineLearning.ForMathlib.Probability.Moments.GaussianAffineDerivative
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The Shcherbina--Tirozzi model: uniqueness of the replica-symmetric solution

For the hard constraint `exp u = 1_{[τ, ∞)}` with `τ ≥ 0`, the replica-symmetric functional
`F (q, ρ)` (Talagrand, *Spin Glasses*, Vol. I, Eq. (3.121)) has at most one critical point with
`0 < q < ρ` (the uniqueness part of Theorem 3.3.1).

In the variables `x = q / (ρ - q)` and `ρ` the functional becomes `G (x, ρ) = F (x ρ / (1 + x), ρ)`
(Eq. (3.149)). The proof shows that `x ↦ G (x, ρ)` has at most one critical point, which is a
strict minimum, and that `ρ ↦ G (x, ρ)` has at most one, which is a strict maximum.

Throughout, `mills v = p v / ℙ (ξ ≥ v)` is the inverse Mills ratio.

## Main declarations

* `SpinGlasses.shcherbinaTirozziHardFunctional`: the functional `F`.
* `SpinGlasses.hasDerivAt_shcherbinaTirozziHardFunctional_ratio` and
  `SpinGlasses.hasDerivAt_shcherbinaTirozziHardFunctional_self`: Lemma 3.3.13.
* `SpinGlasses.strictMonoOn_shcherbinaTirozziHardFunctional_ratio_deriv` and
  `SpinGlasses.strictAntiOn_shcherbinaTirozziHardFunctional_self_deriv`: Proposition 3.3.11.
* `SpinGlasses.shcherbinaTirozziHardFunctional_ratio_lt_of_hasDerivAt_zero` and
  `SpinGlasses.shcherbinaTirozziHardFunctional_self_lt_of_hasDerivAt_zero`: Corollary 3.3.12.
* `SpinGlasses.eq_of_hasDerivAt_shcherbinaTirozziHardFunctional_zero`: Theorem 3.3.1, uniqueness.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

namespace SpinGlasses

local notation "mills " v:arg =>
  gaussianPDFReal 0 1 v / Measure.real (gaussianReal 0 1) (Ici v)

/-- **The replica-symmetric functional of the hard constraint** (Talagrand, Eq. (3.121)):
`α 𝔼 log ℙ_ξ (z √q + ξ √(ρ - q) ≥ τ) + q / (2 (ρ - q)) + log (ρ - q) / 2 - κ ρ
  + h² (ρ - q) / 2`. -/
noncomputable def shcherbinaTirozziHardFunctional (α κ h τ q ρ : ℝ) : ℝ :=
  α * ∫ z, Real.log ((gaussianReal 0 1).real
      (Ici ((τ - Real.sqrt q * z) / Real.sqrt (ρ - q)))) ∂(gaussianReal 0 1) +
    q / (2 * (ρ - q)) + Real.log (ρ - q) / 2 - κ * ρ + h ^ 2 * (ρ - q) / 2

/-- Eq. (3.149): the functional in the variables `x = q / (ρ - q)` and `ρ`. -/
theorem shcherbinaTirozziHardFunctional_ratio_eq (α κ h τ : ℝ) {x ρ : ℝ} (hx : 0 ≤ x)
    (hρ : 0 < ρ) :
    shcherbinaTirozziHardFunctional α κ h τ (x * ρ / (1 + x)) ρ =
      α * ∫ z, Real.log ((gaussianReal 0 1).real
          (Ici (τ * Real.sqrt (1 + x) / Real.sqrt ρ + -Real.sqrt x * z))) ∂(gaussianReal 0 1) +
        x / 2 + (Real.log ρ - Real.log (1 + x)) / 2 - κ * ρ + h ^ 2 * ρ / (2 * (1 + x)) := by
  have h1x : 0 < 1 + x := by linarith
  have hs : ρ - x * ρ / (1 + x) = ρ / (1 + x) := by
    field_simp
    ring
  have hW : ∀ z : ℝ, (τ - Real.sqrt (x * ρ / (1 + x)) * z) / Real.sqrt (ρ / (1 + x)) =
      τ * Real.sqrt (1 + x) / Real.sqrt ρ + -Real.sqrt x * z := fun z => by
    rw [Real.sqrt_div' _ h1x.le, Real.sqrt_div' _ h1x.le, Real.sqrt_mul hx]
    have := (Real.sqrt_pos.2 h1x).ne'
    have := (Real.sqrt_pos.2 hρ).ne'
    field_simp
    ring
  unfold shcherbinaTirozziHardFunctional
  simp only [hs, hW]
  rw [Real.log_div hρ.ne' h1x.ne']
  field_simp

/-- Gaussian integration by parts for the inverse Mills ratio:
`𝔼 [z A (m + σ z)] = σ 𝔼 [A² - W A]` at `W = m + σ z`. -/
private theorem integral_id_mul_mills (m σ : ℝ) :
    ∫ z, z * mills (m + σ * z) ∂(gaussianReal 0 1) =
      σ * ∫ z, (mills (m + σ * z) ^ 2 - (m + σ * z) * mills (m + σ * z))
        ∂(gaussianReal 0 1) := by
  obtain ⟨C, hC0, hC⟩ := exists_gaussianPDFReal_div_measureReal_Ici_le
  have hd := fun v => (hasDerivAt_gaussianPDFReal_div_measureReal_Ici v _ fun _ => rfl).1
  have hAm : Measurable fun v : ℝ => mills v :=
    monotone_gaussianPDFReal_div_measureReal_Ici.measurable
  set B : ℝ := C + |m| + |σ| + 1 with hB
  have hW : ∀ z : ℝ, |m + σ * z| ≤ (|m| + |σ|) * (1 + |z|) := fun z => by
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul]
    nlinarith [mul_nonneg (abs_nonneg m) (abs_nonneg z), abs_nonneg σ]
  have hAb : ∀ z : ℝ, |mills (m + σ * z)| ≤ B * (1 + |z|) := fun z => by
    rw [abs_of_nonneg (gaussianPDFReal_div_measureReal_Ici_nonneg _)]
    refine (hC _).trans ?_
    have h1 := hW z
    have h2 := abs_nonneg z
    rw [hB]
    nlinarith [mul_nonneg hC0 h2]
  have hWm : Measurable fun z : ℝ => m + σ * z := by fun_prop
  have hdiff : ∀ z, HasDerivAt (fun z => mills (m + σ * z))
      (σ * (mills (m + σ * z) ^ 2 - (m + σ * z) * mills (m + σ * z))) z := fun z => by
    have h1 : HasDerivAt (fun z => m + σ * z) σ z := by
      simpa using ((hasDerivAt_id z).const_mul σ).const_add m
    exact ((hd _).comp z h1).congr_deriv (mul_comm _ _)
  have h1 : Integrable (fun z => z * mills (m + σ * z)) (gaussianReal 0 1) := by
    refine integrable_gaussianReal_of_norm_le_pow (measurable_id.mul
      (hAm.comp hWm)).aestronglyMeasurable (C := B) (k := 2) fun z => ?_
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, sq,
      show B * ((1 + |z|) * (1 + |z|)) = (1 + |z|) * (B * (1 + |z|)) by ring]
    exact mul_le_mul (le_add_of_nonneg_left zero_le_one) (hAb z) (abs_nonneg _) (by positivity)
  have h2 : Integrable (fun z => σ * (mills (m + σ * z) ^ 2 -
      (m + σ * z) * mills (m + σ * z))) (gaussianReal 0 1) := by
    refine (integrable_gaussianReal_of_norm_le_pow (((hAm.comp hWm).pow_const 2).sub
      (hWm.mul (hAm.comp hWm))).aestronglyMeasurable (C := B ^ 2 + (|m| + |σ|) * B) (k := 2)
      fun z => ?_).const_mul σ
    simp only [Function.comp_apply, Pi.sub_apply, Pi.mul_apply]
    rw [Real.norm_eq_abs]
    refine (abs_sub _ _).trans ?_
    rw [abs_pow, abs_mul, add_mul]
    refine add_le_add ?_ ?_
    · rw [← mul_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (hAb z) 2
    · rw [show (|m| + |σ|) * B * (1 + |z|) ^ 2 =
        ((|m| + |σ|) * (1 + |z|)) * (B * (1 + |z|)) by ring]
      exact mul_le_mul (hW z) (hAb z) (abs_nonneg _) (by positivity)
  rw [integral_id_mul_gaussianReal_eq 1 hdiff h1 h2, NNReal.coe_one, one_mul, integral_const_mul]

/-- Differentiation of `t ↦ 𝔼 log ℙ (ξ ≥ m t + σ t z)`. -/
private theorem hasDerivAt_integral_log_gaussianTail {m σ m' σ' : ℝ → ℝ} {t : ℝ}
    (hm : ∀ᶠ s in 𝓝 t, HasDerivAt m (m' s) s) (hσ : ∀ᶠ s in 𝓝 t, HasDerivAt σ (σ' s) s)
    (hm' : ContinuousAt m' t) (hσ' : ContinuousAt σ' t) :
    HasDerivAt (fun s => ∫ z, Real.log ((gaussianReal 0 1).real (Ici (m s + σ s * z)))
        ∂(gaussianReal 0 1))
      (∫ z, -(mills (m t + σ t * z)) * (m' t + σ' t * z) ∂(gaussianReal 0 1)) t := by
  obtain ⟨C, hC0, hC⟩ := exists_gaussianPDFReal_div_measureReal_Ici_le
  obtain ⟨C', hC'0, hC'⟩ := exists_abs_log_measureReal_gaussianReal_Ici_le
  refine hasDerivAt_integral_comp_add_mul_gaussianReal
    (f := fun v => Real.log ((gaussianReal 0 1).real (Ici v))) (C := C' + C + 1) (k := 2)
    hasDerivAt_log_measureReal_gaussianReal_Ici
    monotone_gaussianPDFReal_div_measureReal_Ici.measurable.neg (fun y => ?_) (fun y => ?_)
    hm hσ hm' hσ'
  · exact (hC' y).trans (mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _))
  · rw [abs_neg, abs_of_nonneg (gaussianPDFReal_div_measureReal_Ici_nonneg _)]
    refine (hC y).trans ?_
    have h1 := abs_nonneg y
    nlinarith [mul_nonneg hC0 h1, mul_nonneg hC'0 h1, mul_nonneg hC0 (sq_nonneg |y|),
      mul_nonneg hC'0 (sq_nonneg |y|), sq_nonneg |y|]

/-- Linear growth of `A (W)` and integrability facts used below. -/
private theorem integrable_mills_comp (m σ : ℝ) :
    Integrable (fun z => mills (m + σ * z)) (gaussianReal 0 1) ∧
      Integrable (fun z => z * mills (m + σ * z)) (gaussianReal 0 1) ∧
      Integrable (fun z => mills (m + σ * z) ^ 2) (gaussianReal 0 1) := by
  obtain ⟨C, hC0, hC⟩ := exists_gaussianPDFReal_div_measureReal_Ici_le
  have hAm : Measurable fun v : ℝ => mills v :=
    monotone_gaussianPDFReal_div_measureReal_Ici.measurable
  have hWm : Measurable fun z : ℝ => m + σ * z := by fun_prop
  set B : ℝ := C + |m| + |σ| + 1 with hB
  have hAb : ∀ z : ℝ, ‖mills (m + σ * z)‖ ≤ B * (1 + |z|) := fun z => by
    rw [Real.norm_of_nonneg (gaussianPDFReal_div_measureReal_Ici_nonneg _)]
    refine (hC _).trans ?_
    have h1 : |m + σ * z| ≤ |m| + |σ| * |z| := (abs_add_le _ _).trans_eq (by rw [abs_mul])
    have h2 := abs_nonneg z
    rw [hB]
    nlinarith [mul_nonneg hC0 h2, mul_nonneg (abs_nonneg m) h2, abs_nonneg σ]
  refine ⟨?_, ?_, ?_⟩
  · refine integrable_gaussianReal_of_norm_le_pow (hAm.comp hWm).aestronglyMeasurable
      (C := B) (k := 1) fun z => ?_
    rw [pow_one]; exact hAb z
  · refine integrable_gaussianReal_of_norm_le_pow
      (measurable_id.mul (hAm.comp hWm)).aestronglyMeasurable (C := B) (k := 2) fun z => ?_
    rw [norm_mul, Real.norm_eq_abs, sq,
      show B * ((1 + |z|) * (1 + |z|)) = (1 + |z|) * (B * (1 + |z|)) by ring]
    exact mul_le_mul (le_add_of_nonneg_left zero_le_one) (hAb z) (norm_nonneg _) (by positivity)
  · refine integrable_gaussianReal_of_norm_le_pow
      ((hAm.comp hWm).pow_const 2).aestronglyMeasurable (C := B ^ 2) (k := 2) fun z => ?_
    rw [norm_pow, ← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hAb z) 2

/-- **Lemma 3.3.13, Eq. (3.151):** the derivative in `ρ` of
`G (x, ρ) = F (x ρ / (1 + x), ρ)`. -/
theorem hasDerivAt_shcherbinaTirozziHardFunctional_self (α κ h τ : ℝ) {x ρ : ℝ} (hx : 0 ≤ x)
    (hρ : 0 < ρ) :
    HasDerivAt (fun r => shcherbinaTirozziHardFunctional α κ h τ (x * r / (1 + x)) r)
      ((α * τ * Real.sqrt (1 + x) / (ρ * Real.sqrt ρ) *
          (∫ z, mills (τ * Real.sqrt (1 + x) / Real.sqrt ρ + -Real.sqrt x * z)
            ∂(gaussianReal 0 1)) + ρ⁻¹ - 2 * κ + h ^ 2 / (1 + x)) / 2) ρ := by
  have h1x : 0 < 1 + x := by linarith
  set a : ℝ := τ * Real.sqrt (1 + x) with ha
  set m : ℝ → ℝ := fun r => a / Real.sqrt r with hm
  set m' : ℝ → ℝ := fun r => -(a / (2 * r * Real.sqrt r)) with hm'
  have hmd : ∀ r, 0 < r → HasDerivAt m (m' r) r := fun r hr => by
    have hsr := (Real.sqrt_pos.2 hr).ne'
    have h := (hasDerivAt_const r a).div (Real.hasDerivAt_sqrt hr.ne') hsr
    refine h.congr_deriv ?_
    rw [hm', Real.sq_sqrt hr.le]
    field_simp
    ring
  have hmc : ContinuousAt m' ρ := by
    have hsr := (Real.sqrt_pos.2 hρ).ne'
    refine (continuousAt_const.div (by fun_prop) ?_).neg
    exact mul_ne_zero (mul_ne_zero two_ne_zero hρ.ne') hsr
  have hE := hasDerivAt_integral_log_gaussianTail (m := m) (σ := fun _ => -Real.sqrt x)
    (m' := m') (σ' := fun _ => 0) (t := ρ)
    ((eventually_gt_nhds hρ).mono fun r hr => hmd r hr)
    (Eventually.of_forall fun r => hasDerivAt_const r _) hmc continuousAt_const
  have hrest : HasDerivAt (fun r => x / 2 + (Real.log r - Real.log (1 + x)) / 2 - κ * r +
      h ^ 2 * r / (2 * (1 + x))) (ρ⁻¹ / 2 - κ + h ^ 2 / (2 * (1 + x))) ρ := by
    have h1 := ((((Real.hasDerivAt_log hρ.ne').sub_const (Real.log (1 + x))).div_const 2
      ).const_add (x / 2)).sub ((hasDerivAt_id ρ).const_mul κ)
    have h2 := ((hasDerivAt_id ρ).const_mul (h ^ 2)).div_const (2 * (1 + x))
    refine (h1.add h2).congr_deriv ?_
    ring
  have hsum := (hE.const_mul α).add hrest
  have heq : (fun r => shcherbinaTirozziHardFunctional α κ h τ (x * r / (1 + x)) r) =ᶠ[𝓝 ρ]
      fun r => α * (∫ z, Real.log ((gaussianReal 0 1).real (Ici (m r + -Real.sqrt x * z)))
          ∂(gaussianReal 0 1)) +
        (x / 2 + (Real.log r - Real.log (1 + x)) / 2 - κ * r + h ^ 2 * r / (2 * (1 + x))) := by
    filter_upwards [eventually_gt_nhds hρ] with r hr
    rw [shcherbinaTirozziHardFunctional_ratio_eq α κ h τ hx hr]
    simp only [hm, ha]
    ring
  refine (hsum.congr_of_eventuallyEq heq).congr_deriv ?_
  have hint : ∫ z, -(mills (m ρ + -Real.sqrt x * z)) * (m' ρ + 0 * z) ∂(gaussianReal 0 1) =
      a / (2 * ρ * Real.sqrt ρ) *
        ∫ z, mills (m ρ + -Real.sqrt x * z) ∂(gaussianReal 0 1) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    simp only [hm']
    ring
  rw [hint, show h ^ 2 / (1 + x) = 2 * (h ^ 2 / (2 * (1 + x))) by field_simp]
  simp only [hm, ha]
  ring

/-- **Lemma 3.3.13, Eq. (3.152):** the derivative in `x` of `G (x, ρ) = F (x ρ / (1 + x), ρ)`
satisfies `2 (1 + x) / x · ∂G/∂x = 1 - α 𝔼 A² / x - h² ρ / (x (1 + x))`. -/
theorem hasDerivAt_shcherbinaTirozziHardFunctional_ratio (α κ h τ : ℝ) {x ρ : ℝ} (hx : 0 < x)
    (hρ : 0 < ρ) :
    HasDerivAt (fun y => shcherbinaTirozziHardFunctional α κ h τ (y * ρ / (1 + y)) ρ)
      (x / (2 * (1 + x)) *
        (1 - α * (∫ z, mills (τ * Real.sqrt (1 + x) / Real.sqrt ρ + -Real.sqrt x * z) ^ 2
          ∂(gaussianReal 0 1)) / x - h ^ 2 * ρ / (x * (1 + x)))) x := by
  have h1x : 0 < 1 + x := by linarith
  have hsx := (Real.sqrt_pos.2 hx).ne'
  have hs1 := (Real.sqrt_pos.2 h1x).ne'
  have hsρ := (Real.sqrt_pos.2 hρ).ne'
  set m : ℝ → ℝ := fun y => τ * Real.sqrt (1 + y) / Real.sqrt ρ with hm
  set σ : ℝ → ℝ := fun y => -Real.sqrt y with hσ
  set m' : ℝ → ℝ := fun y => τ / (2 * Real.sqrt (1 + y) * Real.sqrt ρ) with hm'
  set σ' : ℝ → ℝ := fun y => -(1 / (2 * Real.sqrt y)) with hσ'
  have hmd : ∀ y, 0 < y → HasDerivAt m (m' y) y := fun y hy => by
    have h1y : (1 : ℝ) + y ≠ 0 := by linarith
    have h1 : HasDerivAt (fun y => Real.sqrt (1 + y)) (1 / (2 * Real.sqrt (1 + y))) y := by
      simpa using ((hasDerivAt_id y).const_add 1).sqrt h1y
    refine ((h1.const_mul τ).div_const (Real.sqrt ρ)).congr_deriv ?_
    rw [hm']
    ring
  have hσd : ∀ y, 0 < y → HasDerivAt σ (σ' y) y := fun y hy =>
    (Real.hasDerivAt_sqrt hy.ne').neg
  have hmc : ContinuousAt m' x := by
    refine continuousAt_const.div (by fun_prop) ?_
    exact mul_ne_zero (mul_ne_zero two_ne_zero hs1) hsρ
  have hσc : ContinuousAt σ' x := ContinuousAt.neg (ContinuousAt.div continuousAt_const
    (by fun_prop : ContinuousAt (fun y : ℝ => 2 * Real.sqrt y) x)
    (mul_ne_zero two_ne_zero hsx))
  have hE := hasDerivAt_integral_log_gaussianTail (m := m) (σ := σ) (m' := m') (σ' := σ') (t := x)
    ((eventually_gt_nhds hx).mono fun y hy => hmd y hy)
    ((eventually_gt_nhds hx).mono fun y hy => hσd y hy) hmc hσc
  have hrest : HasDerivAt (fun y => y / 2 + (Real.log ρ - Real.log (1 + y)) / 2 - κ * ρ +
      h ^ 2 * ρ / (2 * (1 + y))) (1 / 2 - (1 + x)⁻¹ / 2 - h ^ 2 * ρ / (2 * (1 + x) ^ 2)) x := by
    have h0 : HasDerivAt (fun y : ℝ => 1 + y) 1 x := (hasDerivAt_id x).const_add 1
    have h1 := (((hasDerivAt_id x).div_const 2).add
      (((h0.log h1x.ne').const_sub (Real.log ρ)).div_const 2)).sub_const (κ * ρ)
    have h2 := (hasDerivAt_const x (h ^ 2 * ρ)).div (h0.const_mul 2) (by positivity)
    refine (h1.add h2).congr_deriv ?_
    field_simp
    ring
  have hsum := (hE.const_mul α).add hrest
  have heq : (fun y => shcherbinaTirozziHardFunctional α κ h τ (y * ρ / (1 + y)) ρ) =ᶠ[𝓝 x]
      fun y => α * (∫ z, Real.log ((gaussianReal 0 1).real (Ici (m y + σ y * z)))
          ∂(gaussianReal 0 1)) +
        (y / 2 + (Real.log ρ - Real.log (1 + y)) / 2 - κ * ρ + h ^ 2 * ρ / (2 * (1 + y))) := by
    filter_upwards [eventually_gt_nhds hx] with y hy
    rw [shcherbinaTirozziHardFunctional_ratio_eq α κ h τ hy.le hρ]
    simp only [hm, hσ]
    ring
  refine (hsum.congr_of_eventuallyEq heq).congr_deriv ?_
  -- Gaussian integration by parts
  obtain ⟨hi, hzi, hi2⟩ := integrable_mills_comp (m x) (σ x)
  have hIBP := integral_id_mul_mills (m x) (σ x)
  have hWA : Integrable (fun z => (m x + σ x * z) * mills (m x + σ x * z))
      (gaussianReal 0 1) := by
    refine ((hi.const_mul (m x)).add (hzi.const_mul (σ x))).congr (ae_of_all _ fun z => ?_)
    simp only [Pi.add_apply]
    ring
  have hWAeq : ∫ z, (m x + σ x * z) * mills (m x + σ x * z) ∂(gaussianReal 0 1) =
      m x * (∫ z, mills (m x + σ x * z) ∂(gaussianReal 0 1)) +
        σ x * ∫ z, z * mills (m x + σ x * z) ∂(gaussianReal 0 1) := by
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_add (hi.const_mul _) (hzi.const_mul _)]
    exact integral_congr_ae (ae_of_all _ fun z => by ring)
  rw [integral_sub hi2 hWA, hWAeq] at hIBP
  have hder : ∫ z, -(mills (m x + σ x * z)) * (m' x + σ' x * z) ∂(gaussianReal 0 1) =
      -(m' x) * (∫ z, mills (m x + σ x * z) ∂(gaussianReal 0 1)) +
        -(σ' x) * ∫ z, z * mills (m x + σ x * z) ∂(gaussianReal 0 1) := by
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_add (hi.const_mul _) (hzi.const_mul _)]
    exact integral_congr_ae (ae_of_all _ fun z => by ring)
  rw [hder]
  change _ = x / (2 * (1 + x)) * (1 - α * (∫ z, mills (m x + σ x * z) ^ 2
    ∂(gaussianReal 0 1)) / x - h ^ 2 * ρ / (x * (1 + x)))
  set I1 := ∫ z, mills (m x + σ x * z) ∂(gaussianReal 0 1) with hI1
  set I2 := ∫ z, mills (m x + σ x * z) ^ 2 ∂(gaussianReal 0 1) with hI2
  set J := ∫ z, z * mills (m x + σ x * z) ∂(gaussianReal 0 1) with hJ
  have hsx2 : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx.le
  have hs12 : Real.sqrt (1 + x) ^ 2 = 1 + x := Real.sq_sqrt h1x.le
  -- solve the integration by parts identity for `J`
  have hJeq : J = -Real.sqrt x * (I2 - m x * I1) / (1 + x) := by
    rw [eq_div_iff h1x.ne']
    simp only [hσ] at hIBP ⊢
    linear_combination hIBP - J * hsx2
  have hmx : m x = τ * Real.sqrt (1 + x) / Real.sqrt ρ := rfl
  rw [hJeq, hmx]
  simp only [hm', hσ']
  set a := Real.sqrt (1 + x) with ha
  set b := Real.sqrt x with hb
  set d := Real.sqrt ρ with hd
  rw [← hs12]
  have hxb : x = b ^ 2 := hsx2.symm
  have hx1 : x = a ^ 2 - 1 := by rw [hs12]; ring
  field_simp
  rw [hs12, hxb]
  ring

/-- A function whose derivative is negative before `a` and positive after `a` has a strict minimum
at `a` on `(0, ∞)`. -/
private theorem lt_of_hasDerivAt_neg_of_pos {f f' : ℝ → ℝ} {a x : ℝ} (ha : 0 < a) (hx : 0 < x)
    (hxa : x ≠ a) (hf : ∀ y, 0 < y → HasDerivAt f (f' y) y)
    (hneg : ∀ y, 0 < y → y < a → f' y < 0) (hpos : ∀ y, a < y → 0 < f' y) : f a < f x := by
  rcases lt_or_gt_of_ne hxa with h | h
  · refine strictAntiOn_of_hasDerivWithinAt_neg (f' := f') (convex_Icc x a)
      (fun y hy => (hf y (hx.trans_le hy.1)).continuousAt.continuousWithinAt)
      (fun y hy => ?_) (fun y hy => ?_) (left_mem_Icc.2 h.le) (right_mem_Icc.2 h.le) h
    · rw [interior_Icc] at hy
      exact (hf y (hx.trans hy.1)).hasDerivWithinAt
    · rw [interior_Icc] at hy
      exact hneg y (hx.trans hy.1) hy.2
  · refine strictMonoOn_of_hasDerivWithinAt_pos (f' := f') (convex_Icc a x)
      (fun y hy => (hf y (ha.trans_le hy.1)).continuousAt.continuousWithinAt)
      (fun y hy => ?_) (fun y hy => ?_) (left_mem_Icc.2 h.le) (right_mem_Icc.2 h.le) h
    · rw [interior_Icc] at hy
      exact (hf y (ha.trans hy.1)).hasDerivWithinAt
    · rw [interior_Icc] at hy
      exact hpos y hy.1

/-- **Proposition 3.3.11, second part:** `x ↦ 1 - α 𝔼 A² / x - h² ρ / (x (1 + x))` is strictly
increasing on `(0, ∞)` unless `α = h = 0`. -/
theorem strictMonoOn_shcherbinaTirozziHardFunctional_ratio_deriv {α h τ ρ : ℝ} (hα : 0 ≤ α)
    (hτ : 0 ≤ τ) (hρ : 0 < ρ) (hαh : α ≠ 0 ∨ h ≠ 0) :
    StrictMonoOn (fun x => 1 - α * (∫ z, mills (τ * Real.sqrt (1 + x) / Real.sqrt ρ +
        -Real.sqrt x * z) ^ 2 ∂(gaussianReal 0 1)) / x - h ^ 2 * ρ / (x * (1 + x))) (Ioi 0) := by
  obtain ⟨C, hC0, hC⟩ := exists_gaussianPDFReal_div_measureReal_Ici_le
  have hd := fun v => (hasDerivAt_gaussianPDFReal_div_measureReal_Ici v _ fun _ => rfl)
  have hAm : Measurable fun v : ℝ => mills v :=
    monotone_gaussianPDFReal_div_measureReal_Ici.measurable
  have hA0 : ∀ v, 0 ≤ mills v := gaussianPDFReal_div_measureReal_Ici_nonneg
  set A' : ℝ → ℝ := fun v => mills v ^ 2 - v * mills v with hA'
  have hA'm : Measurable A' := (hAm.pow_const 2).sub (measurable_id.mul hAm)
  have hf : ∀ v, HasDerivAt (fun v => mills v ^ 2) (2 * mills v * A' v) v := fun v => by
    refine ((hd v).1.pow 2).congr_deriv ?_
    simp only [hA']
    push_cast
    ring
  have hAC : ∀ v, mills v ≤ (C + 1) * (1 + |v|) := fun v => by
    refine (hC v).trans ?_
    nlinarith [mul_nonneg hC0 (abs_nonneg v), abs_nonneg v]
  set K : ℝ := 2 * (C + 1) ^ 2 * (C + 2) + (C + 1) ^ 2 with hK
  have hg1 : ∀ v, |mills v ^ 2| ≤ K * (1 + |v|) ^ 3 := fun v => by
    rw [abs_of_nonneg (sq_nonneg _)]
    have h1 := pow_le_pow_left₀ (hA0 v) (hAC v) 2
    rw [mul_pow] at h1
    have h2 : (1 + |v|) ^ 2 ≤ (1 + |v|) ^ 3 :=
      pow_le_pow_right₀ (le_add_of_nonneg_right (abs_nonneg _)) (by norm_num)
    refine h1.trans (mul_le_mul ?_ h2 (by positivity) (by positivity))
    rw [hK]
    exact le_add_of_nonneg_left (by positivity)
  have hg2 : ∀ v, |2 * mills v * A' v| ≤ K * (1 + |v|) ^ 3 := fun v => by
    have h1 : |A' v| ≤ mills v * ((C + 2) * (1 + |v|)) := by
      have e : A' v = mills v * (mills v - v) := by simp only [hA']; ring
      rw [e, abs_mul, abs_of_nonneg (hA0 v)]
      refine mul_le_mul_of_nonneg_left ((abs_sub _ _).trans ?_) (hA0 v)
      rw [abs_of_nonneg (hA0 v)]
      have := hC v
      nlinarith [mul_nonneg hC0 (abs_nonneg v), abs_nonneg v]
    rw [abs_mul, abs_of_nonneg (mul_nonneg two_pos.le (hA0 v))]
    refine (mul_le_mul_of_nonneg_left h1 (mul_nonneg two_pos.le (hA0 v))).trans ?_
    have h2 := pow_le_pow_left₀ (hA0 v) (hAC v) 2
    calc 2 * mills v * (mills v * ((C + 2) * (1 + |v|)))
        = 2 * (C + 2) * (1 + |v|) * mills v ^ 2 := by ring
      _ ≤ 2 * (C + 2) * (1 + |v|) * ((C + 1) * (1 + |v|)) ^ 2 :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = 2 * (C + 1) ^ 2 * (C + 2) * (1 + |v|) ^ 3 := by ring
      _ ≤ K * (1 + |v|) ^ 3 := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          rw [hK]
          exact le_add_of_nonneg_right (sq_nonneg _)
  -- derivative at every `x > 0`
  have key : ∀ x ∈ Ioi (0 : ℝ), ∃ D, 0 < D ∧ HasDerivAt (fun x => 1 - α *
      (∫ z, mills (τ * Real.sqrt (1 + x) / Real.sqrt ρ + -Real.sqrt x * z) ^ 2
        ∂(gaussianReal 0 1)) / x - h ^ 2 * ρ / (x * (1 + x))) D x := by
    intro x (hx : 0 < x)
    have h1x : 0 < 1 + x := by linarith
    have hsx := (Real.sqrt_pos.2 hx).ne'
    have hs1 := (Real.sqrt_pos.2 h1x).ne'
    have hsρ := (Real.sqrt_pos.2 hρ).ne'
    set m : ℝ → ℝ := fun y => τ * Real.sqrt (1 + y) / Real.sqrt ρ with hm
    set σ : ℝ → ℝ := fun y => -Real.sqrt y with hσ
    set m' : ℝ → ℝ := fun y => τ / (2 * Real.sqrt (1 + y) * Real.sqrt ρ) with hm'
    set σ' : ℝ → ℝ := fun y => -(1 / (2 * Real.sqrt y)) with hσ'
    have hmd : ∀ y, 0 < y → HasDerivAt m (m' y) y := fun y hy => by
      have h1y : (1 : ℝ) + y ≠ 0 := by linarith
      have h1 : HasDerivAt (fun y => Real.sqrt (1 + y)) (1 / (2 * Real.sqrt (1 + y))) y := by
        simpa using ((hasDerivAt_id y).const_add 1).sqrt h1y
      refine ((h1.const_mul τ).div_const (Real.sqrt ρ)).congr_deriv ?_
      rw [hm']
      ring
    have hσd : ∀ y, 0 < y → HasDerivAt σ (σ' y) y := fun y hy =>
      (Real.hasDerivAt_sqrt hy.ne').neg
    have hmc : ContinuousAt m' x := by
      refine continuousAt_const.div (by fun_prop) ?_
      exact mul_ne_zero (mul_ne_zero two_ne_zero hs1) hsρ
    have hσc : ContinuousAt σ' x := ContinuousAt.neg (ContinuousAt.div continuousAt_const
      (by fun_prop : ContinuousAt (fun y : ℝ => 2 * Real.sqrt y) x)
      (mul_ne_zero two_ne_zero hsx))
    have hM := hasDerivAt_integral_comp_add_mul_gaussianReal (f := fun v => mills v ^ 2)
      (f' := fun v => 2 * mills v * A' v) (C := K) (k := 3) (m := m) (σ := σ) (m' := m')
      (σ' := σ') (t := x) hf ((measurable_const.mul hAm).mul hA'm) hg1 hg2
      ((eventually_gt_nhds hx).mono fun y hy => hmd y hy)
      ((eventually_gt_nhds hx).mono fun y hy => hσd y hy) hmc hσc
    set M' := ∫ z, 2 * mills (m x + σ x * z) * A' (m x + σ x * z) * (m' x + σ' x * z)
      ∂(gaussianReal 0 1) with hM'
    set M := ∫ z, mills (m x + σ x * z) ^ 2 ∂(gaussianReal 0 1) with hMdef
    have h0 : HasDerivAt (fun y : ℝ => 1 + y) 1 x := (hasDerivAt_id x).const_add 1
    have hfull := (((hM.const_mul α).div (hasDerivAt_id x) hx.ne').const_sub 1).sub
      ((hasDerivAt_const x (h ^ 2 * ρ)).div ((hasDerivAt_id x).mul h0)
        (mul_ne_zero hx.ne' h1x.ne'))
    refine ⟨_, ?_, hfull⟩
    simp only [id_eq, Pi.mul_apply, zero_mul, zero_sub, mul_one, one_mul]
    -- the key positivity: `x M' < M`
    set e : ℝ := τ / (Real.sqrt (1 + x) * Real.sqrt ρ) with he
    have he0 : 0 ≤ e := div_nonneg hτ (by positivity)
    set G : ℝ → ℝ := fun z => mills (m x + σ x * z) ^ 2 -
      x * (2 * mills (m x + σ x * z) * A' (m x + σ x * z) * (m' x + σ' x * z)) with hG
    have hlin : ∀ z, x * (2 * (m' x + σ' x * z)) = (m x + σ x * z) - e := fun z => by
      have h1 : Real.sqrt (1 + x) ^ 2 = 1 + x := Real.sq_sqrt h1x.le
      have h2 : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx.le
      simp only [hm, hσ, hm', hσ', he]
      set a := Real.sqrt (1 + x)
      set b := Real.sqrt x
      field_simp
      linear_combination (-τ * b) * h1 + (z * Real.sqrt ρ * a) * h2
    have hGpos : ∀ z, 0 < G z := fun z => by
      set v := m x + σ x * z with hv
      have hpos : 0 < mills v := div_pos (gaussianPDFReal_pos _ _ _ one_ne_zero)
        (measureReal_gaussianReal_Ici_pos v)
      have hG' : G z = mills v ^ 2 * (1 - v * mills v + v ^ 2) + e * (mills v * A' v) := by
        have h1 : x * (2 * mills v * A' v * (m' x + σ' x * z)) =
            mills v * A' v * (v - e) := by
          rw [← hlin z]; ring
        have h0 : G z = mills v ^ 2 - x * (2 * mills v * A' v * (m' x + σ' x * z)) := rfl
        rw [h0, h1]
        simp only [hA']
        ring
      have hstrict : v * mills v < 1 + v ^ 2 := by
        rw [← mul_div_assoc, div_lt_iff₀ (measureReal_gaussianReal_Ici_pos v)]
        exact mul_gaussianPDFReal_lt_one_add_sq_mul v
      rw [hG']
      exact add_pos_of_pos_of_nonneg (mul_pos (pow_pos hpos 2) (by linarith))
        (mul_nonneg he0 (mul_nonneg hpos.le (hd v).2))
    have hMi : Integrable (fun z => mills (m x + σ x * z) ^ 2) (gaussianReal 0 1) :=
      (integrable_mills_comp (m x) (σ x)).2.2
    have hM'i : Integrable (fun z => 2 * mills (m x + σ x * z) * A' (m x + σ x * z) *
        (m' x + σ' x * z)) (gaussianReal 0 1) := by
      have hWm : Measurable fun z : ℝ => m x + σ x * z := by fun_prop
      set B : ℝ := 1 + |m x| + |σ x| with hB
      refine integrable_gaussianReal_of_norm_le_pow ((((measurable_const.mul (hAm.comp hWm)).mul
        (hA'm.comp hWm)).mul (by fun_prop : Measurable fun z : ℝ => m' x + σ' x * z))
        ).aestronglyMeasurable (C := K * B ^ 3 * (|m' x| + |σ' x|)) (k := 4) fun z => ?_
      have h1 : 1 + |m x + σ x * z| ≤ B * (1 + |z|) := by
        have : |m x + σ x * z| ≤ |m x| + |σ x| * |z| :=
          (abs_add_le _ _).trans_eq (by rw [abs_mul])
        rw [hB]
        nlinarith [mul_nonneg (abs_nonneg (m x)) (abs_nonneg z), abs_nonneg (σ x),
          abs_nonneg z]
      have h2 : |m' x + σ' x * z| ≤ (|m' x| + |σ' x|) * (1 + |z|) := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul]
        nlinarith [mul_nonneg (abs_nonneg (m' x)) (abs_nonneg z), abs_nonneg (σ' x)]
      rw [Real.norm_eq_abs, abs_mul]
      have h3 := (hg2 (m x + σ x * z)).trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) h1 3) (by positivity))
      refine (mul_le_mul h3 h2 (abs_nonneg _) (by positivity)).trans_eq ?_
      ring
    have hGi : Integrable G (gaussianReal 0 1) := hMi.sub (hM'i.const_mul x)
    have hGint : ∫ z, G z ∂(gaussianReal 0 1) = M - x * M' := by
      rw [hMdef, hM', ← integral_const_mul]
      exact integral_sub hMi (hM'i.const_mul x)
    have hGI : 0 < ∫ z, G z ∂(gaussianReal 0 1) := by
      rw [integral_pos_iff_support_of_nonneg (fun z => (hGpos z).le) hGi,
        show Function.support G = univ from eq_univ_of_forall fun z => (hGpos z).ne',
        measure_univ]
      exact one_pos
    have hkey : 0 < M - x * M' := hGint ▸ hGI
    have e1 : -((α * M' * x - α * M) / x ^ 2) -
        -(h ^ 2 * ρ * (1 + x + x)) / (x * (1 + x)) ^ 2 =
        α * (M - x * M') / x ^ 2 + h ^ 2 * ρ * (1 + 2 * x) / (x * (1 + x)) ^ 2 := by ring
    rw [e1]
    have t1 : 0 ≤ α * (M - x * M') / x ^ 2 :=
      div_nonneg (mul_nonneg hα hkey.le) (sq_nonneg _)
    have t2 : 0 ≤ h ^ 2 * ρ * (1 + 2 * x) / (x * (1 + x)) ^ 2 :=
      div_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) hρ.le) (by linarith)) (sq_nonneg _)
    rcases hαh with hα' | hh
    · exact add_pos_of_pos_of_nonneg (div_pos (mul_pos (hα.lt_of_ne' hα') hkey) (by positivity))
        t2
    · have hh2 : 0 < h ^ 2 := by positivity
      exact add_pos_of_nonneg_of_pos t1 (div_pos (mul_pos (mul_pos hh2 hρ) (by linarith))
        (by positivity))
  refine strictMonoOn_of_deriv_pos (convex_Ioi 0) (fun x hx => ?_) fun x hx => ?_
  · obtain ⟨D, -, hD⟩ := key x hx
    exact hD.continuousAt.continuousWithinAt
  · rw [interior_Ioi] at hx
    obtain ⟨D, hD0, hD⟩ := key x hx
    rwa [hD.deriv]

/-- **Proposition 3.3.11, first part:** `ρ ↦ 2 ∂G/∂ρ` is strictly decreasing on `(0, ∞)`. -/
theorem strictAntiOn_shcherbinaTirozziHardFunctional_self_deriv {α τ x : ℝ} (κ h : ℝ)
    (hα : 0 ≤ α) (hτ : 0 ≤ τ) :
    StrictAntiOn (fun ρ => α * τ * Real.sqrt (1 + x) / (ρ * Real.sqrt ρ) *
        (∫ z, mills (τ * Real.sqrt (1 + x) / Real.sqrt ρ + -Real.sqrt x * z)
          ∂(gaussianReal 0 1)) + ρ⁻¹ - 2 * κ + h ^ 2 / (1 + x)) (Ioi 0) := by
  intro ρ (hρ : 0 < ρ) ρ' (hρ' : 0 < ρ') hlt
  have hA0 : ∀ v, 0 ≤ mills v := gaussianPDFReal_div_measureReal_Ici_nonneg
  have hs : Real.sqrt ρ ≤ Real.sqrt ρ' := Real.sqrt_le_sqrt hlt.le
  have hsρ : 0 < Real.sqrt ρ := Real.sqrt_pos.2 hρ
  have hI : ∫ z, mills (τ * Real.sqrt (1 + x) / Real.sqrt ρ' + -Real.sqrt x * z)
        ∂(gaussianReal 0 1) ≤
      ∫ z, mills (τ * Real.sqrt (1 + x) / Real.sqrt ρ + -Real.sqrt x * z)
        ∂(gaussianReal 0 1) := by
    refine integral_mono (integrable_mills_comp _ _).1 (integrable_mills_comp _ _).1 fun z =>
      monotone_gaussianPDFReal_div_measureReal_Ici (add_le_add ?_ le_rfl)
    exact div_le_div_of_nonneg_left (mul_nonneg hτ (Real.sqrt_nonneg _)) hsρ hs
  have hc : α * τ * Real.sqrt (1 + x) / (ρ' * Real.sqrt ρ') ≤
      α * τ * Real.sqrt (1 + x) / (ρ * Real.sqrt ρ) :=
    div_le_div_of_nonneg_left (mul_nonneg (mul_nonneg hα hτ) (Real.sqrt_nonneg _))
      (mul_pos hρ hsρ) (mul_le_mul hlt.le hs hsρ.le hρ'.le)
  have hprod := mul_le_mul hc hI (integral_nonneg fun _ => hA0 _)
    (div_nonneg (mul_nonneg (mul_nonneg hα hτ) (Real.sqrt_nonneg _)) (by positivity))
  have hinv : ρ'⁻¹ < ρ⁻¹ := inv_strictAnti₀ hρ hlt
  dsimp only
  linarith

/-- The derivative of `F (q, ·)` at `ρ`, expressed in `x = q / (ρ - q)`. -/
private theorem hasDerivAt_snd (α κ h τ : ℝ) {x ρ : ℝ} (hx : 0 ≤ x) (hρ : 0 < ρ) :
    HasDerivAt (fun r => shcherbinaTirozziHardFunctional α κ h τ (x * ρ / (1 + x)) r)
      ((α * (τ * Real.sqrt (1 + x) / Real.sqrt ρ *
            (∫ z, mills (τ * Real.sqrt (1 + x) / Real.sqrt ρ + -Real.sqrt x * z)
              ∂(gaussianReal 0 1)) +
          x * ∫ z, mills (τ * Real.sqrt (1 + x) / Real.sqrt ρ + -Real.sqrt x * z) ^ 2
              ∂(gaussianReal 0 1)) + (1 - x) * (1 + x)) / (2 * ρ) - κ + h ^ 2 / 2) ρ := by
  have h1x : 0 < 1 + x := by linarith
  set q : ℝ := x * ρ / (1 + x) with hq
  have hq0 : 0 ≤ q := div_nonneg (mul_nonneg hx hρ.le) h1x.le
  have hs : ρ - q = ρ / (1 + x) := by
    rw [hq]
    field_simp
    ring
  have hs0 : 0 < ρ - q := hs ▸ div_pos hρ h1x
  have hqρ : q < ρ := sub_pos.1 hs0
  set m : ℝ → ℝ := fun r => τ / Real.sqrt (r - q) with hm
  set σ : ℝ → ℝ := fun r => -Real.sqrt q / Real.sqrt (r - q) with hσ
  set m' : ℝ → ℝ := fun r => -(τ / (2 * (r - q) * Real.sqrt (r - q))) with hm'
  set σ' : ℝ → ℝ := fun r => Real.sqrt q / (2 * (r - q) * Real.sqrt (r - q)) with hσ'
  have hquot : ∀ a r : ℝ, q < r → HasDerivAt (fun r => a / Real.sqrt (r - q))
      (-(a / (2 * (r - q) * Real.sqrt (r - q)))) r := fun a r hr => by
    have hr0 : 0 < r - q := sub_pos.2 hr
    have hsr := (Real.sqrt_pos.2 hr0).ne'
    have h1 : HasDerivAt (fun r => Real.sqrt (r - q)) (1 / (2 * Real.sqrt (r - q))) r := by
      simpa using ((hasDerivAt_id r).sub_const q).sqrt hr0.ne'
    refine ((hasDerivAt_const r a).div h1 hsr).congr_deriv ?_
    rw [Real.sq_sqrt hr0.le]
    field_simp
    ring
  have hmd : ∀ r, q < r → HasDerivAt m (m' r) r := fun r hr => hquot τ r hr
  have hσd : ∀ r, q < r → HasDerivAt σ (σ' r) r := fun r hr => by
    refine (hquot (-Real.sqrt q) r hr).congr_deriv ?_
    rw [hσ']
    ring
  have hden : 2 * (ρ - q) * Real.sqrt (ρ - q) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero hs0.ne') (Real.sqrt_pos.2 hs0).ne'
  have hdenc : ContinuousAt (fun r : ℝ => 2 * (r - q) * Real.sqrt (r - q)) ρ := by fun_prop
  have hmc : ContinuousAt m' ρ :=
    ContinuousAt.neg (ContinuousAt.div continuousAt_const hdenc hden)
  have hσc : ContinuousAt σ' ρ := ContinuousAt.div continuousAt_const hdenc hden
  have hE := hasDerivAt_integral_log_gaussianTail (m := m) (σ := σ) (m' := m') (σ' := σ')
    (t := ρ) ((eventually_gt_nhds hqρ).mono fun r hr => hmd r hr)
    ((eventually_gt_nhds hqρ).mono fun r hr => hσd r hr) hmc hσc
  have hrest : HasDerivAt (fun r => q / (2 * (r - q)) + Real.log (r - q) / 2 - κ * r +
      h ^ 2 * (r - q) / 2)
      (-(q / (2 * (ρ - q) ^ 2)) + (ρ - q)⁻¹ / 2 - κ + h ^ 2 / 2) ρ := by
    have h0 : HasDerivAt (fun r : ℝ => r - q) 1 ρ := (hasDerivAt_id ρ).sub_const q
    have h1 := (hasDerivAt_const ρ q).div (h0.const_mul 2) (mul_ne_zero two_ne_zero hs0.ne')
    have h2 := (h0.log hs0.ne').div_const 2
    have h3 := (hasDerivAt_id ρ).const_mul κ
    have h4 := (h0.const_mul (h ^ 2)).div_const 2
    refine (((h1.add h2).sub h3).add h4).congr_deriv ?_
    field_simp
    ring
  have hsum := (hE.const_mul α).add hrest
  have heq : (fun r => shcherbinaTirozziHardFunctional α κ h τ q r) =ᶠ[𝓝 ρ]
      fun r => α * (∫ z, Real.log ((gaussianReal 0 1).real (Ici (m r + σ r * z)))
          ∂(gaussianReal 0 1)) +
        (q / (2 * (r - q)) + Real.log (r - q) / 2 - κ * r + h ^ 2 * (r - q) / 2) := by
    refine Eventually.of_forall fun r => ?_
    have e : ∀ z : ℝ, (τ - Real.sqrt q * z) / Real.sqrt (r - q) = m r + σ r * z := fun z => by
      simp only [hm, hσ]
      ring
    simp only [shcherbinaTirozziHardFunctional, e]
    ring
  refine (hsum.congr_of_eventuallyEq heq).congr_deriv ?_
  -- evaluate at the point, where `m = τ √(1 + x) / √ρ` and `σ = -√x`
  have hsq : Real.sqrt (ρ - q) = Real.sqrt ρ / Real.sqrt (1 + x) := by
    rw [hs, Real.sqrt_div' _ h1x.le]
  have hsρ := (Real.sqrt_pos.2 hρ).ne'
  have hs1 := (Real.sqrt_pos.2 h1x).ne'
  have hmρ : m ρ = τ * Real.sqrt (1 + x) / Real.sqrt ρ := by
    simp only [hm, hsq]
    field_simp
  have hsqq : Real.sqrt q = Real.sqrt x * (Real.sqrt ρ / Real.sqrt (1 + x)) := by
    rw [hq, Real.sqrt_div' _ h1x.le, Real.sqrt_mul hx, mul_div_assoc]
  have hσρ : σ ρ = -Real.sqrt x := by
    simp only [hσ, hsq, hsqq]
    field_simp
  have hm'ρ : m' ρ = -(m ρ / (2 * (ρ - q))) := by
    change -(τ / (2 * (ρ - q) * Real.sqrt (ρ - q))) =
      -(τ / Real.sqrt (ρ - q) / (2 * (ρ - q)))
    rw [div_div, mul_comm (Real.sqrt (ρ - q))]
  have hσ'ρ : σ' ρ = Real.sqrt x / (2 * (ρ - q)) := by
    have : σ' ρ = -(σ ρ) / (2 * (ρ - q)) := by
      change Real.sqrt q / (2 * (ρ - q) * Real.sqrt (ρ - q)) =
        -(-Real.sqrt q / Real.sqrt (ρ - q)) / (2 * (ρ - q))
      rw [neg_div (Real.sqrt (ρ - q)) (Real.sqrt q), neg_neg, div_div,
        mul_comm (Real.sqrt (ρ - q))]
    rw [this, hσρ, neg_neg]
  obtain ⟨hi, hzi, hi2⟩ := integrable_mills_comp (m ρ) (σ ρ)
  have hIBP := integral_id_mul_mills (m ρ) (σ ρ)
  have hWA : Integrable (fun z => (m ρ + σ ρ * z) * mills (m ρ + σ ρ * z))
      (gaussianReal 0 1) := by
    refine ((hi.const_mul (m ρ)).add (hzi.const_mul (σ ρ))).congr (ae_of_all _ fun z => ?_)
    simp only [Pi.add_apply]
    ring
  have hWAeq : ∫ z, (m ρ + σ ρ * z) * mills (m ρ + σ ρ * z) ∂(gaussianReal 0 1) =
      m ρ * (∫ z, mills (m ρ + σ ρ * z) ∂(gaussianReal 0 1)) +
        σ ρ * ∫ z, z * mills (m ρ + σ ρ * z) ∂(gaussianReal 0 1) := by
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_add (hi.const_mul _) (hzi.const_mul _)]
    exact integral_congr_ae (ae_of_all _ fun z => by ring)
  rw [integral_sub hi2 hWA, hWAeq] at hIBP
  have hder : ∫ z, -(mills (m ρ + σ ρ * z)) * (m' ρ + σ' ρ * z) ∂(gaussianReal 0 1) =
      -(m' ρ) * (∫ z, mills (m ρ + σ ρ * z) ∂(gaussianReal 0 1)) +
        -(σ' ρ) * ∫ z, z * mills (m ρ + σ ρ * z) ∂(gaussianReal 0 1) := by
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_add (hi.const_mul _) (hzi.const_mul _)]
    exact integral_congr_ae (ae_of_all _ fun z => by ring)
  rw [hder, ← hmρ, ← hσρ]
  set I1 := ∫ z, mills (m ρ + σ ρ * z) ∂(gaussianReal 0 1) with hI1
  set I2 := ∫ z, mills (m ρ + σ ρ * z) ^ 2 ∂(gaussianReal 0 1) with hI2
  set J := ∫ z, z * mills (m ρ + σ ρ * z) ∂(gaussianReal 0 1) with hJ
  have hsx2 : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx
  -- solve the integration by parts identity for `J`
  have hJeq : J = -Real.sqrt x * (I2 - m ρ * I1) / (1 + x) := by
    rw [eq_div_iff h1x.ne', ← hσρ]
    have h2 : σ ρ ^ 2 = x := by rw [hσρ, neg_sq, hsx2]
    linear_combination hIBP - J * h2
  have e1 : -(m' ρ) * I1 + -(σ' ρ) * J = (m ρ * I1 + x * I2) / (2 * ρ) := by
    rw [hm'ρ, hσ'ρ, hJeq, hs]
    calc _ = ((1 + x) * (m ρ * I1) + Real.sqrt x ^ 2 * (I2 - m ρ * I1)) / (2 * ρ) := by
          field_simp
      _ = (m ρ * I1 + x * I2) / (2 * ρ) := by
          rw [hsx2]
          ring
  have e2 : -(q / (2 * (ρ - q) ^ 2)) + (ρ - q)⁻¹ / 2 = (1 - x) * (1 + x) / (2 * ρ) := by
    have := hρ.ne'
    have := h1x.ne'
    rw [hs, hq]
    field_simp
    ring
  rw [e1, e2]
  ring

/-- **Corollary 3.3.12:** a zero of `x ↦ ∂G/∂x (x, ρ)` is a strict minimum of
`x ↦ G (x, ρ)` on `(0, ∞)`. -/
theorem shcherbinaTirozziHardFunctional_ratio_lt_of_hasDerivAt_zero {α τ x ρ y : ℝ} (κ h : ℝ)
    (hα : 0 ≤ α) (hτ : 0 ≤ τ) (hx : 0 < x) (hρ : 0 < ρ) (hy : 0 < y) (hyx : y ≠ x)
    (hc : HasDerivAt (fun y => shcherbinaTirozziHardFunctional α κ h τ (y * ρ / (1 + y)) ρ)
      0 x) :
    shcherbinaTirozziHardFunctional α κ h τ (x * ρ / (1 + x)) ρ <
      shcherbinaTirozziHardFunctional α κ h τ (y * ρ / (1 + y)) ρ := by
  obtain ⟨K, hK⟩ : ∃ K : ℝ → ℝ, K = fun x => 1 - α * (∫ z, mills (τ * Real.sqrt (1 + x) /
      Real.sqrt ρ + -Real.sqrt x * z) ^ 2 ∂(gaussianReal 0 1)) / x -
      h ^ 2 * ρ / (x * (1 + x)) := ⟨_, rfl⟩
  have hd : ∀ y, 0 < y →
      HasDerivAt (fun y => shcherbinaTirozziHardFunctional α κ h τ (y * ρ / (1 + y)) ρ)
        (y / (2 * (1 + y)) * K y) y := fun y hy => by
    rw [hK]
    exact hasDerivAt_shcherbinaTirozziHardFunctional_ratio α κ h τ hy hρ
  have hKx : K x = 0 := by
    have h1 := (hd x hx).unique hc
    exact (mul_eq_zero.1 h1).resolve_left (div_pos hx (by linarith)).ne'
  have hαh : α ≠ 0 ∨ h ≠ 0 := by
    by_contra hcon
    push Not at hcon
    simp [hK, hcon.1, hcon.2] at hKx
  have hmono : StrictMonoOn K (Ioi 0) := by
    rw [hK]
    exact strictMonoOn_shcherbinaTirozziHardFunctional_ratio_deriv hα hτ hρ hαh
  refine lt_of_hasDerivAt_neg_of_pos
    (f := fun y => shcherbinaTirozziHardFunctional α κ h τ (y * ρ / (1 + y)) ρ)
    (f' := fun y => y / (2 * (1 + y)) * K y) hx hy hyx hd (fun w hw hwx => ?_) fun w hxw => ?_
  · exact mul_neg_of_pos_of_neg (div_pos hw (by linarith))
      ((hmono hw hx hwx).trans_eq hKx)
  · have hw : 0 < w := hx.trans hxw
    exact mul_pos (div_pos hw (by linarith)) (hKx.symm.trans_lt (hmono hx hw hxw))

/-- A zero of `ρ ↦ ∂G/∂ρ (x, ρ)` is a strict maximum of `ρ ↦ G (x, ρ)` on `(0, ∞)`. -/
theorem shcherbinaTirozziHardFunctional_self_lt_of_hasDerivAt_zero {α τ x ρ r : ℝ} (κ h : ℝ)
    (hα : 0 ≤ α) (hτ : 0 ≤ τ) (hx : 0 ≤ x) (hρ : 0 < ρ) (hr : 0 < r) (hrρ : r ≠ ρ)
    (hc : HasDerivAt (fun r => shcherbinaTirozziHardFunctional α κ h τ (x * r / (1 + x)) r)
      0 ρ) :
    shcherbinaTirozziHardFunctional α κ h τ (x * r / (1 + x)) r <
      shcherbinaTirozziHardFunctional α κ h τ (x * ρ / (1 + x)) ρ := by
  obtain ⟨L, hL⟩ : ∃ L : ℝ → ℝ, L = fun ρ => α * τ * Real.sqrt (1 + x) / (ρ * Real.sqrt ρ) *
      (∫ z, mills (τ * Real.sqrt (1 + x) / Real.sqrt ρ + -Real.sqrt x * z)
        ∂(gaussianReal 0 1)) + ρ⁻¹ - 2 * κ + h ^ 2 / (1 + x) := ⟨_, rfl⟩
  have hd : ∀ r, 0 < r →
      HasDerivAt (fun r => shcherbinaTirozziHardFunctional α κ h τ (x * r / (1 + x)) r)
        (L r / 2) r := fun r hr => by
    rw [hL]
    exact hasDerivAt_shcherbinaTirozziHardFunctional_self α κ h τ hx hr
  have hLρ : L ρ = 0 :=
    (div_eq_zero_iff.1 ((hd ρ hρ).unique hc)).resolve_right two_ne_zero
  have hanti : StrictAntiOn L (Ioi 0) := by
    rw [hL]
    exact strictAntiOn_shcherbinaTirozziHardFunctional_self_deriv (x := x) κ h hα hτ
  refine neg_lt_neg_iff.1 (lt_of_hasDerivAt_neg_of_pos
    (f := fun r => -shcherbinaTirozziHardFunctional α κ h τ (x * r / (1 + x)) r)
    (f' := fun r => -(L r / 2)) hρ hr hrρ (fun r hr => (hd r hr).neg)
    (fun w hw hwρ => ?_) fun w hρw => ?_)
  · have h1 : L ρ < L w := hanti hw hρ hwρ
    linarith
  · have h1 : L w < L ρ := hanti hρ (hρ.trans hρw) hρw
    linarith

/-- A critical point `(q, ρ)` of `F` gives a critical point `(q / (ρ - q), ρ)` of `G`. -/
private theorem exists_ratio_critical (α κ h τ : ℝ) {q ρ : ℝ} (hq : 0 < q) (hqρ : q < ρ)
    (hdq : HasDerivAt (fun q => shcherbinaTirozziHardFunctional α κ h τ q ρ) 0 q)
    (hdρ : HasDerivAt (fun ρ => shcherbinaTirozziHardFunctional α κ h τ q ρ) 0 ρ) :
    ∃ x : ℝ, 0 < x ∧ q = x * ρ / (1 + x) ∧
      HasDerivAt (fun y => shcherbinaTirozziHardFunctional α κ h τ (y * ρ / (1 + y)) ρ) 0 x ∧
      HasDerivAt (fun r => shcherbinaTirozziHardFunctional α κ h τ (x * r / (1 + x)) r)
        0 ρ := by
  have hρ : 0 < ρ := hq.trans hqρ
  have hs : 0 < ρ - q := sub_pos.2 hqρ
  obtain ⟨x, hx, hqx⟩ : ∃ x : ℝ, 0 < x ∧ x * ρ / (1 + x) = q := by
    refine ⟨q / (ρ - q), div_pos hq hs, ?_⟩
    have := hs.ne'
    have := hρ.ne'
    field_simp
    ring
  have h1x : 0 < 1 + x := by linarith
  -- the `x`-derivative, by the chain rule
  have hGx : HasDerivAt (fun y => shcherbinaTirozziHardFunctional α κ h τ (y * ρ / (1 + y)) ρ)
      0 x := by
    have hinner : HasDerivAt (fun y : ℝ => y * ρ / (1 + y)) (ρ / (1 + x) ^ 2) x := by
      refine (((hasDerivAt_id x).mul_const ρ).div ((hasDerivAt_id x).const_add 1)
        h1x.ne').congr_deriv ?_
      simp only [id_eq]
      ring
    have h0 : HasDerivAt (fun q => shcherbinaTirozziHardFunctional α κ h τ q ρ) 0
        (x * ρ / (1 + x)) := by rwa [hqx]
    simpa only [zero_mul, Function.comp_def] using h0.comp x hinner
  -- the `ρ`-derivatives of `F (q, ·)` and `G (x, ·)` agree where `∂G/∂x` vanishes
  refine ⟨x, hx, hqx.symm, hGx, ?_⟩
  have hK := (hasDerivAt_shcherbinaTirozziHardFunctional_ratio α κ h τ hx hρ).unique hGx
  replace hK := (mul_eq_zero.1 hK).resolve_left (div_pos hx (by linarith)).ne'
  have hF := (hasDerivAt_snd α κ h τ hx.le hρ).unique (by rwa [hqx])
  refine (hasDerivAt_shcherbinaTirozziHardFunctional_self α κ h τ hx.le hρ).congr_deriv ?_
  obtain ⟨I1, hI1⟩ : ∃ I1, I1 = ∫ z, mills (τ * Real.sqrt (1 + x) / Real.sqrt ρ +
      -Real.sqrt x * z) ∂(gaussianReal 0 1) := ⟨_, rfl⟩
  obtain ⟨I2, hI2⟩ : ∃ I2, I2 = ∫ z, mills (τ * Real.sqrt (1 + x) / Real.sqrt ρ +
      -Real.sqrt x * z) ^ 2 ∂(gaussianReal 0 1) := ⟨_, rfl⟩
  rw [← hI2] at hK
  rw [← hI1, ← hI2] at hF
  rw [← hI1]
  have key : (α * τ * Real.sqrt (1 + x) / (ρ * Real.sqrt ρ) * I1 + ρ⁻¹ - 2 * κ +
        h ^ 2 / (1 + x)) / 2 =
      ((α * (τ * Real.sqrt (1 + x) / Real.sqrt ρ * I1 + x * I2) + (1 - x) * (1 + x)) /
          (2 * ρ) - κ + h ^ 2 / 2) +
        x ^ 2 / (2 * ρ) * (1 - α * I2 / x - h ^ 2 * ρ / (x * (1 + x))) := by
    have := hx.ne'
    have := hρ.ne'
    have := h1x.ne'
    have := (Real.sqrt_pos.2 hρ).ne'
    field_simp
    ring
  rw [key, hF, hK]
  ring

/-- **Talagrand, Theorem 3.3.1, uniqueness:** for `α ≥ 0` and `τ ≥ 0`, the functional
`F (q, ρ)` has at most one point with `0 < q < ρ` at which both partial derivatives vanish. -/
theorem eq_of_hasDerivAt_shcherbinaTirozziHardFunctional_zero {α τ : ℝ} (κ h : ℝ) (hα : 0 ≤ α)
    (hτ : 0 ≤ τ) {q₁ ρ₁ q₂ ρ₂ : ℝ} (hq₁ : 0 < q₁) (hρ₁ : q₁ < ρ₁) (hq₂ : 0 < q₂)
    (hρ₂ : q₂ < ρ₂)
    (h1q : HasDerivAt (fun q => shcherbinaTirozziHardFunctional α κ h τ q ρ₁) 0 q₁)
    (h1ρ : HasDerivAt (fun ρ => shcherbinaTirozziHardFunctional α κ h τ q₁ ρ) 0 ρ₁)
    (h2q : HasDerivAt (fun q => shcherbinaTirozziHardFunctional α κ h τ q ρ₂) 0 q₂)
    (h2ρ : HasDerivAt (fun ρ => shcherbinaTirozziHardFunctional α κ h τ q₂ ρ) 0 ρ₂) :
    q₁ = q₂ ∧ ρ₁ = ρ₂ := by
  have hρ₁0 : 0 < ρ₁ := hq₁.trans hρ₁
  have hρ₂0 : 0 < ρ₂ := hq₂.trans hρ₂
  obtain ⟨x₁, hx₁, hq₁x, hG1x, hG1ρ⟩ := exists_ratio_critical α κ h τ hq₁ hρ₁ h1q h1ρ
  obtain ⟨x₂, hx₂, hq₂x, hG2x, hG2ρ⟩ := exists_ratio_critical α κ h τ hq₂ hρ₂ h2q h2ρ
  have hx : x₁ = x₂ ∧ ρ₁ = ρ₂ := by
    by_contra hcon
    -- two distinct saddle points would each take a smaller value than the other
    have h12 : ∀ a b c d : ℝ, 0 < a → 0 < b → 0 < c → 0 < d → ¬(a = c ∧ b = d) →
        HasDerivAt (fun y => shcherbinaTirozziHardFunctional α κ h τ (y * b / (1 + y)) b) 0 a →
        HasDerivAt (fun r => shcherbinaTirozziHardFunctional α κ h τ (c * r / (1 + c)) r) 0 d →
        shcherbinaTirozziHardFunctional α κ h τ (a * b / (1 + a)) b <
          shcherbinaTirozziHardFunctional α κ h τ (c * d / (1 + c)) d := by
      intro a b c d ha hb hc hd hne hdx hdρ
      by_cases hca : c = a
      · have hbd : b ≠ d := fun e => hne ⟨hca.symm, e⟩
        have := shcherbinaTirozziHardFunctional_self_lt_of_hasDerivAt_zero κ h hα hτ hc.le hd hb
          hbd hdρ
        rw [hca] at this ⊢
        exact this
      by_cases hbd : b = d
      · subst hbd
        exact shcherbinaTirozziHardFunctional_ratio_lt_of_hasDerivAt_zero κ h hα hτ ha hb hc
          hca hdx
      · exact (shcherbinaTirozziHardFunctional_ratio_lt_of_hasDerivAt_zero κ h hα hτ ha hb hc
          hca hdx).trans (shcherbinaTirozziHardFunctional_self_lt_of_hasDerivAt_zero κ h hα hτ
          hc.le hd hb hbd hdρ)
    have l1 := h12 x₁ ρ₁ x₂ ρ₂ hx₁ hρ₁0 hx₂ hρ₂0 hcon hG1x hG2ρ
    have l2 := h12 x₂ ρ₂ x₁ ρ₁ hx₂ hρ₂0 hx₁ hρ₁0 (fun e => hcon ⟨e.1.symm, e.2.symm⟩) hG2x hG1ρ
    exact lt_asymm l1 l2
  refine ⟨?_, hx.2⟩
  rw [hq₁x, hq₂x, hx.1, hx.2]

end SpinGlasses
