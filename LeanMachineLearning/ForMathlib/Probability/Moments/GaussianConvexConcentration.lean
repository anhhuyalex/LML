/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Probability.Distributions.Gaussian.QuadraticTilt
public import LeanMachineLearning.ForMathlib.Probability.Moments.LogConcaveConcentration

/-!
# Gaussian concentration from a convex set of large measure

A function which is Lipschitz only on a convex set carrying most of the standard Gaussian mass
concentrates: Maurey's inequality applies to the Gaussian measure conditioned on the set, and the
complement is controlled by the Cauchy--Schwarz inequality.

## Main statements

* `ProbabilityTheory.exists_integral_stdGaussian_sub_pow_le_of_lipschitzOn`.
-/

@[expose] public section

open MeasureTheory Module
open scoped RealInnerProductSpace

namespace ProbabilityTheory

/-- **Concentration from a convex set of large Gaussian mass.** Let `C` be a convex measurable set
of positive standard Gaussian measure `γ` with `γ Cᶜ ≤ α²`, and let `f` be `A`-Lipschitz on `C`
with `|f| ≤ B` there. Suppose that `∫ (f - m) ^ (4 k) dγ ≤ β²` whenever `|m| ≤ B`. Then some `m`
with `|m| ≤ B` (the mean of `f` conditioned on `C`) satisfies
`∫ (f - m) ^ (2 k) dγ ≤ 4 (16 k A²) ^ k + α β`. -/
theorem exists_integral_stdGaussian_sub_pow_le_of_lipschitzOn {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] {C : Set E} (hC : Convex ℝ C) (hCm : MeasurableSet C)
    (hCpos : 0 < (stdGaussian E).real C) {f : E → ℝ} (hf : Measurable f) {A B : ℝ} (hA : 0 ≤ A)
    (hlip : ∀ x ∈ C, ∀ y ∈ C, |f x - f y| ≤ A * ‖x - y‖) (hB : ∀ x ∈ C, |f x| ≤ B)
    {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (htail : (stdGaussian E).real Cᶜ ≤ α ^ 2) {k : ℕ}
    (h4 : ∀ m : ℝ, |m| ≤ B → Integrable (fun x => (f x - m) ^ (4 * k)) (stdGaussian E) ∧
      ∫ x, (f x - m) ^ (4 * k) ∂(stdGaussian E) ≤ β ^ 2) :
    ∃ m : ℝ, |m| ≤ B ∧ Integrable (fun x => (f x - m) ^ (2 * k)) (stdGaussian E) ∧
      ∫ x, (f x - m) ^ (2 * k) ∂(stdGaussian E) ≤ 4 * (16 * k * A ^ 2) ^ k + α * β := by
  set γ := stdGaussian E with hγ
  have hCvol : volume C ≠ 0 := fun h0 => by
    have hac : γ ≪ volume := by
      rw [hγ, stdGaussian_eq_withDensity]
      exact withDensity_absolutelyContinuous _ _
    rw [measureReal_def, hac h0] at hCpos
    simp at hCpos
  set γ' := (volume.restrict C).tilted (fun x : E => -(‖x‖ ^ 2 / 2)) with hγ'
  have hint : IntegrableOn (fun x : E => Real.exp (-(‖x‖ ^ 2 / 2))) C volume := by
    have h := integrable_exp_neg_mul_sq_norm_add_inner (E := E)
      (by norm_num : (0 : ℝ) < 1 / 2) 0
    refine (h.congr (ae_of_all _ fun x => ?_)).integrableOn
    simp only [inner_zero_left, add_zero]
    congr 1; ring
  have hmid : ∀ x ∈ C, ∀ y ∈ C, (1 / 2 : ℝ) * ‖(1 / 2 : ℝ) • (x - y)‖ ^ 2 ≤
      (‖x‖ ^ 2 / 2 + ‖y‖ ^ 2 / 2) / 2 - ‖(1 / 2 : ℝ) • (x + y)‖ ^ 2 / 2 := fun x _ y _ => by
    have := parallelogram_law_with_norm ℝ x y
    simp only [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2), mul_pow]
    nlinarith
  have hMau := integral_sub_integral_pow_le_of_lipschitz (μ₀ := volume) (C := C)
    (H := fun x => ‖x‖ ^ 2 / 2) (κ := 1 / 2) hC hCm hCvol
    ((measurable_norm.pow_const 2).div_const 2) hint hmid (by norm_num) hA hlip k
  rw [← hγ'] at hMau
  have hprob' : IsProbabilityMeasure γ' :=
    isProbabilityMeasure_tilted_restrict (H := fun x => ‖x‖ ^ 2 / 2) hCvol hint
  set m : ℝ := ∫ x, f x ∂γ' with hm
  have hmb : |m| ≤ B := by
    have h := norm_integral_le_of_norm_le_const (μ := γ') (f := f) (C := B)
      ((ae_mem_of_tilted_restrict (μ₀ := volume) (H := fun x => ‖x‖ ^ 2 / 2) hCm).mono
        fun x hx => by simpa only [Real.norm_eq_abs] using hB x hx)
    simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using h
  obtain ⟨hi4, hI4⟩ := h4 m hmb
  have heven : Even (2 * k) := even_two_mul k
  have hpow : ∀ x, ((f x - m) ^ (2 * k)) ^ 2 = (f x - m) ^ (4 * k) := fun x => by
    rw [← pow_mul]
    congr 1
    ring
  have h2L : MemLp (fun x => (f x - m) ^ (2 * k)) 2 γ := by
    refine (memLp_two_iff_integrable_sq ((hf.sub_const m).pow_const _).aestronglyMeasurable).2
      ?_
    simpa only [hpow] using hi4
  have hi2 : Integrable (fun x => (f x - m) ^ (2 * k)) γ := h2L.integrable one_le_two
  refine ⟨m, hmb, hi2, ?_⟩
  have hgood : ∫ x in C, (f x - m) ^ (2 * k) ∂γ ≤ 4 * (16 * k * A ^ 2) ^ k := by
    have h := integral_tilted_restrict_neg_half_sq_norm hCm (fun x : E => (f x - m) ^ (2 * k))
    rw [← hγ', ← hγ] at h
    have h1 : ∫ x in C, (f x - m) ^ (2 * k) ∂γ =
        γ.real C * ∫ x, (f x - m) ^ (2 * k) ∂γ' := by
      rw [h, mul_div_cancel₀ _ hCpos.ne']
    rw [h1]
    refine (mul_le_of_le_one_left (integral_nonneg fun _ => heven.pow_nonneg _)
      measureReal_le_one).trans (hMau.2.trans_eq ?_)
    congr 2
    ring
  have hfar : ∫ x in Cᶜ, (f x - m) ^ (2 * k) ∂γ ≤ α * β :=
    (Real.le_norm_self _).trans (norm_setIntegral_le_mul_of_integral_sq_le hCm.compl
      (measure_ne_top _ _) h2L hα hβ htail
      (by simpa only [Real.norm_eq_abs, sq_abs, hpow] using hI4))
  rw [← integral_add_compl hCm hi2]
  exact add_le_add hgood hfar

end ProbabilityTheory
