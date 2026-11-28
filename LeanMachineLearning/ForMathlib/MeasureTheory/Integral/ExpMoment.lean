/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

import LeanMachineLearning.ForMathlib.Analysis.SpecialFunctions.AddPowEstimates

public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Moments from exponential moments

On a probability space, `1 + c x ≤ exp (c x)` turns an exponential moment bound
`∫ exp (c X) ≤ C` into the first moment bound `c ∫ X ≤ C - 1`.  The pointwise inequality is
stated for an arbitrary integrand `Z`, so that it also applies to conditional expectations.

All moments of a nonnegative variable `X` are controlled by its exponential moment: if
`∫ exp X ≤ exp C` then `∫ X ^ k ≤ 2 ^ k (k ^ k + C ^ k)`
(`MeasureTheory.integral_pow_le_of_integral_exp_le`), from the pointwise bound
`x ^ k ≤ k ^ k exp x` (`Real.pow_le_natCast_pow_mul_exp`).
-/

@[expose] public section

open MeasureTheory

/-- `x ^ k ≤ k ^ k * exp x` for `x ≥ 0` (Talagrand, Eq. (3.20)). -/
theorem Real.pow_le_natCast_pow_mul_exp {x : ℝ} (hx : 0 ≤ x) (k : ℕ) :
    x ^ k ≤ (k : ℝ) ^ k * Real.exp x := by
  have h := Real.pow_div_factorial_le_exp x hx k
  rw [div_le_iff₀ (by positivity), mul_comm] at h
  exact h.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.factorial_le_pow k)
    (Real.exp_pos _).le)

namespace MeasureTheory

/-- If `1 + c * Y ≤ Z` almost everywhere on a probability space, then
`1 + c * ∫ Y ≤ ∫ Z`. -/
theorem one_add_mul_integral_le_integral_of_ae {Ω : Type*} {m : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Y Z : Ω → ℝ} (c : ℝ) (hY : Integrable Y μ)
    (hZ : Integrable Z μ) (h : ∀ᵐ ω ∂μ, 1 + c * Y ω ≤ Z ω) :
    1 + c * ∫ ω, Y ω ∂μ ≤ ∫ ω, Z ω ∂μ := by
  have hint : ∫ ω, (1 + c * Y ω) ∂μ ≤ ∫ ω, Z ω ∂μ :=
    integral_mono_ae ((integrable_const 1).add (hY.const_mul c)) hZ h
  rwa [integral_add (integrable_const 1) (hY.const_mul c), integral_const, integral_const_mul,
    probReal_univ, one_smul] at hint

/-- If `1 + c * Y ≤ Z` pointwise on a probability space, then `1 + c * ∫ Y ≤ ∫ Z`. -/
theorem one_add_mul_integral_le_integral {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {Y Z : Ω → ℝ} (c : ℝ) (hY : Integrable Y μ) (hZ : Integrable Z μ)
    (h : ∀ ω, 1 + c * Y ω ≤ Z ω) : 1 + c * ∫ ω, Y ω ∂μ ≤ ∫ ω, Z ω ∂μ :=
  one_add_mul_integral_le_integral_of_ae c hY hZ (ae_of_all _ h)

/-- `1 + c ∫ X ≤ ∫ exp (c X)` on a probability space. -/
theorem one_add_mul_integral_le_integral_exp {Ω : Type*} {m : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ} (c : ℝ) (hX : Integrable X μ)
    (hexp : Integrable (fun ω => Real.exp (c * X ω)) μ) :
    1 + c * ∫ ω, X ω ∂μ ≤ ∫ ω, Real.exp (c * X ω) ∂μ :=
  one_add_mul_integral_le_integral c hX hexp fun ω => by
    simpa [add_comm] using Real.add_one_le_exp (c * X ω)

/-- **Two-level version:** for a family of probability measures `μ ω` indexed by a probability
space, `1 + c 𝔼 ∫ X dμ ≤ 𝔼 ∫ exp (c X) dμ`, with integrability under `μ ω` needed only for
almost every `ω`. -/
theorem one_add_mul_integral_integral_le_of_ae {Ω Γ : Type*} {mΩ : MeasurableSpace Ω}
    {mΓ : MeasurableSpace Γ} {P : Measure Ω} [IsProbabilityMeasure P] {μ : Ω → Measure Γ}
    [∀ ω, IsProbabilityMeasure (μ ω)] {X : Γ → ℝ} (c : ℝ) (hX : ∀ᵐ ω ∂P, Integrable X (μ ω))
    (hexp : ∀ᵐ ω ∂P, Integrable (fun σ => Real.exp (c * X σ)) (μ ω))
    (hJX : Integrable (fun ω => ∫ σ, X σ ∂μ ω) P)
    (hJexp : Integrable (fun ω => ∫ σ, Real.exp (c * X σ) ∂μ ω) P) :
    1 + c * ∫ ω, ∫ σ, X σ ∂μ ω ∂P ≤ ∫ ω, ∫ σ, Real.exp (c * X σ) ∂μ ω ∂P :=
  one_add_mul_integral_le_integral_of_ae c hJX hJexp (by
    filter_upwards [hX, hexp] with ω h1 h2 using one_add_mul_integral_le_integral_exp c h1 h2)

/-- **Two-level version:** for a family of probability measures `μ ω` indexed by a probability
space, `1 + c 𝔼 ∫ X dμ ≤ 𝔼 ∫ exp (c X) dμ`.  This is the passage from an exponential moment of a
random Gibbs average to its second moment. -/
theorem one_add_mul_integral_integral_le {Ω Γ : Type*} {mΩ : MeasurableSpace Ω}
    {mΓ : MeasurableSpace Γ} {P : Measure Ω} [IsProbabilityMeasure P] {μ : Ω → Measure Γ}
    [∀ ω, IsProbabilityMeasure (μ ω)] {X : Γ → ℝ} (c : ℝ) (hX : ∀ ω, Integrable X (μ ω))
    (hexp : ∀ ω, Integrable (fun σ => Real.exp (c * X σ)) (μ ω))
    (hJX : Integrable (fun ω => ∫ σ, X σ ∂μ ω) P)
    (hJexp : Integrable (fun ω => ∫ σ, Real.exp (c * X σ) ∂μ ω) P) :
    1 + c * ∫ ω, ∫ σ, X σ ∂μ ω ∂P ≤ ∫ ω, ∫ σ, Real.exp (c * X σ) ∂μ ω ∂P :=
  one_add_mul_integral_integral_le_of_ae c (ae_of_all _ hX) (ae_of_all _ hexp) hJX hJexp

/-- **Moments from the exponential moment** (Talagrand, Lemma 3.1.8, Eq. (3.29)): on a
probability space, if `X ≥ 0` and `∫ exp X ≤ exp C`, then `∫ X ^ k ≤ 2 ^ k (k ^ k + C ^ k)`.
The inequality `0 ≤ C` is a consequence of the hypotheses. -/
theorem integral_pow_le_of_integral_exp_le {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX0 : 0 ≤ᵐ[μ] X)
    (hint : Integrable (fun ω => Real.exp (X ω)) μ) {C : ℝ}
    (hC : ∫ ω, Real.exp (X ω) ∂μ ≤ Real.exp C) (k : ℕ) :
    Integrable (fun ω => X ω ^ k) μ ∧
      ∫ ω, X ω ^ k ∂μ ≤ 2 ^ k * ((k : ℝ) ^ k + C ^ k) := by
  have hXm : AEMeasurable X μ := Real.aemeasurable_of_aemeasurable_exp hint.1.aemeasurable
  have hC0 : 0 ≤ C := by
    have h1 : (1 : ℝ) ≤ ∫ ω, Real.exp (X ω) ∂μ := by
      have := integral_mono_ae (integrable_const (1 : ℝ)) hint
        (hX0.mono fun ω h => Real.one_le_exp h)
      simpa using this
    exact Real.one_le_exp_iff.1 (h1.trans hC)
  have hXk : AEStronglyMeasurable (fun ω => X ω ^ k) μ := (hXm.pow_const k).aestronglyMeasurable
  set Y : Ω → ℝ := fun ω => max (X ω - C) 0 with hY
  have hYm : AEMeasurable Y μ := (hXm.sub_const C).max aemeasurable_const
  have hY0 : ∀ ω, 0 ≤ Y ω := fun ω => le_max_right _ _
  have hexpY : ∀ ω, Real.exp (Y ω) ≤ 1 + Real.exp (-C) * Real.exp (X ω) := fun ω => by
    rw [← Real.exp_add, neg_add_eq_sub]
    rcases le_total (X ω - C) 0 with h | h
    · rw [hY]; simp only [max_eq_right h, Real.exp_zero]
      exact le_add_of_nonneg_right (Real.exp_pos _).le
    · rw [hY]; simp only [max_eq_left h]
      exact le_add_of_nonneg_left zero_le_one
  have hdom : Integrable (fun ω => 1 + Real.exp (-C) * Real.exp (X ω)) μ :=
    (integrable_const 1).add (hint.const_mul _)
  have hexpYi : Integrable (fun ω => Real.exp (Y ω)) μ :=
    Integrable.mono' hdom (Real.measurable_exp.comp_aemeasurable hYm).aestronglyMeasurable
      (ae_of_all _ fun ω => by
        rw [Real.norm_of_nonneg (Real.exp_pos _).le]
        exact hexpY ω)
  have hexpY2 : ∫ ω, Real.exp (Y ω) ∂μ ≤ 2 := by
    refine (integral_mono hexpYi hdom hexpY).trans ?_
    rw [integral_add (integrable_const 1) (hint.const_mul _), integral_const_mul]
    have : Real.exp (-C) * ∫ ω, Real.exp (X ω) ∂μ ≤ 1 := by
      refine (mul_le_mul_of_nonneg_left hC (Real.exp_pos _).le).trans_eq ?_
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    simp only [integral_const, probReal_univ, one_smul]
    linarith
  have hYk : ∀ ω, Y ω ^ k ≤ (k : ℝ) ^ k * Real.exp (Y ω) := fun ω =>
    Real.pow_le_natCast_pow_mul_exp (hY0 ω) k
  have hYki : Integrable (fun ω => Y ω ^ k) μ :=
    Integrable.mono' (hexpYi.const_mul ((k : ℝ) ^ k)) (hYm.pow_const k).aestronglyMeasurable
      (ae_of_all _ fun ω => by
        rw [Real.norm_of_nonneg (pow_nonneg (hY0 ω) k)]
        exact hYk ω)
  have hYkI : ∫ ω, Y ω ^ k ∂μ ≤ (k : ℝ) ^ k * 2 := by
    refine (integral_mono hYki (hexpYi.const_mul _) hYk).trans ?_
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left hexpY2 (by positivity)
  have hpt : ∀ᵐ ω ∂μ, X ω ^ k ≤ 2 ^ (k - 1) * (Y ω ^ k + C ^ k) := hX0.mono fun ω h => by
    have hle : X ω ≤ Y ω + C := by
      have := le_max_left (X ω - C) 0
      simp only [hY]; linarith
    exact (pow_le_pow_left₀ h hle k).trans (add_pow_le (hY0 ω) hC0 k)
  have hdom2 : Integrable (fun ω => 2 ^ (k - 1) * (Y ω ^ k + C ^ k)) μ :=
    (hYki.add (integrable_const _)).const_mul _
  have hXki : Integrable (fun ω => X ω ^ k) μ :=
    Integrable.mono' hdom2 hXk (by
      filter_upwards [hpt, hX0] with ω h h0
      rwa [Real.norm_of_nonneg (pow_nonneg h0 k)])
  refine ⟨hXki, ?_⟩
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · norm_num
  refine (integral_mono_ae hXki hdom2 hpt).trans ?_
  rw [integral_const_mul, integral_add hYki (integrable_const _), integral_const, probReal_univ,
    one_smul]
  have h2 : (2 : ℝ) ^ k = 2 ^ (k - 1) * 2 := by
    rw [← pow_succ]; congr 1; omega
  rw [h2, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have := pow_nonneg hC0 k
  linarith

/-- An exponential moment of a square controls shifted even moments of its absolute value. -/
theorem integrable_one_add_abs_pow_of_integrable_exp_sq {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {X : Ω → ℝ} (hX : AEStronglyMeasurable X μ) {K : ℝ} (hK : 0 < K)
    (h : Integrable (fun x => Real.exp (X x ^ 2 / K)) μ) (m : ℕ) :
    Integrable (fun x => (1 + |X x|) ^ (2 * m)) μ := by
  let A : ℝ := K ^ m * (m.factorial : ℝ)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  refine (h.const_mul (2 ^ (2 * m - 1) * (1 + A))).mono'
    ((aestronglyMeasurable_const.add hX.abs).pow _) (ae_of_all _ fun x => ?_)
  have hpow : |X x| ^ (2 * m) ≤ A * Real.exp (X x ^ 2 / K) := by
    have hexp := Real.pow_div_factorial_le_exp (X x ^ 2 / K) (by positivity) m
    rw [div_pow, div_div, div_le_iff₀ (by positivity)] at hexp
    rw [pow_mul, sq_abs]
    simpa only [A, mul_comm] using hexp
  rw [Real.norm_of_nonneg (by positivity)]
  calc
    (1 + |X x|) ^ (2 * m) ≤ 2 ^ (2 * m - 1) * (1 + |X x| ^ (2 * m)) := by
      simpa only [one_pow] using add_pow_le zero_le_one (abs_nonneg (X x)) (2 * m)
    _ ≤ 2 ^ (2 * m - 1) * (Real.exp (X x ^ 2 / K) + A * Real.exp (X x ^ 2 / K)) :=
      mul_le_mul_of_nonneg_left (add_le_add (Real.one_le_exp (by positivity)) hpow) (by positivity)
    _ = _ := by ring

end MeasureTheory
