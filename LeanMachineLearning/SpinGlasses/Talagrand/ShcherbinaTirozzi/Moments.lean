/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Pi
public import LeanMachineLearning.ForMathlib.MeasureTheory.Integral.ExpMoment
public import LeanMachineLearning.ForMathlib.Probability.Distributions.Gaussian.ExpSq
public import LeanMachineLearning.SpinGlasses.Talagrand.ShcherbinaTirozzi.Convexity

/-!
# The Shcherbina--Tirozzi model: the Gibbs measure lives on a ball of radius `√N`

The constants below depend only on `κ₀, h₀, D` and are chosen before `N, M, k` and the disorder.
Throughout, `B^*` denotes the expression of Eq. (3.27),
`N + √(∑_{i,k} g_{i,k}²) + ∑_i g_i²`, which is written out in the statements.

## Main declarations

* `SpinGlasses.exists_integral_exp_half_sq_norm_shcherbinaTirozziGibbs_le_exp`:
  Corollary 3.1.7.
* `SpinGlasses.exists_integral_sq_norm_pow_shcherbinaTirozziGibbs_le`: Corollary 3.1.9.
* `SpinGlasses.integral_exp_shcherbinaTirozzi_radius_div_four_le`: Eq. (3.33).
* `SpinGlasses.integral_shcherbinaTirozzi_radius_pow_le`: Lemma 3.1.10.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Module
open scoped RealInnerProductSpace Real

namespace SpinGlasses

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)

variable {N M : ℕ}

/-- **Corollary 3.1.7:** under (3.6) and (3.25), `⟨exp (κ ‖σ‖² / 2)⟩ ≤ exp (K B^*)`, where `K`
depends only on `κ₀, h₀, D`. -/
theorem exists_integral_exp_half_sq_norm_shcherbinaTirozziGibbs_le_exp (κ₀ h₀ D : ℝ)
    (hκ₀ : 0 < κ₀) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (N M : ℕ) (κ h : ℝ) (u : ℝ → ℝ) (g : Fin M → Fin N → ℝ)
      (g₀ : Fin N → ℝ), κ₀ ≤ κ → |h| ≤ h₀ → M ≤ 10 * N → Measurable u →
      (∀ x, u x ≤ 0) → (∀ x, -D * (1 + |x|) ≤ u x) →
        ∫ σ, Real.exp (κ / 2 * ‖σ‖ ^ 2)
            ∂(volume.tilted fun σ => -shcherbinaTirozziHamiltonian κ h u g g₀ σ) ≤
          Real.exp (K * (N + Real.sqrt (∑ k, ∑ i, g k i ^ 2) + ∑ i, g₀ i ^ 2)) := by
  set K : ℝ := 1 + 10 * |D| + |D| * Real.sqrt (10 / κ₀) + h₀ ^ 2 / (2 * κ₀) with hK
  have h10 : 0 ≤ h₀ ^ 2 / (2 * κ₀) := div_nonneg (sq_nonneg _) (by positivity)
  have hDs : 0 ≤ |D| * Real.sqrt (10 / κ₀) := mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)
  refine ⟨K, by rw [hK]; linarith [abs_nonneg D],
    fun N M κ h u g g₀ hκ hh hM hu hu0 hD => ?_⟩
  have hκ0 : 0 < κ := hκ₀.trans_le hκ
  have hD0 : 0 ≤ D := by
    have h1 := (hD 0).trans (hu0 0)
    simp only [abs_zero, add_zero, mul_one] at h1
    linarith
  rw [abs_of_nonneg hD0] at hK hDs
  set S : ℝ := ∑ k, ∑ i, g k i ^ 2 with hS
  set T : ℝ := ∑ i, g₀ i ^ 2 with hT
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun i _ => sq_nonneg _
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun i _ => sq_nonneg _
  have h35 := (integral_exp_half_sq_norm_shcherbinaTirozziGibbs_le (h := h) hκ0 hu hu0 g g₀).2
  have h36 := inv_integral_exp_neg_shcherbinaTirozziHamiltonian_le (h := h) hκ0 hu hu0 hD g g₀
  rw [← hS] at h36
  rw [← hT] at h35
  have h2 : (κ / π) ^ ((N : ℝ) / 2) * (2 * π / κ) ^ ((N : ℝ) / 2) ≤ Real.exp N := by
    rw [← Real.mul_rpow (by positivity) (by positivity),
      show κ / π * (2 * π / κ) = 2 by field_simp]
    have h2e : (2 : ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp (1 : ℝ)
      linarith
    refine (Real.rpow_le_rpow zero_le_two h2e (by positivity)).trans ?_
    rw [Real.exp_one_rpow, Real.exp_le_exp]
    linarith [Nat.cast_nonneg (α := ℝ) N]
  have hMN : (M : ℝ) ≤ 10 * N := by exact_mod_cast hM
  have hsqrt : Real.sqrt (M / (κ * N) * S) ≤ Real.sqrt (10 / κ₀) * Real.sqrt S := by
    rw [← Real.sqrt_mul (by positivity)]
    refine Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right ?_ hS0)
    rcases Nat.eq_zero_or_pos N with hN | hN
    · rw [hN, Nat.cast_zero, mul_zero, div_zero]
      positivity
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    rw [div_le_div_iff₀ (by positivity) hκ₀]
    calc (M : ℝ) * κ₀ ≤ 10 * N * κ := mul_le_mul hMN hκ hκ₀.le (by positivity)
      _ = 10 * (κ * N) := by ring
  have hfield : h ^ 2 * T / (2 * κ) ≤ h₀ ^ 2 / (2 * κ₀) * T := by
    rw [div_mul_eq_mul_div]
    exact div_le_div₀ (mul_nonneg (sq_nonneg _) hT0)
      (mul_le_mul_of_nonneg_right (show h ^ 2 ≤ h₀ ^ 2 by
        rw [← sq_abs h]
        exact pow_le_pow_left₀ (abs_nonneg _) hh 2) hT0) (by positivity)
      (by linarith)
  have htotal : (N : ℝ) + D * (M + Real.sqrt (M / (κ * N) * S)) + h ^ 2 * T / (2 * κ) ≤
      K * (N + Real.sqrt S + T) := by
    have h1 : D * (M + Real.sqrt (M / (κ * N) * S)) ≤
        10 * D * N + D * Real.sqrt (10 / κ₀) * Real.sqrt S := by
      have := mul_le_mul_of_nonneg_left (add_le_add hMN hsqrt) hD0
      linarith
    have hKN : (1 + 10 * D) * N ≤ K * N :=
      mul_le_mul_of_nonneg_right (by rw [hK]; linarith) (Nat.cast_nonneg N)
    have hKS : D * Real.sqrt (10 / κ₀) * Real.sqrt S ≤ K * Real.sqrt S :=
      mul_le_mul_of_nonneg_right (by rw [hK]; linarith) (Real.sqrt_nonneg _)
    have hKT : h₀ ^ 2 / (2 * κ₀) * T ≤ K * T :=
      mul_le_mul_of_nonneg_right (by rw [hK]; linarith) hT0
    rw [mul_add, mul_add]
    linarith
  refine h35.trans ?_
  refine (mul_le_mul_of_nonneg_right h36 (by positivity)).trans ?_
  calc (κ / π) ^ ((N : ℝ) / 2) * Real.exp (D * (M + Real.sqrt (M / (κ * N) * S))) *
        ((2 * π / κ) ^ ((N : ℝ) / 2) * Real.exp (h ^ 2 * T / (2 * κ)))
      = ((κ / π) ^ ((N : ℝ) / 2) * (2 * π / κ) ^ ((N : ℝ) / 2)) *
          (Real.exp (D * (M + Real.sqrt (M / (κ * N) * S))) *
            Real.exp (h ^ 2 * T / (2 * κ))) := by ring
    _ ≤ Real.exp N * (Real.exp (D * (M + Real.sqrt (M / (κ * N) * S))) *
          Real.exp (h ^ 2 * T / (2 * κ))) := mul_le_mul_of_nonneg_right h2 (by positivity)
    _ ≤ Real.exp (K * (N + Real.sqrt S + T)) := by
        rw [← Real.exp_add, ← Real.exp_add, Real.exp_le_exp, ← add_assoc]
        exact htotal

/-- **Corollary 3.1.9:** for `k ≤ 4 N`, `⟨‖σ‖^{2k}⟩ ≤ (K B^*)^k`. Integrability is part of the
conclusion. -/
theorem exists_integral_sq_norm_pow_shcherbinaTirozziGibbs_le (κ₀ h₀ D : ℝ) (hκ₀ : 0 < κ₀) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (N M k : ℕ) (κ h : ℝ) (u : ℝ → ℝ) (g : Fin M → Fin N → ℝ)
      (g₀ : Fin N → ℝ), κ₀ ≤ κ → |h| ≤ h₀ → M ≤ 10 * N → k ≤ 4 * N → Measurable u →
      (∀ x, u x ≤ 0) → (∀ x, -D * (1 + |x|) ≤ u x) →
        Integrable (fun σ : ℝ^N => ‖σ‖ ^ (2 * k))
            (volume.tilted fun σ => -shcherbinaTirozziHamiltonian κ h u g g₀ σ) ∧
          ∫ σ, ‖σ‖ ^ (2 * k)
              ∂(volume.tilted fun σ => -shcherbinaTirozziHamiltonian κ h u g g₀ σ) ≤
            (K * (N + Real.sqrt (∑ k, ∑ i, g k i ^ 2) + ∑ i, g₀ i ^ 2)) ^ k := by
  obtain ⟨K₁, hK₁, h317⟩ :=
    exists_integral_exp_half_sq_norm_shcherbinaTirozziGibbs_le_exp κ₀ h₀ D hκ₀
  refine ⟨4 / κ₀ * (4 + K₁), by positivity,
    fun N M k κ h u g g₀ hκ hh hM hk hu hu0 hD => ?_⟩
  have hκ0 : 0 < κ := hκ₀.trans_le hκ
  have := isProbabilityMeasure_shcherbinaTirozziGibbs (h := h) hκ0 hu hu0 g g₀
  set G := volume.tilted fun σ => -shcherbinaTirozziHamiltonian κ h u g g₀ σ with hG
  set B : ℝ := N + Real.sqrt (∑ k, ∑ i, g k i ^ 2) + ∑ i, g₀ i ^ 2 with hB
  have hNB : (N : ℝ) ≤ B := by
    have h2 : 0 ≤ ∑ i, g₀ i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    rw [hB]
    linarith [Real.sqrt_nonneg (∑ k, ∑ i, g k i ^ 2)]
  have hB0 : 0 ≤ B := (Nat.cast_nonneg N).trans hNB
  have hX0 : 0 ≤ᵐ[G] fun σ : ℝ^N => κ / 2 * ‖σ‖ ^ 2 :=
    ae_of_all _ fun σ => mul_nonneg (by positivity) (sq_nonneg _)
  have hexp := (integral_exp_half_sq_norm_shcherbinaTirozziGibbs_le (h := h) hκ0 hu hu0 g g₀).1
  have hmom := integral_pow_le_of_integral_exp_le hX0 hexp
    (h317 N M κ h u g g₀ hκ hh hM hu hu0 hD) k
  have hpow : ∀ σ : ℝ^N,
      ‖σ‖ ^ (2 * k) = (2 / κ) ^ k * (κ / 2 * ‖σ‖ ^ 2) ^ k := fun σ => by
    rw [← mul_pow, pow_mul]
    congr 1
    field_simp
  rcases eq_or_ne k 0 with rfl | hk0
  · simp
  simp_rw [hpow]
  refine ⟨hmom.1.const_mul _, ?_⟩
  rw [integral_const_mul]
  refine (mul_le_mul_of_nonneg_left hmom.2 (by positivity)).trans ?_
  have h1 : (k : ℝ) ^ k ≤ (4 * B) ^ k := by
    refine pow_le_pow_left₀ (Nat.cast_nonneg _) ?_ k
    have h4 : (k : ℝ) ≤ 4 * N := by exact_mod_cast hk
    exact h4.trans (mul_le_mul_of_nonneg_left hNB (by norm_num))
  have h2 : (k : ℝ) ^ k + (K₁ * B) ^ k ≤ ((4 + K₁) * B) ^ k := by
    refine (add_le_add h1 le_rfl).trans ?_
    rw [add_mul]
    exact pow_add_pow_le (by positivity) (mul_nonneg hK₁ hB0) hk0
  have h3 : (2 / κ) ^ k * 2 ^ k ≤ (4 / κ₀) ^ k := by
    rw [← mul_pow]
    refine pow_le_pow_left₀ (by positivity) ?_ k
    rw [div_mul_eq_mul_div]
    exact div_le_div₀ (by norm_num) (by norm_num) hκ₀ hκ
  calc (2 / κ) ^ k * (2 ^ k * ((k : ℝ) ^ k + (K₁ * B) ^ k))
      = ((2 / κ) ^ k * 2 ^ k) * ((k : ℝ) ^ k + (K₁ * B) ^ k) := by ring
    _ ≤ (4 / κ₀) ^ k * ((4 + K₁) * B) ^ k :=
        mul_le_mul h3 h2 (add_nonneg (by positivity) (pow_nonneg (mul_nonneg hK₁ hB0) _))
          (by positivity)
    _ = (4 / κ₀ * (4 + K₁) * B) ^ k := by rw [← mul_pow]; ring

/-- The exponential moment of a weighted sum of squares of i.i.d. standard Gaussians. -/
private theorem integrable_exp_mul_sum_sq_pi_gaussianReal_and_le {ι : Type*} [Fintype ι] {t : ℝ}
    (ht0 : 0 ≤ t) (ht : t ≤ 1 / 4) :
    Integrable (fun x : ι → ℝ => Real.exp (t * ∑ i, x i ^ 2))
        (Measure.pi fun _ : ι => gaussianReal 0 1) ∧
      ∫ x, Real.exp (t * ∑ i, x i ^ 2) ∂(Measure.pi fun _ : ι => gaussianReal 0 1) ≤
        Real.exp (2 * t * Fintype.card ι) := by
  have ht2 : t < 1 / 2 := by linarith
  have e : ∀ x : ι → ℝ, Real.exp (t * ∑ i, x i ^ 2) = ∏ i, Real.exp (t * x i ^ 2) :=
    fun x => by rw [Finset.mul_sum, Real.exp_sum]
  simp_rw [e]
  refine ⟨Integrable.fintype_prod (f := fun _ : ι => fun y : ℝ => Real.exp (t * y ^ 2))
    fun _ => integrable_exp_mul_sq_gaussianReal ht2, ?_⟩
  rw [integral_fintype_prod_eq_prod (fun _ : ι => fun y : ℝ => Real.exp (t * y ^ 2)),
    integral_exp_mul_sq_gaussianReal ht2, Finset.prod_const, Finset.card_univ]
  have h1 : (Real.sqrt (1 - 2 * t))⁻¹ ≤ Real.exp (2 * t) := by
    have hpos : 0 < 1 - 2 * t := by linarith
    have hlow : Real.exp (-(4 * t)) ≤ 1 - 2 * t := by
      have h2 : Real.exp (-(4 * t)) ≤ (1 + 4 * t)⁻¹ := by
        rw [Real.exp_neg]
        exact inv_anti₀ (by linarith) (by linarith [Real.add_one_le_exp (4 * t)])
      refine h2.trans ?_
      rw [inv_le_iff_one_le_mul₀ (by linarith)]
      nlinarith
    have h3 : Real.exp (-(2 * t)) ≤ Real.sqrt (1 - 2 * t) := by
      refine Real.le_sqrt_of_sq_le (le_trans (le_of_eq ?_) hlow)
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    have := inv_anti₀ (Real.exp_pos _) h3
    rwa [Real.exp_neg, inv_inv] at this
  refine (pow_le_pow_left₀ (inv_nonneg.2 (Real.sqrt_nonneg _)) h1 _).trans_eq ?_
  rw [← Real.exp_nat_mul]
  congr 1
  ring

/-- **Eq. (3.33):** if `M ≤ 10 N`, then `𝔼 exp (B^* / 4) ≤ exp (4 N)` over the standard Gaussian
disorder. -/
theorem integral_exp_shcherbinaTirozzi_radius_div_four_le (hM : M ≤ 10 * N) :
    Integrable (fun d : (Fin M → Fin N → ℝ) × (Fin N → ℝ) =>
        Real.exp ((N + Real.sqrt (∑ k, ∑ i, d.1 k i ^ 2) + ∑ i, d.2 i ^ 2) / 4))
        ((Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin N => gaussianReal 0 1).prod
          (Measure.pi fun _ : Fin N => gaussianReal 0 1)) ∧
      ∫ d : (Fin M → Fin N → ℝ) × (Fin N → ℝ),
          Real.exp ((N + Real.sqrt (∑ k, ∑ i, d.1 k i ^ 2) + ∑ i, d.2 i ^ 2) / 4)
          ∂((Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin N => gaussianReal 0 1).prod
            (Measure.pi fun _ : Fin N => gaussianReal 0 1)) ≤ Real.exp (4 * N) := by
  set P₁ := Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin N => gaussianReal 0 1 with hP₁
  set P₀ := Measure.pi fun _ : Fin N => gaussianReal 0 1 with hP₀
  rcases Nat.eq_zero_or_pos N with hN | hN
  · have hM0 : M = 0 := by omega
    subst hN hM0
    simp
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  set t : ℝ := 1 / (8 * N) with ht
  have ht0 : 0 ≤ t := by positivity
  have ht4 : t ≤ 1 / 4 := by
    rw [ht, div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  -- the matrix part
  have hrow := integrable_exp_mul_sum_sq_pi_gaussianReal_and_le (ι := Fin N) ht0 ht4
  have e1 : ∀ g : Fin M → Fin N → ℝ, Real.exp (t * ∑ k, ∑ i, g k i ^ 2) =
      ∏ k, Real.exp (t * ∑ i, g k i ^ 2) := fun g => by rw [Finset.mul_sum, Real.exp_sum]
  have hmat : Integrable (fun g : Fin M → Fin N → ℝ => Real.exp (t * ∑ k, ∑ i, g k i ^ 2)) P₁ := by
    simp_rw [e1]
    exact Integrable.fintype_prod (f := fun _ : Fin M => fun x : Fin N → ℝ =>
      Real.exp (t * ∑ i, x i ^ 2)) fun _ => hrow.1
  have hmatI : ∫ g, Real.exp (t * ∑ k, ∑ i, g k i ^ 2) ∂P₁ ≤ Real.exp (2 * t * N * M) := by
    simp_rw [e1]
    rw [hP₁, integral_fintype_prod_eq_prod (fun _ : Fin M => fun x : Fin N → ℝ =>
      Real.exp (t * ∑ i, x i ^ 2)), Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    refine (pow_le_pow_left₀ (integral_nonneg fun _ => (Real.exp_pos _).le) hrow.2 M).trans_eq ?_
    rw [← Real.exp_nat_mul, Fintype.card_fin]
    congr 1
    ring
  have hfld := integrable_exp_mul_sum_sq_pi_gaussianReal_and_le (ι := Fin N) (t := 1 / 4)
    (by norm_num) le_rfl
  have hpt : ∀ d : (Fin M → Fin N → ℝ) × (Fin N → ℝ),
      Real.exp ((N + Real.sqrt (∑ k, ∑ i, d.1 k i ^ 2) + ∑ i, d.2 i ^ 2) / 4) ≤
        Real.exp (3 * N / 8) * (Real.exp (t * ∑ k, ∑ i, d.1 k i ^ 2) *
          Real.exp (1 / 4 * ∑ i, d.2 i ^ 2)) := fun d => by
    rw [← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
    set S : ℝ := ∑ k, ∑ i, d.1 k i ^ 2 with hS
    have hS0 : 0 ≤ S := Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun i _ => sq_nonneg _
    have hsq : Real.sqrt S / 4 ≤ t * S + N / 8 := by
      have h1 : 2 * Real.sqrt S * N ≤ S + N ^ 2 := by
        nlinarith [sq_nonneg (Real.sqrt S - N), Real.sq_sqrt hS0]
      have h2 : t * S + N / 8 = (S + N ^ 2) / (8 * N) := by
        rw [ht]; field_simp
      rw [h2, div_le_div_iff₀ (by norm_num) (by positivity)]
      nlinarith
    linarith
  have hdom : Integrable (fun d : (Fin M → Fin N → ℝ) × (Fin N → ℝ) =>
      Real.exp (3 * N / 8) * (Real.exp (t * ∑ k, ∑ i, d.1 k i ^ 2) *
        Real.exp (1 / 4 * ∑ i, d.2 i ^ 2))) (P₁.prod P₀) :=
    (hmat.mul_prod hfld.1).const_mul _
  have hint : Integrable (fun d : (Fin M → Fin N → ℝ) × (Fin N → ℝ) =>
      Real.exp ((N + Real.sqrt (∑ k, ∑ i, d.1 k i ^ 2) + ∑ i, d.2 i ^ 2) / 4)) (P₁.prod P₀) :=
    Integrable.mono' hdom (by fun_prop : Measurable fun d : (Fin M → Fin N → ℝ) × (Fin N → ℝ) =>
      Real.exp ((N + Real.sqrt (∑ k, ∑ i, d.1 k i ^ 2) + ∑ i, d.2 i ^ 2) / 4)).aestronglyMeasurable
      (ae_of_all _ fun d => by
        rw [Real.norm_of_nonneg (Real.exp_pos _).le]
        exact hpt d)
  refine ⟨hint, (integral_mono hint hdom hpt).trans ?_⟩
  rw [integral_const_mul, integral_prod_mul
    (fun g : Fin M → Fin N → ℝ => Real.exp (t * ∑ k, ∑ i, g k i ^ 2))
    (fun x : Fin N → ℝ => Real.exp (1 / 4 * ∑ i, x i ^ 2))]
  refine (mul_le_mul_of_nonneg_left (mul_le_mul hmatI hfld.2
    (integral_nonneg fun _ => (Real.exp_pos _).le) (Real.exp_pos _).le)
    (Real.exp_pos _).le).trans ?_
  rw [← Real.exp_add, ← Real.exp_add, Real.exp_le_exp, Fintype.card_fin]
  have h1 : 2 * t * N * M = M / 4 := by
    rw [ht]; field_simp; ring
  have hMN : (M : ℝ) ≤ 10 * N := by exact_mod_cast hM
  rw [h1]
  linarith

/-- **Lemma 3.1.10:** if `M ≤ 10 N` and `k ≤ N`, then `𝔼 (B^*)^k ≤ (40 N)^k` over the standard
Gaussian disorder. -/
theorem integral_shcherbinaTirozzi_radius_pow_le (hM : M ≤ 10 * N) {k : ℕ} (hk : k ≤ N) :
    Integrable (fun d : (Fin M → Fin N → ℝ) × (Fin N → ℝ) =>
        (N + Real.sqrt (∑ k, ∑ i, d.1 k i ^ 2) + ∑ i, d.2 i ^ 2) ^ k)
        ((Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin N => gaussianReal 0 1).prod
          (Measure.pi fun _ : Fin N => gaussianReal 0 1)) ∧
      ∫ d : (Fin M → Fin N → ℝ) × (Fin N → ℝ),
          (N + Real.sqrt (∑ k, ∑ i, d.1 k i ^ 2) + ∑ i, d.2 i ^ 2) ^ k
          ∂((Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin N => gaussianReal 0 1).prod
            (Measure.pi fun _ : Fin N => gaussianReal 0 1)) ≤ (40 * N) ^ k := by
  set P := (Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin N => gaussianReal 0 1).prod
    (Measure.pi fun _ : Fin N => gaussianReal 0 1) with hP
  have h333 := integral_exp_shcherbinaTirozzi_radius_div_four_le (N := N) (M := M) hM
  rw [← hP] at h333
  set B : (Fin M → Fin N → ℝ) × (Fin N → ℝ) → ℝ := fun d =>
    N + Real.sqrt (∑ k, ∑ i, d.1 k i ^ 2) + ∑ i, d.2 i ^ 2 with hB
  have hX0 : 0 ≤ᵐ[P] fun d => B d / 4 := ae_of_all _ fun d => by
    have h2 : 0 ≤ ∑ i, d.2 i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    exact div_nonneg (add_nonneg (by positivity) h2) (by norm_num)
  have hmom := integral_pow_le_of_integral_exp_le hX0 h333.1 h333.2 k
  rcases eq_or_ne k 0 with rfl | hk0
  · simp [hP]
  have e : ∀ d, B d ^ k = 4 ^ k * (B d / 4) ^ k := fun d => by
    rw [← mul_pow, mul_div_cancel₀ _ (by norm_num : (4 : ℝ) ≠ 0)]
  change Integrable (fun d => B d ^ k) P ∧ ∫ d, B d ^ k ∂P ≤ (40 * N) ^ k
  simp_rw [e]
  refine ⟨hmom.1.const_mul _, ?_⟩
  rw [integral_const_mul]
  refine (mul_le_mul_of_nonneg_left hmom.2 (by positivity)).trans ?_
  have h1 : (k : ℝ) ^ k ≤ (N : ℝ) ^ k :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hk) k
  have h2 : (k : ℝ) ^ k + (4 * N) ^ k ≤ (5 * N) ^ k := by
    refine (add_le_add h1 le_rfl).trans ?_
    refine (pow_add_pow_le (Nat.cast_nonneg N) (by positivity) hk0).trans_eq ?_
    ring
  calc (4 : ℝ) ^ k * (2 ^ k * ((k : ℝ) ^ k + (4 * N) ^ k))
      ≤ 4 ^ k * (2 ^ k * (5 * N) ^ k) := by gcongr
    _ = (40 * N) ^ k := by rw [← mul_pow, ← mul_pow]; ring

end SpinGlasses
