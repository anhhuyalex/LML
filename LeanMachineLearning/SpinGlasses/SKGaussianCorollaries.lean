/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.SKGaussianFluctuation
public import LeanMachineLearning.ForMathlib.Analysis.RatioBound
public import LeanMachineLearning.ForMathlib.Probability.Moments.GaussianPiExp
public import LeanMachineLearning.ForMathlib.Probability.Moments.GaussianStein

/-!
# Corollaries of the General Gaussian Fluctuation Bound

This file contains Corollaries 1.7.13 and 1.7.15 of Talagrand's *Spin Glasses:
A Challenge for Mathematicians*, Vol. I, Section 1.7.
-/

namespace SpinGlasses

public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ContDiff

theorem hasDerivAt_exp_mul (c x : ℝ) :
    HasDerivAt (fun y => Real.exp (c * y)) (c * Real.exp (c * x)) x := by
  have h := ((hasDerivAt_id' x).const_mul c).exp
  convert h using 1
  ring

theorem iterate_deriv_exp (c : ℝ) (j : ℕ) (x : ℝ) :
    deriv^[j] (fun y => Real.exp (c * y)) x = c ^ j * Real.exp (c * x) := by
  induction j generalizing x with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    have h_eq : deriv^[j] (fun y => Real.exp (c * y)) = fun y => c ^ j * Real.exp (c * y) := by
      ext y; exact ih y
    rw [h_eq]
    have h1 := (hasDerivAt_exp_mul c x).const_mul (c ^ j)
    have h : HasDerivAt (fun y => c ^ j * Real.exp (c * y)) (c ^ (j + 1) * Real.exp (c * x)) x := by
      convert h1 using 1
      ring
    exact h.deriv

/-- The exponential function `x ↦ exp(c * x)` is exponentially tame. -/
theorem expTame_exp (c : ℝ) : ExpTame (fun x => Real.exp (c * x)) where
  contDiff := Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)
  bound j := by
    refine ⟨|c| ^ j, |c|, by positivity, by positivity, fun x => ?_⟩
    rw [iterate_deriv_exp]
    rw [abs_mul, abs_pow, Real.abs_exp]
    have h_le : c * x ≤ |c| * |x| := by
      calc c * x ≤ |c * x| := le_abs_self _
        _ = |c| * |x| := abs_mul c x
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp_of_le h_le) (by positivity)

theorem iterate_deriv_id_mul_exp (c : ℝ) (j : ℕ) (x : ℝ) :
    deriv^[j] (fun y => y * Real.exp (c * y)) x =
      ((j : ℝ) * c ^ (j - 1) + c ^ j * x) * Real.exp (c * x) := by
  induction j generalizing x with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    have h_eq : deriv^[j] (fun y => y * Real.exp (c * y)) =
        fun y => ((j : ℝ) * c ^ (j - 1) + c ^ j * y) * Real.exp (c * y) := by
      ext y; exact ih y
    rw [h_eq]
    have h1 : HasDerivAt (fun y => (j : ℝ) * c ^ (j - 1) + c ^ j * y) (c ^ j) x := by
      have h_lin := (hasDerivAt_id' x).const_mul (c ^ j)
      have h_add := h_lin.const_add ((j : ℝ) * c ^ (j - 1))
      convert h_add using 1
      ring
    have h2 := hasDerivAt_exp_mul c x
    have h := h1.mul h2
    change HasDerivAt (fun y => ((j : ℝ) * c ^ (j - 1) + c ^ j * y) * Real.exp (c * y)) _ x at h
    rw [h.deriv]
    simp only [Nat.succ_sub_one]
    cases j with
    | zero =>
      simp only [Nat.zero_sub, pow_zero, CharP.cast_eq_zero, zero_mul, zero_add,
        one_mul, pow_one]
      ring
    | succ m =>
      simp only [Nat.succ_sub_one]
      have h1 : c ^ (m + 1) = c ^ m * c := pow_succ c m
      have h2 : c ^ (m + 1 + 1) = (c ^ m * c) * c := by
        rw [pow_succ c (m + 1), pow_succ c m]
      have h3 : (↑(m + 1 + 1) : ℝ) = (m : ℝ) + 2 := by push_cast; ring
      have h4 : (↑(m + 1) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
      rw [h1, h2, h3, h4]
      ring

/-- The function `x ↦ x * exp(c * x)` is exponentially tame. -/
theorem expTame_id_mul_exp (c : ℝ) : ExpTame (fun x => x * Real.exp (c * x)) where
  contDiff := contDiff_id.mul (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id))
  bound j := by
    refine ⟨2 * ((j : ℝ) * |c| ^ (j - 1) + |c| ^ j), |c| + 1,
      by positivity, by positivity, fun x => ?_⟩
    rw [iterate_deriv_id_mul_exp]
    rw [abs_mul, Real.abs_exp]
    have h_le1 : |(j : ℝ) * c ^ (j - 1) + c ^ j * x| ≤ (j : ℝ) * |c| ^ (j - 1) + |c| ^ j * |x| := by
      calc |(j : ℝ) * c ^ (j - 1) + c ^ j * x|
        _ ≤ |(j : ℝ) * c ^ (j - 1)| + |c ^ j * x| := abs_add_le _ _
        _ = (j : ℝ) * |c| ^ (j - 1) + |c| ^ j * |x| := by
          simp only [abs_mul, abs_pow]
          rw [abs_of_nonneg (by positivity)]
    have h_x_le : |x| ≤ Real.exp |x| := by
      linarith [Real.add_one_le_exp |x|, abs_nonneg x]
    have h_one_le : (1 : ℝ) ≤ Real.exp |x| := by
      have := Real.exp_le_exp_of_le (abs_nonneg x)
      rwa [Real.exp_zero] at this
    have h_poly : (j : ℝ) * |c| ^ (j - 1) + |c| ^ j * |x| ≤
        2 * ((j : ℝ) * |c| ^ (j - 1) + |c| ^ j) * Real.exp |x| := by
      calc (j : ℝ) * |c| ^ (j - 1) + |c| ^ j * |x|
        _ ≤ (j : ℝ) * |c| ^ (j - 1) * Real.exp |x| + |c| ^ j * Real.exp |x| := by
          have h1 : (j : ℝ) * |c| ^ (j - 1) ≤ (j : ℝ) * |c| ^ (j - 1) * Real.exp |x| := by
            calc (j : ℝ) * |c| ^ (j - 1) = (j : ℝ) * |c| ^ (j - 1) * 1 := by ring
              _ ≤ (j : ℝ) * |c| ^ (j - 1) * Real.exp |x| :=
                mul_le_mul_of_nonneg_left h_one_le (by positivity)
          have h2 : |c| ^ j * |x| ≤ |c| ^ j * Real.exp |x| :=
            mul_le_mul_of_nonneg_left h_x_le (by positivity)
          linarith
        _ = ((j : ℝ) * |c| ^ (j - 1) + |c| ^ j) * Real.exp |x| := by ring
        _ ≤ ((j : ℝ) * |c| ^ (j - 1) + |c| ^ j) * Real.exp |x| +
            ((j : ℝ) * |c| ^ (j - 1) + |c| ^ j) * Real.exp |x| :=
          le_add_of_nonneg_right (by positivity)
        _ = 2 * ((j : ℝ) * |c| ^ (j - 1) + |c| ^ j) * Real.exp |x| := by ring
    have h_exp : Real.exp (c * x) ≤ Real.exp (|c| * |x|) := by
      have : c * x ≤ |c| * |x| := (le_abs_self _).trans_eq (abs_mul c x)
      exact Real.exp_le_exp_of_le this
    have h_prod : Real.exp |x| * Real.exp (|c| * |x|) = Real.exp ((|c| + 1) * |x|) := by
      rw [← Real.exp_add]
      ring_nf
    calc |(j : ℝ) * c ^ (j - 1) + c ^ j * x| * Real.exp (c * x)
      _ ≤ ((j : ℝ) * |c| ^ (j - 1) + |c| ^ j * |x|) * Real.exp (|c| * |x|) :=
        mul_le_mul h_le1 h_exp (by positivity) (by positivity)
      _ ≤ (2 * ((j : ℝ) * |c| ^ (j - 1) + |c| ^ j) * Real.exp |x|) * Real.exp (|c| * |x|) :=
        mul_le_mul_of_nonneg_right h_poly (by positivity)
      _ = 2 * ((j : ℝ) * |c| ^ (j - 1) + |c| ^ j) * (Real.exp |x| * Real.exp (|c| * |x|)) := by ring
      _ = 2 * ((j : ℝ) * |c| ^ (j - 1) + |c| ^ j) * Real.exp ((|c| + 1) * |x|) := by rw [h_prod]

theorem integral_exp_scaled_gaussianReal_zero_one (c v : ℝ) :
    ∫ t, Real.exp (c * (v * t)) ∂(gaussianReal 0 1) = Real.exp (c ^ 2 * v ^ 2 / 2) := by
  have heq : (fun t => Real.exp (c * (v * t))) = fun t => Real.exp ((c * v) * t) := by
    ext t; ring_nf
  rw [heq, integral_exp_mul_gaussianReal_zero_one]
  ring_nf

theorem integral_id_mul_exp_scaled_gaussianReal_zero_one (c v : ℝ) :
    ∫ t, (v * t) * Real.exp (c * (v * t)) ∂(gaussianReal 0 1) =
      c * v ^ 2 * Real.exp (c ^ 2 * v ^ 2 / 2) := by
  have heq : (fun t => (v * t) * Real.exp (c * (v * t))) =
      fun t => v * (t * Real.exp ((c * v) * t)) := by
    ext t; ring_nf
  rw [heq, integral_const_mul]
  have hF : ∀ x,
      HasDerivAt (fun y => Real.exp ((c * v) * y)) ((c * v) * Real.exp ((c * v) * x)) x :=
    fun x => hasDerivAt_exp_mul (c * v) x
  have hxF : Integrable (fun x => x * Real.exp ((c * v) * x)) (gaussianReal 0 1) := by
    have h := (expTame_id_mul_exp (c * v)).integrable_comp_mul_gaussianReal 1
    simpa using h
  have hF' : Integrable (fun x => (c * v) * Real.exp ((c * v) * x)) (gaussianReal 0 1) := by
    have h := (expTame_exp (c * v)).integrable_comp_mul_gaussianReal 1
    simpa using h.const_mul (c * v)
  have h_ibp := integral_id_mul_gaussianReal_eq (v := 1) hF hxF hF'
  simp only [NNReal.coe_one, one_mul] at h_ibp
  rw [h_ibp, integral_const_mul, integral_exp_mul_gaussianReal_zero_one]
  ring_nf

theorem mul_le_half_mul_add_inv_mul {t a b : ℝ} (ht : 0 < t) :
    a * b ≤ (t * a ^ 2 + t⁻¹ * b ^ 2) / 2 := by
  have hsq : 0 ≤ (t * a - b) ^ 2 := sq_nonneg _
  have ht2 : 0 < 2 * t := by linarith
  have : 0 ≤ (t * a - b) ^ 2 / (2 * t) := div_nonneg hsq ht2.le
  calc a * b = (t * a ^ 2 + t⁻¹ * b ^ 2) / 2 - (t * a - b) ^ 2 / (2 * t) := by
        field_simp; ring
    _ ≤ (t * a ^ 2 + t⁻¹ * b ^ 2) / 2 := by linarith

theorem dotProduct_ising_split (N : ℕ) (β ε : ℝ) (y : Fin N → ℝ)
    (a : Fin N → ℤˣ) (m : Fin N → ℝ) :
    ε * β * ((fun i => (Real.sqrt N)⁻¹ * (((a i : ℤ) : ℝ) - m i)) ⬝ᵥ y) +
      ((fun i => (Real.sqrt N)⁻¹ * (ε * β * m i)) ⬝ᵥ y) =
    (fun i => (Real.sqrt N)⁻¹ * (ε * β * ((a i : ℤ) : ℝ))) ⬝ᵥ y := by
  simp only [dotProduct]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => by ring

theorem exp_dotProduct_ising_split (N : ℕ) (β ε : ℝ) (y : Fin N → ℝ)
    (a : Fin N → ℤˣ) (m : Fin N → ℝ) :
    Real.exp (ε * β * ((fun i => (Real.sqrt N)⁻¹ * (((a i : ℤ) : ℝ) - m i)) ⬝ᵥ y)) *
      Real.exp (((fun i => (Real.sqrt N)⁻¹ * (ε * β * m i)) ⬝ᵥ y)) =
    Real.exp ((fun i => (Real.sqrt N)⁻¹ * (ε * β * ((a i : ℤ) : ℝ))) ⬝ᵥ y) := by
  rw [← Real.exp_add, dotProduct_ising_split]

theorem id_mul_exp_dotProduct_ising_split (N : ℕ) (β ε : ℝ) (y : Fin N → ℝ)
    (a : Fin N → ℤˣ) (m : Fin N → ℝ) :
    (((fun i => (Real.sqrt N)⁻¹ * (((a i : ℤ) : ℝ) - m i)) ⬝ᵥ y) *
      Real.exp (ε * β * ((fun i => (Real.sqrt N)⁻¹ * (((a i : ℤ) : ℝ) - m i)) ⬝ᵥ y))) *
      Real.exp (((fun i => (Real.sqrt N)⁻¹ * (ε * β * m i)) ⬝ᵥ y)) =
    ((fun i => (Real.sqrt N)⁻¹ * (((a i : ℤ) : ℝ) - m i)) ⬝ᵥ y) *
      Real.exp ((fun i => (Real.sqrt N)⁻¹ * (ε * β * ((a i : ℤ) : ℝ))) ⬝ᵥ y) := by
  rw [mul_assoc, ← Real.exp_add, dotProduct_ising_split]

theorem integral_exp_sum_ising_moment_le {N : ℕ} (hN : 0 < N) (c : ℝ)
    (m : Fin N → ℝ) (hm : ∀ i, |m i| ≤ 1) :
    ∫ y : Fin N → ℝ, Real.exp (c * ((fun i => (Real.sqrt N)⁻¹ * m i) ⬝ᵥ y))
      ∂(Measure.pi fun _ : Fin N => gaussianReal 0 1) ≤
    Real.exp (c ^ 2 / 2) := by
  have heq : (fun y : Fin N → ℝ =>
      Real.exp (c * ((fun i => (Real.sqrt N)⁻¹ * m i) ⬝ᵥ y))) =
      fun y => Real.exp (∑ i : Fin N, (c * (Real.sqrt N)⁻¹ * m i) * y i) := by
    ext y
    simp only [dotProduct]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => by ring
  rw [heq, integral_exp_sum_mul_gaussianReal]
  have h_sq_le (i : Fin N) : (c * (Real.sqrt N)⁻¹ * m i) ^ 2 ≤ c ^ 2 / (N : ℝ) := by
    have hN_pos : (0 : ℝ) < N := Nat.cast_pos.mpr hN
    have hsqrt_sq : (Real.sqrt N) ^ 2 = (N : ℝ) := Real.sq_sqrt hN_pos.le
    have hm_sq : (m i) ^ 2 ≤ 1 := by
      calc (m i) ^ 2 = |m i| ^ 2 := (sq_abs (m i)).symm
        _ ≤ 1 ^ 2 := by nlinarith [hm i, abs_nonneg (m i)]
        _ = 1 := by norm_num
    calc (c * (Real.sqrt N)⁻¹ * m i) ^ 2
      _ = c ^ 2 * ((Real.sqrt N)⁻¹ ^ 2) * (m i) ^ 2 := by ring
      _ = c ^ 2 * ((Real.sqrt N) ^ 2)⁻¹ * (m i) ^ 2 := by rw [inv_pow]
      _ = (c ^ 2 / (N : ℝ)) * (m i) ^ 2 := by rw [hsqrt_sq]; ring
      _ ≤ (c ^ 2 / (N : ℝ)) * 1 := mul_le_mul_of_nonneg_left hm_sq (by positivity)
      _ = c ^ 2 / (N : ℝ) := mul_one _
  have h_sum_le : ∑ i : Fin N, (c * (Real.sqrt N)⁻¹ * m i) ^ 2 / 2 ≤ c ^ 2 / 2 := by
    have hN_pos : (0 : ℝ) < N := Nat.cast_pos.mpr hN
    calc ∑ i : Fin N, (c * (Real.sqrt N)⁻¹ * m i) ^ 2 / 2
      _ ≤ ∑ i : Fin N, (c ^ 2 / (N : ℝ)) / 2 :=
        Finset.sum_le_sum fun i _ => div_le_div_of_nonneg_right (h_sq_le i) (by positivity)
      _ = (N : ℝ) * ((c ^ 2 / (N : ℝ)) / 2) := by simp [Finset.sum_const]
      _ = c ^ 2 / 2 := by
        field_simp
  exact Real.exp_le_exp_of_le h_sum_le

theorem abs_integral_units_cast_le {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] (f : α → ℤˣ) :
    |∫ x, ((f x : ℤ) : ℝ) ∂μ| ≤ 1 := by
  refine abs_integral_le_integral_abs.trans ?_
  have h_eq : ∀ x, |((f x : ℤ) : ℝ)| = 1 := fun x => by
    obtain (h | h) := Int.units_eq_one_or (f x) <;> { simp [h] }
  simp_rw [h_eq]
  rw [integral_const]
  simp only [Measure.real, measure_univ, ENNReal.toReal_one, one_smul, le_refl]

theorem integral_le_add_of_le {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {f g₁ g₂ : α → ℝ} (hf : ∀ x, 0 ≤ f x) (h_le : ∀ x, f x ≤ g₁ x + g₂ x)
    (hg₁ : Integrable g₁ μ) (hg₂ : Integrable g₂ μ) :
    ∫ x, f x ∂μ ≤ ∫ x, g₁ x ∂μ + ∫ x, g₂ x ∂μ := by
  have h_int : Integrable (fun x => g₁ x + g₂ x) μ := hg₁.add hg₂
  have h_mono := integral_mono_of_nonneg (ae_of_all _ hf) h_int (ae_of_all _ h_le)
  rw [integral_add hg₁ hg₂] at h_mono
  exact h_mono

theorem double_integral_mono_of_nonneg {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β)
    {f g : α → β → ℝ} (hf : ∀ x y, 0 ≤ f x y) (h_le : ∀ x y, f x y ≤ g x y)
    (h_int_inner : ∀ x, Integrable (g x) ν)
    (h_int_outer : Integrable (fun x => ∫ y, g x y ∂ν) μ) :
    ∫ x, ∫ y, f x y ∂ν ∂μ ≤ ∫ x, ∫ y, g x y ∂ν ∂μ := by
  have h_inner : ∀ x, ∫ y, f x y ∂ν ≤ ∫ y, g x y ∂ν := fun x =>
    integral_mono_of_nonneg (ae_of_all _ (hf x)) (h_int_inner x) (ae_of_all _ (h_le x))
  have h_inner_nonneg : ∀ x, 0 ≤ ∫ y, f x y ∂ν := fun x =>
    integral_nonneg (hf x)
  exact integral_mono_of_nonneg (ae_of_all _ h_inner_nonneg) h_int_outer (ae_of_all _ h_inner)

theorem double_integral_le_add_of_le {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β)
    {f g₁ g₂ : α → β → ℝ} (hf : ∀ x y, 0 ≤ f x y) (h_le : ∀ x y, f x y ≤ g₁ x y + g₂ x y)
    (hg₁ : ∀ x, Integrable (g₁ x) ν) (hg₂ : ∀ x, Integrable (g₂ x) ν)
    (hG₁ : Integrable (fun x => ∫ y, g₁ x y ∂ν) μ)
    (hG₂ : Integrable (fun x => ∫ y, g₂ x y ∂ν) μ) :
    ∫ x, ∫ y, f x y ∂ν ∂μ ≤ ∫ x, ∫ y, g₁ x y ∂ν ∂μ + ∫ x, ∫ y, g₂ x y ∂ν ∂μ := by
  have h_inner : ∀ x, ∫ y, f x y ∂ν ≤ (∫ y, g₁ x y ∂ν) + (∫ y, g₂ x y ∂ν) := fun x =>
    integral_le_add_of_le ν (hf x) (h_le x) (hg₁ x) (hg₂ x)
  have h_inner_nonneg : ∀ x, 0 ≤ ∫ y, f x y ∂ν := fun x =>
    integral_nonneg (hf x)
  exact integral_le_add_of_le μ h_inner_nonneg h_inner hG₁ hG₂

theorem integrable_exp_dotProduct_gaussianReal {N : ℕ} (u : Fin N → ℝ) :
    Integrable (fun y : Fin N → ℝ => Real.exp (u ⬝ᵥ y))
      (Measure.pi fun _ : Fin N => gaussianReal 0 1) := by
  have heq : (fun y : Fin N → ℝ => Real.exp (u ⬝ᵥ y)) =
      fun y => Real.exp (∑ i, u i * y i) := by
    ext y; congr 1; simp [dotProduct]
  rw [heq]
  exact integrable_exp_sum_mul_gaussianReal u

/-- **Talagrand Corollary 1.7.13, Eq. (1.206): Exponential observable.** -/
theorem sk_gaussian_fluctuation_exp (β h q : ℝ)
    (hfix : ∫ x : ℝ, Real.tanh (β * Real.sqrt q * x + h) ^ 2 ∂(gaussianReal 0 1) = q)
    (hβ : 4 * β ^ 2 < 1) (ε : ℝ) (hε : ε ^ 2 = 1) {k : ℕ} (hk : 1 ≤ k) :
    ∃ K : ℝ, 0 < K ∧ ∀ N : ℕ, 0 < N →
      ∫ g : FinPairs N → ℝ, ∫ y : Fin N → ℝ,
        ((∫ a, Real.exp ((fun i => (Real.sqrt N)⁻¹ * (ε * β * ((a i : ℤ) : ℝ))) ⬝ᵥ y)
            ∂(Measure.count.tilted (skGibbsEnergy N β h g))) -
          Real.exp (β ^ 2 * (1 - q) / 2) *
            Real.exp ((fun i => (Real.sqrt N)⁻¹ *
              (ε * β * ∫ b, ((b i : ℤ) : ℝ)
                ∂(Measure.count.tilted (skGibbsEnergy N β h g)))) ⬝ᵥ y)) ^ (2 * k)
          ∂(Measure.pi fun _ : Fin N => gaussianReal 0 1)
        ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1) ≤ K / (N : ℝ) ^ k := by
  have hq := fixedPoint_mem_Icc hfix
  set v : ℝ := Real.sqrt (1 - q) with hvdef
  have hv : v ^ 2 = 1 - q := Real.sq_sqrt (by linarith [hq.2])
  set c₀ : ℝ := Real.exp (β ^ 2 * (1 - q) / 2) with hc₀
  have h_gauss : ∫ t, Real.exp (ε * β * (v * t)) ∂(gaussianReal 0 1) = c₀ := by
    rw [integral_exp_scaled_gaussianReal_zero_one]
    congr 1
    calc (ε * β) ^ 2 * v ^ 2 / 2
      _ = (ε ^ 2 * β ^ 2) * (1 - q) / 2 := by rw [hv]; ring
      _ = β ^ 2 * (1 - q) / 2 := by rw [hε, one_mul]
  have hU : ExpTame (fun x => Real.exp (ε * β * x)) := expTame_exp (ε * β)
  have hV : ExpTame (fun x => Real.exp (ε * β * x) - c₀) := hU.sub_const c₀
  have hV0 : ∫ t, (fun x => Real.exp (ε * β * x) - c₀) (v * t) ∂(gaussianReal 0 1) = 0 := by
    have h1 := hU.integral_sub_const_mul_gaussianReal v
    rw [← h_gauss]
    exact h1
  obtain ⟨C, hC0, hCb⟩ := hV.gibbs_fluctuation_abs_le (m := 4 * k) (by omega) v
    (by nlinarith [hq.1, hq.2]) hV0
  obtain ⟨K', hK'0, hK'⟩ := sk_overlap_moment_le_of_exp β h q hfix hβ (2 * k)
  set C₂ : ℝ := C * (((4 * k) * (4 * k) : ℝ) ^ (4 * k) * ((4 * k : ℝ) * 4 ^ (4 * k))) with hC₂
  have hC₂0 : 0 ≤ C₂ := by positivity
  set M : ℝ := Real.exp (8 * (k : ℝ) ^ 2 * β ^ 2) with hM
  have hM0 : 0 < M := Real.exp_pos _
  refine ⟨(C₂ * K' + M) / 2 + 1, by positivity, fun N hN => ?_⟩
  have hNk : (0 : ℝ) < (N : ℝ) ^ k := by positivity
  set ξ : Fin N → (Fin N → ℤˣ) → ℝ := fun i a => ((a i : ℤ) : ℝ) with hξ
  have hξ_abs : ∀ i a, |ξ i a| ≤ 1 := fun i a => isingObs_abs_le N i a
  have hξ_sq : ∀ i a, ξ i a ^ 2 = 1 := fun i a => isingObs_sq N i a
  set P : Measure (FinPairs N → ℝ) := Measure.pi fun _ : FinPairs N => gaussianReal 0 1 with hP
  set Q : Measure (Fin N → ℝ) := Measure.pi fun _ : Fin N => gaussianReal 0 1 with hQ
  set J : (FinPairs N → ℝ) → ℝ := fun g =>
    overlapMoment ξ (skGibbsEnergy N β h g) q (2 * k) with hJ
  have hJint : Integrable J P := by
    refine integrable_integral_pi_count_tilted_det (R := Fin 2)
      (g := fun a g => skGibbsEnergy N β h g a) (fun a => ?_)
      (fun τ => (overlapGibbs ξ (τ 0) (τ 1) - q) ^ (4 * k))
    unfold skGibbsEnergy
    exact (by fun_prop : Measurable _).aemeasurable
  have hJmom : ∫ g, J g ∂P ≤ K' / ((N : ℝ) ^ k) ^ 2 := by
    have h1 := hK' N hN
    have h2 : ((N : ℝ) ^ (2 * k)) = ((N : ℝ) ^ k) ^ 2 := by
      rw [← pow_mul]; congr 1; ring
    rwa [h2] at h1
  have hpt : ∀ g : FinPairs N → ℝ, ∫ y : Fin N → ℝ,
      ((∫ a, Real.exp ((fun i => (Real.sqrt N)⁻¹ * (ε * β * ((a i : ℤ) : ℝ))) ⬝ᵥ y)
          ∂(Measure.count.tilted (skGibbsEnergy N β h g))) -
        c₀ * Real.exp ((fun i => (Real.sqrt N)⁻¹ *
          (ε * β * ∫ b, ((b i : ℤ) : ℝ)
            ∂(Measure.count.tilted (skGibbsEnergy N β h g)))) ⬝ᵥ y)) ^ (2 * k) ∂Q ≤
      (C₂ * (N : ℝ) ^ k * J g + (N : ℝ) ^ (- (k : ℝ)) * M) / 2 := by
    intro g
    set f := skGibbsEnergy N β h g with hf
    set μ := Measure.count.tilted f with hμ
    set m : Fin N → ℝ := fun i => ∫ b, ((b i : ℤ) : ℝ) ∂μ with hm
    have hm_le : ∀ i, |m i| ≤ 1 := fun i => abs_integral_units_cast_le μ _
    set A : (Fin N → ℝ) → ℝ := fun y =>
      (∫ a, Real.exp (ε * β * ((fun i => (Real.sqrt N)⁻¹ * (((a i : ℤ) : ℝ) - m i)) ⬝ᵥ y)) ∂μ) - c₀
    set B : (Fin N → ℝ) → ℝ := fun y =>
      Real.exp ((fun i => (Real.sqrt N)⁻¹ * (ε * β * m i)) ⬝ᵥ y)
    have h_split : ∀ y, ((∫ a, Real.exp ((fun i => (Real.sqrt N)⁻¹ * (ε * β * ((a i : ℤ) : ℝ))) ⬝ᵥ y) ∂μ) -
        c₀ * B y) = A y * B y := fun y => by
      have h1 : ∀ a, Real.exp (ε * β * ((fun i => (Real.sqrt N)⁻¹ * (((a i : ℤ) : ℝ) - m i)) ⬝ᵥ y)) * B y =
          Real.exp ((fun i => (Real.sqrt N)⁻¹ * (ε * β * ((a i : ℤ) : ℝ))) ⬝ᵥ y) :=
        fun a => exp_dotProduct_ising_split N β ε y a m
      have h2 : ∫ a, Real.exp ((fun i => (Real.sqrt N)⁻¹ * (ε * β * ((a i : ℤ) : ℝ))) ⬝ᵥ y) ∂μ =
          (∫ a, Real.exp (ε * β * ((fun i => (Real.sqrt N)⁻¹ * (((a i : ℤ) : ℝ) - m i)) ⬝ᵥ y)) ∂μ) * B y := by
        simp_rw [← h1, integral_mul_const]
      rw [h2, sub_mul]
    have h_le : ∀ y, ((∫ a, Real.exp ((fun i => (Real.sqrt N)⁻¹ * (ε * β * ((a i : ℤ) : ℝ))) ⬝ᵥ y) ∂μ) -
        c₀ * B y) ^ (2 * k) ≤
        ((N : ℝ) ^ k * A y ^ (4 * k) + (N : ℝ) ^ (- (k : ℝ)) * B y ^ (4 * k)) / 2 := fun y => by
      rw [h_split y, mul_pow]
      have h_amgm := mul_le_half_mul_add_inv_mul (t := (N : ℝ) ^ k) hNk (a := A y ^ (2 * k)) (b := B y ^ (2 * k))
      have hA4 : (A y ^ (2 * k)) ^ 2 = A y ^ (4 * k) := by rw [← pow_mul]; congr 1; ring
      have hB4 : (B y ^ (2 * k)) ^ 2 = B y ^ (4 * k) := by rw [← pow_mul]; congr 1; ring
      rw [hA4, hB4] at h_amgm
      have h_inv : ((N : ℝ) ^ k)⁻¹ = (N : ℝ) ^ (- (k : ℝ)) := by
        rw [Real.rpow_neg hNk.le, Real.rpow_natCast]
      rw [h_inv] at h_amgm
      exact h_amgm
    have hA_int : ∫ y, A y ^ (4 * k) ∂Q ≤ C₂ * J g := by
      have hrew : ∀ y : Fin N → ℝ, A y =
          ∫ a, (Real.exp (ε * β * ((fun i => (Real.sqrt N)⁻¹ * (((a i : ℤ) : ℝ) - m i)) ⬝ᵥ y)) - c₀) ∂μ := fun y => by
        rw [integral_sub Integrable.of_finite (integrable_const _)]
        simp
      simp_rw [hrew]
      refine (le_abs_self _).trans ?_
      have h1 := hCb N (Fin N → ℤˣ) ξ hξ_abs f
      exact h1.trans (mul_le_mul_of_nonneg_left
        (sum_integral_abs_pairProd_le ξ hξ_sq hN f q v hv (by omega))
          hC0 |>.trans (le_of_eq (by simp only [hC₂, hJ]; ring)))
    have hB_int : ∫ y, B y ^ (4 * k) ∂Q ≤ M := by
      have heq : (fun y => B y ^ (4 * k)) =
          fun y => Real.exp (4 * (k : ℝ) * (ε * β) * ((fun i => (Real.sqrt N)⁻¹ * m i) ⬝ᵥ y)) := by
        ext y
        simp only [B]
        rw [← Real.exp_nat_mul]
        congr 1
        simp only [dotProduct]
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => by ring
      rw [heq]
      have h_mom := integral_exp_sum_ising_moment_le hN (4 * (k : ℝ) * (ε * β)) m hm_le
      have h_pow : (4 * (k : ℝ) * (ε * β)) ^ 2 / 2 = 8 * (k : ℝ) ^ 2 * β ^ 2 := by
        calc (4 * (k : ℝ) * (ε * β)) ^ 2 / 2
          _ = (16 * (k : ℝ) ^ 2 * (ε ^ 2 * β ^ 2)) / 2 := by ring
          _ = (16 * (k : ℝ) ^ 2 * β ^ 2) / 2 := by rw [hε, one_mul]
          _ = 8 * (k : ℝ) ^ 2 * β ^ 2 := by ring
      rwa [h_pow] at h_mom
    have hg₂ : Integrable (fun y => (N : ℝ) ^ (- (k : ℝ)) * B y ^ (4 * k)) Q := by
      have heq : (fun y => B y ^ (4 * k)) =
          fun y => Real.exp (((fun i => 4 * (k : ℝ) * ((Real.sqrt N)⁻¹ * (ε * β * m i)))) ⬝ᵥ y) := by
        ext y
        simp only [B, dotProduct]
        rw [← Real.exp_nat_mul, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => by ring
      rw [heq]
      exact (integrable_exp_dotProduct_gaussianReal _).const_mul _
    -- bound using integral_mono_of_nonneg
    have h_nonneg : ∀ y, 0 ≤ ((∫ a, Real.exp ((fun i => (Real.sqrt N)⁻¹ * (ε * β * ((a i : ℤ) : ℝ))) ⬝ᵥ y) ∂μ) -
        c₀ * B y) ^ (2 * k) := fun y => Even.pow_nonneg ⟨k, by ring⟩ _
    have h_target_nonneg : 0 ≤ (C₂ * (N : ℝ) ^ k * J g + (N : ℝ) ^ (- (k : ℝ)) * M) / 2 := by
      positivity
    sorry

end

end SpinGlasses
