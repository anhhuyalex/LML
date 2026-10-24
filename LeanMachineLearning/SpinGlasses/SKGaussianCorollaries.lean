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

end

end SpinGlasses
