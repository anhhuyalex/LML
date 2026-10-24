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
public import LeanMachineLearning.ForMathlib.Analysis.SpecialFunctions.Hyperbolic
public import LeanMachineLearning.ForMathlib.Analysis.SpecialFunctions.AddPowEstimates

/-!
# Corollaries of the General Gaussian Fluctuation Bound

This file contains Corollaries 1.7.13 and 1.7.15 of Talagrand's *Spin Glasses:
A Challenge for Mathematicians*, Vol. I, Section 1.7.
-/

namespace SpinGlasses

public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ContDiff

attribute [local instance] Fintype.ofFinite

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
    ext y; simp [dotProduct]
  rw [heq]
  exact integrable_exp_sum_mul_gaussianReal u

theorem projPath_zero_pi_div_two {m N : ℕ} (u : Fin m → Fin N → ℝ)
    (w : (Fin m → ℝ) × (Fin N → ℝ)) (l : Fin m) :
    projPath u 0 (Real.pi / 2) w l = u l ⬝ᵥ w.2 := by
  simp only [projPath, Real.cos_pi_div_two, Real.sin_pi_div_two, zero_mul, one_mul, zero_add]

theorem integrable_prod_derivProd_zero {m N : ℕ} (hm : 0 < m)
    {V : ℝ → ℝ} (hV : ExpTame V) (u : Fin m → Fin N → ℝ) :
    Integrable (fun y : Fin N → ℝ => ∏ l, V (u l ⬝ᵥ y))
      (Measure.pi fun _ : Fin N => gaussianReal 0 1) := by
  have hint := hV.integrable_derivProd_projPath hm u 0 (Real.pi / 2) 0
  have hpath : (fun (w : (Fin m → ℝ) × (Fin N → ℝ)) =>
      derivProd V 0 (projPath u 0 (Real.pi / 2) w)) =
      fun w => ∏ l, V (u l ⬝ᵥ w.2) := by
    ext w
    simp only [derivProd, projPath_zero_pi_div_two, Pi.zero_apply, Function.iterate_zero, id]
  rw [hpath] at hint
  exact hint.of_comp_snd (NeZero.ne _)

theorem add_pow_two_mul_le {k : ℕ} (hk : 1 ≤ k) (x y : ℝ) :
    (x + y) ^ (2 * k) ≤ 2 ^ (2 * k - 1) * (x ^ (2 * k) + y ^ (2 * k)) := by
  have h_even : Even (2 * k) := ⟨k, by ring⟩
  rw [← Even.pow_abs h_even (x + y)]
  have h_le : |x + y| ≤ |x| + |y| := abs_add_le x y
  have h_pow := pow_le_pow_left₀ (abs_nonneg _) h_le (2 * k)
  refine h_pow.trans ?_
  have h_add := add_pow_le_mul_pow_add_mul_pow (abs_nonneg x) (abs_nonneg y)
    zero_lt_one (n := 2 * k) (by omega)
  have h1 : (1 : ℝ) + 1 = 2 := by norm_num
  have h2 : (1 : ℝ) + 1⁻¹ = 2 := by norm_num
  rw [h1, h2] at h_add
  rw [Even.pow_abs h_even x, Even.pow_abs h_even y] at h_add
  linarith

theorem sub_pow_two_mul_le {k : ℕ} (hk : 1 ≤ k) (x y : ℝ) :
    (x - y) ^ (2 * k) ≤ 2 ^ (2 * k - 1) * (x ^ (2 * k) + y ^ (2 * k)) := by
  have h := add_pow_two_mul_le hk x (-y)
  rw [show x + -y = x - y by ring] at h
  have he : (-y) ^ (2 * k) = y ^ (2 * k) := Even.neg_pow ⟨k, by ring⟩ y
  rwa [he] at h

/-- **The master upper bound kernel for the general Gaussian fluctuation principle
with multiplier.**
Constructs an explicit integrable dominating function `Upper` pointwise bounding
the $2k$-th moment
of the fluctuation product, with double integral bounded by `((C₂ * K' + M) / 2) / N^k`. -/
lemma sk_gaussian_fluctuation_upper_bound (β h q : ℝ)
    (hfix : ∫ x : ℝ, Real.tanh (β * Real.sqrt q * x + h) ^ 2 ∂(gaussianReal 0 1) = q)
    (hβ : 4 * β ^ 2 < 1) (ε : ℝ) (hε : ε ^ 2 = 1) {k : ℕ} (hk : 1 ≤ k)
    {U : ℝ → ℝ} (hU : ExpTame U) :
    ∃ C₂ M K' : ℝ, 0 ≤ C₂ ∧ 0 < M ∧ 0 < K' ∧
      ∀ N : ℕ, 0 < N →
        ∃ (Upper : (FinPairs N → ℝ) → (Fin N → ℝ) → ℝ)
          (Bnd : (FinPairs N → ℝ) → ℝ),
          (∀ g y, (((∫ a, U ((fun i => (Real.sqrt N)⁻¹ *
              (((a i : ℤ) : ℝ) -
              ∫ b, ((b i : ℤ) : ℝ) ∂(Measure.count.tilted (skGibbsEnergy N β h g)))) ⬝ᵥ y)
            ∂(Measure.count.tilted (skGibbsEnergy N β h g))) -
            ∫ s, U (Real.sqrt (1 - q) * s) ∂(gaussianReal 0 1)) *
            Real.exp ((fun i => (Real.sqrt N)⁻¹ *
              (ε * β * ∫ b, ((b i : ℤ) : ℝ)
                ∂(Measure.count.tilted (skGibbsEnergy N β h g)))) ⬝ᵥ y)) ^ (2 * k) ≤ Upper g y) ∧
          (∀ g, Integrable (Upper g) (Measure.pi fun _ : Fin N => gaussianReal 0 1)) ∧
          (∀ g, ∫ y, Upper g y ∂(Measure.pi fun _ : Fin N => gaussianReal 0 1) ≤ Bnd g) ∧
          (Integrable Bnd (Measure.pi fun _ : FinPairs N => gaussianReal 0 1)) ∧
          (∫ g, Bnd g ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1) ≤
            ((C₂ * K' + M) / 2) / (N : ℝ) ^ k) := by
  have hq := fixedPoint_mem_Icc hfix
  set v : ℝ := Real.sqrt (1 - q) with hvdef
  have hv : v ^ 2 = 1 - q := Real.sq_sqrt (by linarith [hq.2])
  set c₀ : ℝ := ∫ s, U (v * s) ∂(gaussianReal 0 1) with hc₀
  have hV : ExpTame (fun x => U x - c₀) := hU.sub_const c₀
  have hV0 : ∫ t, (fun x => U x - c₀) (v * t) ∂(gaussianReal 0 1) = 0 :=
    hU.integral_sub_const_mul_gaussianReal v
  obtain ⟨C, hC0, hCb⟩ := hV.gibbs_fluctuation_abs_le (m := 2 * (2 * k)) (by omega) v
    (by nlinarith [hq.1, hq.2]) hV0
  obtain ⟨K', hK'0, hK'⟩ := sk_overlap_moment_le_of_exp β h q hfix hβ (2 * k)
  set C₂ : ℝ := C * (((2 * (2 * k)) * (2 * (2 * k)) : ℝ) ^ (2 * (2 * k)) *
    ((2 * (2 * k) : ℝ) * 4 ^ (2 * (2 * k)))) with hC₂
  have hC₂0 : 0 ≤ C₂ := by positivity
  set M : ℝ := Real.exp (8 * (k : ℝ) ^ 2 * β ^ 2) with hM
  have hM0 : 0 < M := Real.exp_pos _
  refine ⟨C₂, M, K', hC₂0, hM0, hK'0, fun N hN => ?_⟩
  have hNk : (0 : ℝ) < (N : ℝ) ^ k := by positivity
  set ξ : Fin N → (Fin N → ℤˣ) → ℝ := fun i a => ((a i : ℤ) : ℝ) with hξ
  have hξ_abs : ∀ i a, |ξ i a| ≤ 1 := fun i a => abs_units_cast_le_one (a i)
  have hξ_sq : ∀ i a, ξ i a ^ 2 = 1 := fun i a => units_cast_sq (a i)
  set P : Measure (FinPairs N → ℝ) := Measure.pi fun _ : FinPairs N => gaussianReal 0 1 with hP
  set Q : Measure (Fin N → ℝ) := Measure.pi fun _ : Fin N => gaussianReal 0 1 with hQ
  set J : (FinPairs N → ℝ) → ℝ := fun g =>
    overlapMoment ξ (skGibbsEnergy N β h g) q (2 * k) with hJ
  have hJint : Integrable J P := by
    refine integrable_integral_pi_count_tilted_det (P := P) (R := Fin 2)
      (g := fun a g => skGibbsEnergy N β h g a) (fun a => ?_)
      (fun τ => (overlapGibbs ξ (τ 0) (τ 1) - q) ^ (2 * (2 * k)))
    unfold skGibbsEnergy
    exact (by fun_prop : Measurable _).aemeasurable
  have hJmom : ∫ g, J g ∂P ≤ K' / ((N : ℝ) ^ k) ^ 2 := by
    have h1 := hK' N hN
    have h2 : ((N : ℝ) ^ (2 * k)) = ((N : ℝ) ^ k) ^ 2 := by
      rw [← pow_mul]; congr 1; ring
    rwa [h2] at h1
  set Upper : (FinPairs N → ℝ) → (Fin N → ℝ) → ℝ := fun g y =>
    let f := skGibbsEnergy N β h g
    let μ := Measure.count.tilted f
    let m : Fin N → ℝ := fun i => ∫ b, ((b i : ℤ) : ℝ) ∂μ
    let A := (∫ a, U ((fun i => (Real.sqrt N)⁻¹ * (((a i : ℤ) : ℝ) - m i)) ⬝ᵥ y) ∂μ) - c₀
    let B := Real.exp ((fun i => (Real.sqrt N)⁻¹ * (ε * β * m i)) ⬝ᵥ y)
    ((N : ℝ) ^ k * A ^ (4 * k) + (N : ℝ) ^ (- (k : ℝ)) * B ^ (4 * k)) / 2 with hUpper
  set Bnd : (FinPairs N → ℝ) → ℝ := fun g =>
    (C₂ * (N : ℝ) ^ k * J g + (N : ℝ) ^ (- (k : ℝ)) * M) / 2 with hBnd
  have h_bound_int : Integrable Bnd P := by
    have h1 : Integrable (fun g => C₂ * (N : ℝ) ^ k * J g / 2) P :=
      (hJint.const_mul (C₂ * (N : ℝ) ^ k)).div_const 2
    have h2 : Integrable (fun _ : FinPairs N → ℝ => (N : ℝ) ^ (- (k : ℝ)) * M / 2) P :=
      integrable_const _
    have heq : Bnd = fun g => C₂ * (N : ℝ) ^ k * J g / 2 + (N : ℝ) ^ (- (k : ℝ)) * M / 2 := by
      ext g; ring
    rw [heq]
    exact h1.add h2
  have h_split_outer : ∫ g, Bnd g ∂P =
      (C₂ * (N : ℝ) ^ k * (∫ g, J g ∂P) + (N : ℝ) ^ (- (k : ℝ)) * M) / 2 := by
    have h1 : Integrable (fun g => C₂ * (N : ℝ) ^ k * J g / 2) P :=
      (hJint.const_mul (C₂ * (N : ℝ) ^ k)).div_const 2
    have h2 : Integrable (fun _ : FinPairs N → ℝ => (N : ℝ) ^ (- (k : ℝ)) * M / 2) P :=
      integrable_const _
    have heq : Bnd = fun g => C₂ * (N : ℝ) ^ k * J g / 2 + (N : ℝ) ^ (- (k : ℝ)) * M / 2 := by
      ext g; ring
    rw [heq, integral_add h1 h2]
    simp only [integral_div, integral_const_mul, integral_const, probReal_univ, one_smul]
    ring_nf
  have h_calc : (C₂ * (N : ℝ) ^ k * (∫ g, J g ∂P) + (N : ℝ) ^ (- (k : ℝ)) * M) / 2 ≤
      ((C₂ * K' + M) / 2) / (N : ℝ) ^ k := by
    have hJ_le : C₂ * (N : ℝ) ^ k * (∫ g, J g ∂P) ≤ C₂ * K' / (N : ℝ) ^ k := by
      have h1 : C₂ * (N : ℝ) ^ k * (∫ g, J g ∂P) ≤
          C₂ * (N : ℝ) ^ k * (K' / ((N : ℝ) ^ k) ^ 2) :=
        mul_le_mul_of_nonneg_left hJmom (by positivity)
      refine h1.trans (le_of_eq ?_)
      have hNk_ne : (N : ℝ) ^ k ≠ 0 := hNk.ne'
      field_simp
    have hM_le : (N : ℝ) ^ (- (k : ℝ)) * M = M / (N : ℝ) ^ k := by
      rw [Real.rpow_neg (by positivity), Real.rpow_natCast]
      ring
    rw [hM_le]
    calc (C₂ * (N : ℝ) ^ k * (∫ g, J g ∂P) + M / (N : ℝ) ^ k) / 2
      _ ≤ (C₂ * K' / (N : ℝ) ^ k + M / (N : ℝ) ^ k) / 2 := by gcongr
      _ = ((C₂ * K' + M) / 2) / (N : ℝ) ^ k := by ring
  have h_calc_final : ∫ g, Bnd g ∂P ≤ ((C₂ * K' + M) / 2) / (N : ℝ) ^ k := by
    rw [h_split_outer]
    exact h_calc
  refine ⟨Upper, Bnd, fun g y => ?_, fun g => ?_, fun g => ?_, h_bound_int, h_calc_final⟩
  · set f := skGibbsEnergy N β h g
    set μ := Measure.count.tilted f
    set m : Fin N → ℝ := fun i => ∫ b, ((b i : ℤ) : ℝ) ∂μ
    set A : (Fin N → ℝ) → ℝ := fun y =>
      (∫ a, U ((fun i => (Real.sqrt N)⁻¹ * (((a i : ℤ) : ℝ) - m i)) ⬝ᵥ y) ∂μ) - c₀
    set B : (Fin N → ℝ) → ℝ := fun y =>
      Real.exp ((fun i => (Real.sqrt N)⁻¹ * (ε * β * m i)) ⬝ᵥ y)
    rw [mul_pow]
    have h_amgm := mul_le_half_mul_add_inv_mul (t := (N : ℝ) ^ k) hNk
      (a := A y ^ (2 * k)) (b := B y ^ (2 * k))
    have hA4 : (A y ^ (2 * k)) ^ 2 = A y ^ (4 * k) := by rw [← pow_mul]; congr 1; ring
    have hB4 : (B y ^ (2 * k)) ^ 2 = B y ^ (4 * k) := by rw [← pow_mul]; congr 1; ring
    rw [hA4, hB4] at h_amgm
    have h_inv : ((N : ℝ) ^ k)⁻¹ = (N : ℝ) ^ (- (k : ℝ)) := by
      rw [Real.rpow_neg (by positivity), Real.rpow_natCast]
    rw [h_inv] at h_amgm
    exact h_amgm
  · set f := skGibbsEnergy N β h g
    set μ := Measure.count.tilted f with hμ
    set m : Fin N → ℝ := fun i => ∫ b, ((b i : ℤ) : ℝ) ∂μ
    set A : (Fin N → ℝ) → ℝ := fun y =>
      (∫ a, U ((fun i => (Real.sqrt N)⁻¹ * (((a i : ℤ) : ℝ) - m i)) ⬝ᵥ y) ∂μ) - c₀
    set B : (Fin N → ℝ) → ℝ := fun y =>
      Real.exp ((fun i => (Real.sqrt N)⁻¹ * (ε * β * m i)) ⬝ᵥ y)
    have heqB : (fun y => B y ^ (4 * k)) =
        fun y => Real.exp (((fun i =>
          ((4 * k : ℕ) : ℝ) * ((Real.sqrt N)⁻¹ * (ε * β * m i)))) ⬝ᵥ y) := by
      ext y
      simp only [B]
      rw [← Real.exp_nat_mul]
      congr 1
      simp only [dotProduct]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => by push_cast; ring
    have hB_integrable : Integrable (fun y => B y ^ (4 * k)) Q := by
      rw [heqB]
      exact integrable_exp_dotProduct_gaussianReal _
    have hrew : ∀ y : Fin N → ℝ, A y =
        ∫ a, (U ((fun i => (Real.sqrt N)⁻¹ * (((a i : ℤ) : ℝ) - m i)) ⬝ᵥ y) - c₀) ∂μ := fun y => by
      dsimp [A]
      rw [integral_sub Integrable.of_finite (integrable_const _)]
      simp
    have hA_integrable : Integrable (fun y => A y ^ (4 * k)) Q := by
      set c : (Fin N → ℤˣ) → Fin N → ℝ :=
        fun a i => (Real.sqrt N)⁻¹ * (((a i : ℤ) : ℝ) - m i)
      have h4k : 4 * k = 2 * (2 * k) := by ring
      have h4k_pos : 0 < 2 * (2 * k) := by omega
      have hint : ∀ σ : Fin (2 * (2 * k)) → (Fin N → ℤˣ),
          Integrable (fun y => ∏ l,
            (fun x => U x - c₀) (c (σ l) ⬝ᵥ y)) Q := fun σ =>
        integrable_prod_derivProd_zero h4k_pos hV (fun l => c (σ l))
      have h_sum : Integrable (fun y => ∑ σ : Fin (2 * (2 * k)) → (Fin N → ℤˣ),
          (∏ i, Real.exp (f (σ i)) / ∑ b, Real.exp (f b)) *
            ∏ l, (fun x => U x - c₀) (c (σ l) ⬝ᵥ y)) Q :=
        integrable_finsetSum _ fun σ _ => (hint σ).const_mul _
      have heq : (fun y => A y ^ (4 * k)) = fun y =>
          ∑ σ : Fin (2 * (2 * k)) → (Fin N → ℤˣ),
            (∏ i, Real.exp (f (σ i)) / ∑ b, Real.exp (f b)) *
              ∏ l, (fun x => U x - c₀) (c (σ l) ⬝ᵥ y) := by
        ext y
        rw [hrew y, h4k]
        have hprod : (∫ a, (fun x => U x - c₀) (c a ⬝ᵥ y) ∂μ) ^ (2 * (2 * k)) =
            ∫ σ : Fin (2 * (2 * k)) → (Fin N → ℤˣ),
              ∏ l, (fun x => U x - c₀) (c (σ l) ⬝ᵥ y)
              ∂(Measure.pi fun _ : Fin (2 * (2 * k)) => Measure.count.tilted f) := by
          rw [hμ, integral_fintype_prod_eq_prod (fun (_ : Fin (2 * (2 * k))) (a : Fin N → ℤˣ) =>
            (fun x => U x - c₀) (c a ⬝ᵥ y))]
          simp
        rw [hprod, integral_pi_count_tilted f]
      rw [heq]
      exact h_sum
    have hg₁ : Integrable (fun y => (N : ℝ) ^ k * A y ^ (4 * k) / 2) Q :=
      (hA_integrable.const_mul ((N : ℝ) ^ k)).div_const 2
    have hg₂_div : Integrable (fun y => (N : ℝ) ^ (- (k : ℝ)) * B y ^ (4 * k) / 2) Q :=
      (hB_integrable.const_mul ((N : ℝ) ^ (- (k : ℝ)))).div_const 2
    have heq : (fun y => Upper g y) =
        (fun y => (N : ℝ) ^ k * A y ^ (4 * k) / 2 + (N : ℝ) ^ (- (k : ℝ)) * B y ^ (4 * k) / 2) := by
      ext y; ring
    change Integrable (fun y => Upper g y) Q
    rw [heq]
    exact hg₁.add hg₂_div
  · set f := skGibbsEnergy N β h g
    set μ := Measure.count.tilted f with hμ
    set m : Fin N → ℝ := fun i => ∫ b, ((b i : ℤ) : ℝ) ∂μ
    have hm_le : ∀ i, |m i| ≤ 1 := fun i => abs_integral_units_cast_le μ _
    set A : (Fin N → ℝ) → ℝ := fun y =>
      (∫ a, U ((fun i => (Real.sqrt N)⁻¹ * (((a i : ℤ) : ℝ) - m i)) ⬝ᵥ y) ∂μ) - c₀
    set B : (Fin N → ℝ) → ℝ := fun y =>
      Real.exp ((fun i => (Real.sqrt N)⁻¹ * (ε * β * m i)) ⬝ᵥ y)
    have hrew : ∀ y : Fin N → ℝ, A y =
        ∫ a, (U ((fun i => (Real.sqrt N)⁻¹ * (((a i : ℤ) : ℝ) - m i)) ⬝ᵥ y) - c₀) ∂μ := fun y => by
      dsimp [A]
      rw [integral_sub Integrable.of_finite (integrable_const _)]
      simp
    have hA_int : ∫ y, A y ^ (4 * k) ∂Q ≤ C₂ * J g := by
      simp_rw [hrew]
      refine (le_abs_self _).trans ?_
      have h4k : 4 * k = 2 * (2 * k) := by ring
      have heq : |∫ y, (∫ a, U ((fun i => (Real.sqrt N)⁻¹ *
              (((a i : ℤ) : ℝ) - m i)) ⬝ᵥ y) - c₀ ∂μ) ^ (4 * k) ∂Q| =
          |∫ y, (∫ a, U ((fun i => (Real.sqrt N)⁻¹ *
              (ξ i a - ∫ b, ξ i b ∂(Measure.count.tilted f))) ⬝ᵥ y) - c₀
              ∂(Measure.count.tilted f)) ^ (2 * (2 * k))
              ∂(Measure.pi fun _ : Fin N => gaussianReal 0 1)| := by
        rw [h4k]
      rw [heq]
      have h1 := hCb N (Fin N → ℤˣ) ξ hξ_abs f
      have h2 := sum_integral_abs_pairProd_le (k := 2 * k) ξ hξ_sq hN f q v hv (by omega)
      have h3 : C * ((2 * ↑(2 * k) * (2 * ↑(2 * k))) ^ (2 * (2 * k)) *
          (2 * ↑(2 * k) * (4 ^ (2 * (2 * k)) * overlapMoment ξ f q (2 * k)))) = C₂ * J g := by
        dsimp [C₂, J, f]
        push_cast
        ring
      exact h1.trans (mul_le_mul_of_nonneg_left h2 hC0 |>.trans (le_of_eq h3))
    have hB_int : ∫ y, B y ^ (4 * k) ∂Q ≤ M := by
      have heq : (fun y => B y ^ (4 * k)) =
          fun y => Real.exp (4 * (k : ℝ) * (ε * β) * ((fun i => (Real.sqrt N)⁻¹ * m i) ⬝ᵥ y)) := by
        ext y
        simp only [B]
        rw [← Real.exp_nat_mul]
        congr 1
        simp only [dotProduct]
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => by push_cast; ring
      rw [heq]
      have h_mom := integral_exp_sum_ising_moment_le hN (4 * (k : ℝ) * (ε * β)) m hm_le
      have h_pow : (4 * (k : ℝ) * (ε * β)) ^ 2 / 2 = 8 * (k : ℝ) ^ 2 * β ^ 2 := by
        calc (4 * (k : ℝ) * (ε * β)) ^ 2 / 2
          _ = (16 * (k : ℝ) ^ 2 * (ε ^ 2 * β ^ 2)) / 2 := by ring
          _ = (16 * (k : ℝ) ^ 2 * β ^ 2) / 2 := by rw [hε, one_mul]
          _ = 8 * (k : ℝ) ^ 2 * β ^ 2 := by ring
      rwa [h_pow] at h_mom
    have heqB : (fun y => B y ^ (4 * k)) =
        fun y => Real.exp (((fun i =>
          ((4 * k : ℕ) : ℝ) * ((Real.sqrt N)⁻¹ * (ε * β * m i)))) ⬝ᵥ y) := by
      ext y
      simp only [B]
      rw [← Real.exp_nat_mul]
      congr 1
      simp only [dotProduct]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => by push_cast; ring
    have hB_integrable : Integrable (fun y => B y ^ (4 * k)) Q := by
      rw [heqB]
      exact integrable_exp_dotProduct_gaussianReal _
    have hA_integrable : Integrable (fun y => A y ^ (4 * k)) Q := by
      set c : (Fin N → ℤˣ) → Fin N → ℝ :=
        fun a i => (Real.sqrt N)⁻¹ * (((a i : ℤ) : ℝ) - m i)
      have h4k : 4 * k = 2 * (2 * k) := by ring
      have h4k_pos : 0 < 2 * (2 * k) := by omega
      have hint : ∀ σ : Fin (2 * (2 * k)) → (Fin N → ℤˣ),
          Integrable (fun y => ∏ l,
            (fun x => U x - c₀) (c (σ l) ⬝ᵥ y)) Q := fun σ =>
        integrable_prod_derivProd_zero h4k_pos hV (fun l => c (σ l))
      have h_sum : Integrable (fun y => ∑ σ : Fin (2 * (2 * k)) → (Fin N → ℤˣ),
          (∏ i, Real.exp (f (σ i)) / ∑ b, Real.exp (f b)) *
            ∏ l, (fun x => U x - c₀) (c (σ l) ⬝ᵥ y)) Q :=
        integrable_finsetSum _ fun σ _ => (hint σ).const_mul _
      have heq : (fun y => A y ^ (4 * k)) = fun y =>
          ∑ σ : Fin (2 * (2 * k)) → (Fin N → ℤˣ),
            (∏ i, Real.exp (f (σ i)) / ∑ b, Real.exp (f b)) *
              ∏ l, (fun x => U x - c₀) (c (σ l) ⬝ᵥ y) := by
        ext y
        rw [hrew y, h4k]
        have hprod : (∫ a, (fun x => U x - c₀) (c a ⬝ᵥ y) ∂μ) ^ (2 * (2 * k)) =
            ∫ σ : Fin (2 * (2 * k)) → (Fin N → ℤˣ),
              ∏ l, (fun x => U x - c₀) (c (σ l) ⬝ᵥ y)
              ∂(Measure.pi fun _ : Fin (2 * (2 * k)) => Measure.count.tilted f) := by
          rw [hμ, integral_fintype_prod_eq_prod (fun (_ : Fin (2 * (2 * k))) (a : Fin N → ℤˣ) =>
            (fun x => U x - c₀) (c a ⬝ᵥ y))]
          simp
        rw [hprod, integral_pi_count_tilted f]
      rw [heq]
      exact h_sum
    have hg₁ : Integrable (fun y => (N : ℝ) ^ k * A y ^ (4 * k) / 2) Q :=
      (hA_integrable.const_mul ((N : ℝ) ^ k)).div_const 2
    have hg₂_div : Integrable (fun y => (N : ℝ) ^ (- (k : ℝ)) * B y ^ (4 * k) / 2) Q :=
      (hB_integrable.const_mul ((N : ℝ) ^ (- (k : ℝ)))).div_const 2
    have h_split_int : ∫ y, Upper g y ∂Q =
        ((N : ℝ) ^ k * (∫ y, A y ^ (4 * k) ∂Q) +
          (N : ℝ) ^ (- (k : ℝ)) * (∫ y, B y ^ (4 * k) ∂Q)) / 2 := by
      have heq : (fun y => Upper g y) =
          (fun y => (N : ℝ) ^ k * A y ^ (4 * k) / 2 +
            (N : ℝ) ^ (- (k : ℝ)) * B y ^ (4 * k) / 2) := by
        ext y; ring
      rw [heq, integral_add hg₁ hg₂_div]
      simp only [integral_div, integral_const_mul]
      ring_nf
    rw [h_split_int]
    refine div_le_div_of_nonneg_right (add_le_add ?_ ?_) (by norm_num)
    · calc (N : ℝ) ^ k * (∫ y, A y ^ (4 * k) ∂Q) ≤ (N : ℝ) ^ k * (C₂ * J g) :=
           mul_le_mul_of_nonneg_left hA_int (by positivity)
        _ = C₂ * (N : ℝ) ^ k * J g := by ring
    · exact mul_le_mul_of_nonneg_left hB_int (by positivity)

/-- **The general Gaussian fluctuation principle with multiplier
(generalizes (1.206) and (1.207)).** -/
theorem sk_gaussian_fluctuation_mul_exp (β h q : ℝ)
    (hfix : ∫ x : ℝ, Real.tanh (β * Real.sqrt q * x + h) ^ 2 ∂(gaussianReal 0 1) = q)
    (hβ : 4 * β ^ 2 < 1) (ε : ℝ) (hε : ε ^ 2 = 1) {k : ℕ} (hk : 1 ≤ k)
    {U : ℝ → ℝ} (hU : ExpTame U) :
    ∃ K : ℝ, 0 < K ∧ ∀ N : ℕ, 0 < N →
      ∫ g : FinPairs N → ℝ, ∫ y : Fin N → ℝ,
        (((∫ a, U ((fun i => (Real.sqrt N)⁻¹ *
              (((a i : ℤ) : ℝ) -
              ∫ b, ((b i : ℤ) : ℝ) ∂(Measure.count.tilted (skGibbsEnergy N β h g)))) ⬝ᵥ y)
            ∂(Measure.count.tilted (skGibbsEnergy N β h g))) -
          ∫ s, U (Real.sqrt (1 - q) * s) ∂(gaussianReal 0 1)) *
          Real.exp ((fun i => (Real.sqrt N)⁻¹ *
            (ε * β * ∫ b, ((b i : ℤ) : ℝ)
              ∂(Measure.count.tilted (skGibbsEnergy N β h g)))) ⬝ᵥ y)) ^ (2 * k)
        ∂(Measure.pi fun _ : Fin N => gaussianReal 0 1)
      ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1) ≤ K / (N : ℝ) ^ k := by
  obtain ⟨C₂, M, K', hC₂, hM, hK', h_bound⟩ :=
    sk_gaussian_fluctuation_upper_bound β h q hfix hβ ε hε hk hU
  refine ⟨(C₂ * K' + M) / 2 + 1, by positivity, fun N hN => ?_⟩
  obtain ⟨Upper, Bnd, h_le, h_int_inner, h_upper_bnd, h_bnd_int, h_bnd_le⟩ := h_bound N hN
  have h_inner : ∀ g, ∫ y : Fin N → ℝ,
      (((∫ a, U ((fun i => (Real.sqrt N)⁻¹ *
            (((a i : ℤ) : ℝ) -
              ∫ b, ((b i : ℤ) : ℝ) ∂(Measure.count.tilted (skGibbsEnergy N β h g)))) ⬝ᵥ y)
          ∂(Measure.count.tilted (skGibbsEnergy N β h g))) -
        ∫ s, U (Real.sqrt (1 - q) * s) ∂(gaussianReal 0 1)) *
        Real.exp ((fun i => (Real.sqrt N)⁻¹ *
          (ε * β * ∫ b, ((b i : ℤ) : ℝ)
            ∂(Measure.count.tilted (skGibbsEnergy N β h g)))) ⬝ᵥ y)) ^ (2 * k)
      ∂(Measure.pi fun _ : Fin N => gaussianReal 0 1) ≤ Bnd g := fun g =>
    (integral_mono_of_nonneg
      (ae_of_all _ fun y => Even.pow_nonneg ⟨k, by ring⟩ _)
      (h_int_inner g) (ae_of_all _ fun y => h_le g y)).trans (h_upper_bnd g)
  have hnonneg : ∀ g, 0 ≤ ∫ y : Fin N → ℝ,
      (((∫ a, U ((fun i => (Real.sqrt N)⁻¹ *
            (((a i : ℤ) : ℝ) -
              ∫ b, ((b i : ℤ) : ℝ) ∂(Measure.count.tilted (skGibbsEnergy N β h g)))) ⬝ᵥ y)
          ∂(Measure.count.tilted (skGibbsEnergy N β h g))) -
        ∫ s, U (Real.sqrt (1 - q) * s) ∂(gaussianReal 0 1)) *
        Real.exp ((fun i => (Real.sqrt N)⁻¹ *
          (ε * β * ∫ b, ((b i : ℤ) : ℝ)
            ∂(Measure.count.tilted (skGibbsEnergy N β h g)))) ⬝ᵥ y)) ^ (2 * k)
      ∂(Measure.pi fun _ : Fin N => gaussianReal 0 1) := fun g =>
    integral_nonneg fun y => Even.pow_nonneg ⟨k, by ring⟩ _
  have h_outer := integral_mono_of_nonneg (ae_of_all _ hnonneg) h_bnd_int (ae_of_all _ h_inner)
  exact h_outer.trans (h_bnd_le.trans (by gcongr; linarith))

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
  have hU : ExpTame (fun x => Real.exp (ε * β * x)) := expTame_exp (ε * β)
  obtain ⟨K, hK0, hK⟩ := sk_gaussian_fluctuation_mul_exp β h q hfix hβ ε hε hk hU
  refine ⟨K, hK0, fun N hN => ?_⟩
  have h_bound := hK N hN
  have hq := fixedPoint_mem_Icc hfix
  set v : ℝ := Real.sqrt (1 - q)
  have hv : v ^ 2 = 1 - q := Real.sq_sqrt (by linarith [hq.2])
  have h_gauss : ∫ t, Real.exp (ε * β * (v * t)) ∂(gaussianReal 0 1) =
      Real.exp (β ^ 2 * (1 - q) / 2) := by
    rw [integral_exp_scaled_gaussianReal_zero_one]
    congr 1
    calc (ε * β) ^ 2 * v ^ 2 / 2
      _ = (ε ^ 2 * β ^ 2) * (1 - q) / 2 := by rw [hv]; ring
      _ = β ^ 2 * (1 - q) / 2 := by rw [hε, one_mul]
  have heq : ∀ (g : FinPairs N → ℝ) (y : Fin N → ℝ),
      ((∫ a, Real.exp ((fun i => (Real.sqrt N)⁻¹ * (ε * β * ((a i : ℤ) : ℝ))) ⬝ᵥ y)
          ∂(Measure.count.tilted (skGibbsEnergy N β h g))) -
        Real.exp (β ^ 2 * (1 - q) / 2) *
          Real.exp ((fun i => (Real.sqrt N)⁻¹ *
            (ε * β * ∫ b, ((b i : ℤ) : ℝ)
              ∂(Measure.count.tilted (skGibbsEnergy N β h g)))) ⬝ᵥ y)) =
      ((∫ a, Real.exp (ε * β * ((fun i => (Real.sqrt N)⁻¹ *
            (((a i : ℤ) : ℝ) -
              ∫ b, ((b i : ℤ) : ℝ) ∂(Measure.count.tilted (skGibbsEnergy N β h g)))) ⬝ᵥ y))
          ∂(Measure.count.tilted (skGibbsEnergy N β h g))) -
        ∫ s, Real.exp (ε * β * (Real.sqrt (1 - q) * s)) ∂(gaussianReal 0 1)) *
        Real.exp ((fun i => (Real.sqrt N)⁻¹ *
          (ε * β * ∫ b, ((b i : ℤ) : ℝ)
            ∂(Measure.count.tilted (skGibbsEnergy N β h g)))) ⬝ᵥ y) := fun g y => by
    set f := skGibbsEnergy N β h g
    set μ := Measure.count.tilted f
    set m : Fin N → ℝ := fun i => ∫ b, ((b i : ℤ) : ℝ) ∂μ
    set B : ℝ := Real.exp ((fun i => (Real.sqrt N)⁻¹ * (ε * β * m i)) ⬝ᵥ y)
    rw [h_gauss]
    have h1 : ∀ a : Fin N → ℤˣ,
        Real.exp (ε * β * ((fun i => (Real.sqrt N)⁻¹ * (((a i : ℤ) : ℝ) - m i)) ⬝ᵥ y)) * B =
        Real.exp ((fun i => (Real.sqrt N)⁻¹ * (ε * β * ((a i : ℤ) : ℝ))) ⬝ᵥ y) :=
      fun a => exp_dotProduct_ising_split N β ε y a m
    have h2 : ∫ a, Real.exp ((fun i => (Real.sqrt N)⁻¹ * (ε * β * ((a i : ℤ) : ℝ))) ⬝ᵥ y) ∂μ =
        (∫ a, Real.exp (ε * β *
          ((fun i => (Real.sqrt N)⁻¹ * (((a i : ℤ) : ℝ) - m i)) ⬝ᵥ y)) ∂μ) * B := by
      simp_rw [← h1, integral_mul_const]
    rw [h2, sub_mul]
  simp_rw [heq]
  exact h_bound

/-- **Talagrand Corollary 1.7.13, Eq. (1.207): Derivative/id-mul-exp observable.** -/
theorem sk_gaussian_fluctuation_id_mul_exp (β h q : ℝ)
    (hfix : ∫ x : ℝ, Real.tanh (β * Real.sqrt q * x + h) ^ 2 ∂(gaussianReal 0 1) = q)
    (hβ : 4 * β ^ 2 < 1) (ε : ℝ) (hε : ε ^ 2 = 1) {k : ℕ} (hk : 1 ≤ k) :
    ∃ K : ℝ, 0 < K ∧ ∀ N : ℕ, 0 < N →
      ∫ g : FinPairs N → ℝ, ∫ y : Fin N → ℝ,
        ((∫ a, ((fun i => (Real.sqrt N)⁻¹ *
              (((a i : ℤ) : ℝ) -
              ∫ b, ((b i : ℤ) : ℝ) ∂(Measure.count.tilted (skGibbsEnergy N β h g)))) ⬝ᵥ y) *
            Real.exp ((fun i => (Real.sqrt N)⁻¹ * (ε * β * ((a i : ℤ) : ℝ))) ⬝ᵥ y)
            ∂(Measure.count.tilted (skGibbsEnergy N β h g))) -
          ε * β * (1 - q) * Real.exp (β ^ 2 * (1 - q) / 2) *
            Real.exp ((fun i => (Real.sqrt N)⁻¹ *
              (ε * β * ∫ b, ((b i : ℤ) : ℝ)
                ∂(Measure.count.tilted (skGibbsEnergy N β h g)))) ⬝ᵥ y)) ^ (2 * k)
          ∂(Measure.pi fun _ : Fin N => gaussianReal 0 1)
        ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1) ≤ K / (N : ℝ) ^ k := by
  have hU : ExpTame (fun x => x * Real.exp (ε * β * x)) := expTame_id_mul_exp (ε * β)
  obtain ⟨K, hK0, hK⟩ := sk_gaussian_fluctuation_mul_exp β h q hfix hβ ε hε hk hU
  refine ⟨K, hK0, fun N hN => ?_⟩
  have h_bound := hK N hN
  have hq := fixedPoint_mem_Icc hfix
  set v : ℝ := Real.sqrt (1 - q)
  have hv : v ^ 2 = 1 - q := Real.sq_sqrt (by linarith [hq.2])
  have h_gauss : ∫ t, (v * t) * Real.exp (ε * β * (v * t)) ∂(gaussianReal 0 1) =
      ε * β * (1 - q) * Real.exp (β ^ 2 * (1 - q) / 2) := by
    rw [integral_id_mul_exp_scaled_gaussianReal_zero_one, hv]
    congr 1
    congr 1
    calc (ε * β) ^ 2 * (1 - q) / 2
      _ = (ε ^ 2 * β ^ 2) * (1 - q) / 2 := by ring
      _ = β ^ 2 * (1 - q) / 2 := by rw [hε, one_mul]
  have heq : ∀ (g : FinPairs N → ℝ) (y : Fin N → ℝ),
      ((∫ a, ((fun i => (Real.sqrt N)⁻¹ *
            (((a i : ℤ) : ℝ) -
              ∫ b, ((b i : ℤ) : ℝ) ∂(Measure.count.tilted (skGibbsEnergy N β h g)))) ⬝ᵥ y) *
          Real.exp ((fun i => (Real.sqrt N)⁻¹ * (ε * β * ((a i : ℤ) : ℝ))) ⬝ᵥ y)
          ∂(Measure.count.tilted (skGibbsEnergy N β h g))) -
        ε * β * (1 - q) * Real.exp (β ^ 2 * (1 - q) / 2) *
          Real.exp ((fun i => (Real.sqrt N)⁻¹ *
            (ε * β * ∫ b, ((b i : ℤ) : ℝ)
              ∂(Measure.count.tilted (skGibbsEnergy N β h g)))) ⬝ᵥ y)) =
      ((∫ a, ((fun i => (Real.sqrt N)⁻¹ *
            (((a i : ℤ) : ℝ) -
              ∫ b, ((b i : ℤ) : ℝ) ∂(Measure.count.tilted (skGibbsEnergy N β h g)))) ⬝ᵥ y) *
          Real.exp (ε * β * ((fun i => (Real.sqrt N)⁻¹ *
            (((a i : ℤ) : ℝ) -
              ∫ b, ((b i : ℤ) : ℝ) ∂(Measure.count.tilted (skGibbsEnergy N β h g)))) ⬝ᵥ y))
          ∂(Measure.count.tilted (skGibbsEnergy N β h g))) -
        ∫ s, (Real.sqrt (1 - q) * s) *
          Real.exp (ε * β * (Real.sqrt (1 - q) * s)) ∂(gaussianReal 0 1)) *
        Real.exp ((fun i => (Real.sqrt N)⁻¹ *
          (ε * β * ∫ b, ((b i : ℤ) : ℝ)
            ∂(Measure.count.tilted (skGibbsEnergy N β h g)))) ⬝ᵥ y) := fun g y => by
    set f := skGibbsEnergy N β h g
    set μ := Measure.count.tilted f
    set m : Fin N → ℝ := fun i => ∫ b, ((b i : ℤ) : ℝ) ∂μ
    set B : ℝ := Real.exp ((fun i => (Real.sqrt N)⁻¹ * (ε * β * m i)) ⬝ᵥ y)
    rw [h_gauss]
    have h1 : ∀ a : Fin N → ℤˣ,
        (((fun i => (Real.sqrt N)⁻¹ * (((a i : ℤ) : ℝ) - m i)) ⬝ᵥ y) *
          Real.exp (ε * β * ((fun i => (Real.sqrt N)⁻¹ * (((a i : ℤ) : ℝ) - m i)) ⬝ᵥ y))) * B =
        ((fun i => (Real.sqrt N)⁻¹ * (((a i : ℤ) : ℝ) - m i)) ⬝ᵥ y) *
          Real.exp ((fun i => (Real.sqrt N)⁻¹ * (ε * β * ((a i : ℤ) : ℝ))) ⬝ᵥ y) :=
      fun a => id_mul_exp_dotProduct_ising_split N β ε y a m
    have h2 : ∫ a, ((fun i => (Real.sqrt N)⁻¹ * (((a i : ℤ) : ℝ) - m i)) ⬝ᵥ y) *
        Real.exp ((fun i => (Real.sqrt N)⁻¹ * (ε * β * ((a i : ℤ) : ℝ))) ⬝ᵥ y) ∂μ =
        (∫ a, ((fun i => (Real.sqrt N)⁻¹ * (((a i : ℤ) : ℝ) - m i)) ⬝ᵥ y) *
          Real.exp (ε * β *
            ((fun i => (Real.sqrt N)⁻¹ * (((a i : ℤ) : ℝ) - m i)) ⬝ᵥ y)) ∂μ) * B := by
      simp_rw [← h1, integral_mul_const]
    rw [h2, sub_mul]
  simp_rw [heq]
  exact h_bound

lemma cosh_add_eq (u h : ℝ) :
    Real.cosh (u + h) = (Real.exp h * Real.exp u + Real.exp (-h) * Real.exp (-u)) / 2 := by
  rw [Real.cosh_eq, Real.exp_add, show -(u + h) = -h + -u by ring, Real.exp_add]
  ring

lemma sinh_add_eq (u h : ℝ) :
    Real.sinh (u + h) = (Real.exp h * Real.exp u - Real.exp (-h) * Real.exp (-u)) / 2 := by
  rw [Real.sinh_eq, Real.exp_add, show -(u + h) = -h + -u by ring, Real.exp_add]
  ring

lemma integral_sinh_add {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : Measure α) [IsProbabilityMeasure μ] [Finite α] (u : α → ℝ) (h : ℝ) :
    ∫ a, Real.sinh (u a + h) ∂μ =
      (Real.exp h * (∫ a, Real.exp (u a) ∂μ) -
        Real.exp (-h) * (∫ a, Real.exp (-u a) ∂μ)) / 2 := by
  have heq : (fun a => Real.sinh (u a + h)) =
      fun a => (Real.exp h * Real.exp (u a) - Real.exp (-h) * Real.exp (-u a)) / 2 := by
    ext a; exact sinh_add_eq (u a) h
  rw [heq, integral_div]
  rw [integral_sub Integrable.of_finite Integrable.of_finite]
  rw [integral_const_mul, integral_const_mul]

lemma integral_cosh_add {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : Measure α) [IsProbabilityMeasure μ] [Finite α] (u : α → ℝ) (h : ℝ) :
    ∫ a, Real.cosh (u a + h) ∂μ =
      (Real.exp h * (∫ a, Real.exp (u a) ∂μ) +
        Real.exp (-h) * (∫ a, Real.exp (-u a) ∂μ)) / 2 := by
  have heq : (fun a => Real.cosh (u a + h)) =
      fun a => (Real.exp h * Real.exp (u a) + Real.exp (-h) * Real.exp (-u a)) / 2 := by
    ext a; exact cosh_add_eq (u a) h
  rw [heq, integral_div]
  rw [integral_add Integrable.of_finite Integrable.of_finite]
  rw [integral_const_mul, integral_const_mul]

lemma dotProduct_neg (N : ℕ) (β : ℝ) (y : Fin N → ℝ) (v : Fin N → ℝ) :
    ((fun i => (Real.sqrt N)⁻¹ * ((-1) * β * v i)) ⬝ᵥ y) =
    - (((fun i => (Real.sqrt N)⁻¹ * (β * v i)) ⬝ᵥ y)) := by
  simp only [dotProduct]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => by ring


lemma abs_beta_one_sub_q_le {β q : ℝ} (hβ : 4 * β ^ 2 < 1) (hq : q ∈ Set.Icc (0 : ℝ) 1) :
    |β * (1 - q)| ≤ 1 := by
  have h1 : 0 ≤ 1 - q := by linarith [hq.2]
  have h2 : 1 - q ≤ 1 := by linarith [hq.1]
  have h4 : |β| ≤ 1 := by
    have hsq : β ^ 2 < (1 : ℝ) ^ 2 := by linarith [hβ]
    have h_lt : |β| < |(1 : ℝ)| := sq_lt_sq.mp hsq
    rw [abs_one] at h_lt
    exact h_lt.le
  calc |β * (1 - q)| = |β| * (1 - q) := by rw [abs_mul, abs_of_nonneg h1]
    _ ≤ 1 * 1 := mul_le_mul h4 h2 h1 zero_le_one
    _ = 1 := by norm_num

lemma one_le_integral_cosh {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : Measure α) [IsProbabilityMeasure μ] [Finite α] (u : α → ℝ) :
    1 ≤ ∫ a, Real.cosh (u a) ∂μ := by
  have h1 : (1 : ℝ) = ∫ _ : α, (1 : ℝ) ∂μ := by
    simp only [integral_const, probReal_univ, one_smul]
  rw [h1]
  exact integral_mono (integrable_const 1) Integrable.of_finite (fun a => Real.one_le_cosh (u a))

lemma abs_integral_sinh_le_integral_cosh {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] (μ : Measure α) [IsProbabilityMeasure μ]
    [Finite α] (u : α → ℝ) :
    |∫ a, Real.sinh (u a) ∂μ| ≤ ∫ a, Real.cosh (u a) ∂μ := by
  refine abs_integral_le_integral_abs.trans ?_
  exact integral_mono Integrable.of_finite Integrable.of_finite
    (fun a => Real.abs_sinh_le_cosh (u a))

lemma abs_sinh_cosh_diff_le (A' Atgt B' B D₁ D₂ h : ℝ)
    (hA : A' - Atgt = (Real.exp h * D₁ - Real.exp (-h) * D₂) / 2)
    (hB : B' - B = (Real.exp h * D₁ + Real.exp (-h) * D₂) / 2) :
    |A' - Atgt| + |B' - B| ≤ 2 * Real.cosh h * (|D₁| + |D₂|) := by
  have h1 : |A' - Atgt| ≤ (Real.exp h * |D₁| + Real.exp (-h) * |D₂|) / 2 := by
    rw [hA]
    refine (abs_div _ _).trans_le ?_
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    refine div_le_div_of_nonneg_right ?_ (by norm_num)
    calc |Real.exp h * D₁ - Real.exp (-h) * D₂|
      _ = |Real.exp h * D₁ + -(Real.exp (-h) * D₂)| := by rw [sub_eq_add_neg]
      _ ≤ |Real.exp h * D₁| + |-(Real.exp (-h) * D₂)| := abs_add_le _ _
      _ = |Real.exp h * D₁| + |Real.exp (-h) * D₂| := by rw [abs_neg]
      _ = Real.exp h * |D₁| + Real.exp (-h) * |D₂| := by
        rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)]
  have h2 : |B' - B| ≤ (Real.exp h * |D₁| + Real.exp (-h) * |D₂|) / 2 := by
    rw [hB]
    refine (abs_div _ _).trans_le ?_
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    refine div_le_div_of_nonneg_right ?_ (by norm_num)
    calc |Real.exp h * D₁ + Real.exp (-h) * D₂|
      _ ≤ |Real.exp h * D₁| + |Real.exp (-h) * D₂| := abs_add_le _ _
      _ = Real.exp h * |D₁| + Real.exp (-h) * |D₂| := by
        rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)]
  have he1 : Real.exp h ≤ 2 * Real.cosh h := by
    rw [Real.cosh_eq]; linarith [Real.exp_pos (-h)]
  have he2 : Real.exp (-h) ≤ 2 * Real.cosh h := by
    rw [Real.cosh_eq]; linarith [Real.exp_pos h]
  have hsum : (Real.exp h * |D₁| + Real.exp (-h) * |D₂|) / 2 +
      (Real.exp h * |D₁| + Real.exp (-h) * |D₂|) / 2 =
      Real.exp h * |D₁| + Real.exp (-h) * |D₂| := by ring
  calc |A' - Atgt| + |B' - B|
    _ ≤ (Real.exp h * |D₁| + Real.exp (-h) * |D₂|) / 2 +
        (Real.exp h * |D₁| + Real.exp (-h) * |D₂|) / 2 := add_le_add h1 h2
    _ = Real.exp h * |D₁| + Real.exp (-h) * |D₂| := hsum
    _ ≤ 2 * Real.cosh h * |D₁| + 2 * Real.cosh h * |D₂| := by gcongr
    _ = 2 * Real.cosh h * (|D₁| + |D₂|) := by ring

lemma add_pow_four_two_mul_le {k : ℕ} (hk : 1 ≤ k) (x₁ x₂ x₃ x₄ : ℝ) :
    (x₁ + x₂ + x₃ + x₄) ^ (2 * k) ≤
      4 ^ (2 * k - 1) * (x₁ ^ (2 * k) + x₂ ^ (2 * k) + x₃ ^ (2 * k) + x₄ ^ (2 * k)) := by
  have h1 : (x₁ + x₂ + x₃ + x₄) = (x₁ + x₂) + (x₃ + x₄) := by ring
  rw [h1]
  refine (add_pow_two_mul_le hk (x₁ + x₂) (x₃ + x₄)).trans ?_
  have h2 := add_pow_two_mul_le hk x₁ x₂
  have h3 := add_pow_two_mul_le hk x₃ x₄
  have h22 : (2 : ℝ) ^ (2 * k - 1) * 2 ^ (2 * k - 1) = 4 ^ (2 * k - 1) := by
    rw [← mul_pow, show (2 : ℝ) * 2 = 4 by norm_num]
  calc 2 ^ (2 * k - 1) * ((x₁ + x₂) ^ (2 * k) + (x₃ + x₄) ^ (2 * k))
    _ ≤ 2 ^ (2 * k - 1) * (2 ^ (2 * k - 1) * (x₁ ^ (2 * k) + x₂ ^ (2 * k)) +
        2 ^ (2 * k - 1) * (x₃ ^ (2 * k) + x₄ ^ (2 * k))) :=
      mul_le_mul_of_nonneg_left (add_le_add h2 h3) (by positivity)
    _ = (2 ^ (2 * k - 1) * 2 ^ (2 * k - 1)) *
        (x₁ ^ (2 * k) + x₂ ^ (2 * k) + x₃ ^ (2 * k) + x₄ ^ (2 * k)) := by ring
    _ = 4 ^ (2 * k - 1) * (x₁ ^ (2 * k) + x₂ ^ (2 * k) + x₃ ^ (2 * k) + x₄ ^ (2 * k)) := by rw [h22]

lemma abs_id_mul_exp_cosh_sub_le (A'' Atgt D₁' D₂' h : ℝ)
    (hA : A'' - Atgt = (Real.exp h * D₁' + Real.exp (-h) * D₂') / 2) :
    |A'' - Atgt| ≤ Real.cosh h * (|D₁'| + |D₂'|) := by
  have h1 : |A'' - Atgt| ≤ (Real.exp h * |D₁'| + Real.exp (-h) * |D₂'|) / 2 := by
    rw [hA]
    refine (abs_div _ _).trans_le ?_
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    refine div_le_div_of_nonneg_right ?_ (by norm_num)
    calc |Real.exp h * D₁' + Real.exp (-h) * D₂'|
      _ ≤ |Real.exp h * D₁'| + |Real.exp (-h) * D₂'| := abs_add_le _ _
      _ = Real.exp h * |D₁'| + Real.exp (-h) * |D₂'| := by
        rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)]
  refine h1.trans ?_
  have he1 : Real.exp h ≤ 2 * Real.cosh h := by
    rw [Real.cosh_eq]; linarith [Real.exp_pos (-h)]
  have he2 : Real.exp (-h) ≤ 2 * Real.cosh h := by
    rw [Real.cosh_eq]; linarith [Real.exp_pos h]
  calc (Real.exp h * |D₁'| + Real.exp (-h) * |D₂'|) / 2
    _ ≤ (2 * Real.cosh h * |D₁'| + 2 * Real.cosh h * |D₂'|) / 2 := by
      gcongr
    _ = Real.cosh h * (|D₁'| + |D₂'|) := by ring

lemma abs_cosh_diff_le (B' B D₁ D₂ h : ℝ)
    (hB : B' - B = (Real.exp h * D₁ + Real.exp (-h) * D₂) / 2) :
    |B' - B| ≤ Real.cosh h * (|D₁| + |D₂|) :=
  abs_id_mul_exp_cosh_sub_le B' B D₁ D₂ h hB

/-- **Talagrand Corollary 1.7.15, Eq. (1.209): Cavity field tanh approximation.** -/
theorem sk_cavity_field_tanh_approx (β h q : ℝ)
    (hfix : ∫ x : ℝ, Real.tanh (β * Real.sqrt q * x + h) ^ 2 ∂(gaussianReal 0 1) = q)
    (hβ : 4 * β ^ 2 < 1) {k : ℕ} (hk : 1 ≤ k) :
    ∃ K : ℝ, 0 < K ∧ ∀ N : ℕ, 0 < N →
      ∫ g : FinPairs N → ℝ, ∫ y : Fin N → ℝ,
        (((∫ a, Real.sinh (((fun i => (Real.sqrt N)⁻¹ * (β * ((a i : ℤ) : ℝ))) ⬝ᵥ y) + h)
            ∂(Measure.count.tilted (skGibbsEnergy N β h g))) /
          (∫ a, Real.cosh (((fun i => (Real.sqrt N)⁻¹ * (β * ((a i : ℤ) : ℝ))) ⬝ᵥ y) + h)
            ∂(Measure.count.tilted (skGibbsEnergy N β h g)))) -
          Real.tanh (((fun i => (Real.sqrt N)⁻¹ *
            (β *
            ∫ b, ((b i : ℤ) : ℝ)
                ∂(Measure.count.tilted (skGibbsEnergy N β h g)))) ⬝ᵥ y) + h)) ^ (2 * k)
        ∂(Measure.pi fun _ : Fin N => gaussianReal 0 1)
      ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1) ≤ K / (N : ℝ) ^ k := by
  have hU1 : ExpTame (fun x => Real.exp (1 * β * x)) := by
    simp_rw [one_mul]; exact expTame_exp β
  have hU2 : ExpTame (fun x => Real.exp ((-1) * β * x)) := by
    simp_rw [neg_one_mul]; exact expTame_exp (-β)
  have hε1 : (1 : ℝ) ^ 2 = 1 := by norm_num
  have hε2 : (-1 : ℝ) ^ 2 = 1 := by norm_num
  obtain ⟨C₂_1, M_1, K'_1, hC₂_1, hM_1, hK'_1, h_bound1⟩ :=
    sk_gaussian_fluctuation_upper_bound β h q hfix hβ 1 hε1 hk hU1
  obtain ⟨C₂_2, M_2, K'_2, hC₂_2, hM_2, hK'_2, h_bound2⟩ :=
    sk_gaussian_fluctuation_upper_bound β h q hfix hβ (-1) hε2 hk hU2
  set C_k : ℝ := (2 * Real.cosh h) ^ (2 * k) * 2 ^ (2 * k - 1) with hC_k_def
  have hC_k_pos : 0 < C_k := by
    dsimp [C_k]
    have : 0 < Real.cosh h := Real.cosh_pos h
    positivity
  set Bnd_const : ℝ := C_k * (((C₂_1 * K'_1 + M_1) / 2) + ((C₂_2 * K'_2 + M_2) / 2)) + 1
  have hBnd_const_pos : 0 < Bnd_const := by positivity
  refine ⟨Bnd_const, hBnd_const_pos, fun N hN => ?_⟩
  obtain ⟨Upper₁, Bnd₁, h_le1, h_int_inner1, h_upper_bnd1, h_bnd_int1, h_bnd_le1⟩ := h_bound1 N hN
  obtain ⟨Upper₂, Bnd₂, h_le2, h_int_inner2, h_upper_bnd2, h_bnd_int2, h_bnd_le2⟩ := h_bound2 N hN
  set P := Measure.pi fun _ : FinPairs N => gaussianReal 0 1
  set Q := Measure.pi fun _ : Fin N => gaussianReal 0 1
  set Upper := fun g y => C_k * (Upper₁ g y + Upper₂ g y)
  set Bnd := fun g => C_k * (Bnd₁ g + Bnd₂ g)
  have hq := fixedPoint_mem_Icc hfix
  set v : ℝ := Real.sqrt (1 - q)
  have hv : v ^ 2 = 1 - q := Real.sq_sqrt (by linarith [hq.2])
  set E : ℝ := Real.exp (β ^ 2 * (1 - q) / 2) with hE_def
  have hE_ge1 : 1 ≤ E := by
    have : 0 ≤ β ^ 2 * (1 - q) / 2 := by
      have : 0 ≤ 1 - q := by linarith [hq.2]
      positivity
    exact Real.one_le_exp this
  have h_gauss1 : ∫ t, Real.exp (1 * β * (v * t)) ∂(gaussianReal 0 1) = E := by
    rw [integral_exp_scaled_gaussianReal_zero_one]
    congr 1
    calc (1 * β) ^ 2 * v ^ 2 / 2
      _ = (1 ^ 2 * β ^ 2) * (1 - q) / 2 := by rw [hv]; ring
      _ = β ^ 2 * (1 - q) / 2 := by ring
  have h_gauss2 : ∫ t, Real.exp ((-1) * β * (v * t)) ∂(gaussianReal 0 1) = E := by
    rw [integral_exp_scaled_gaussianReal_zero_one]
    congr 1
    calc ((-1) * β) ^ 2 * v ^ 2 / 2
      _ = ((-1) ^ 2 * β ^ 2) * (1 - q) / 2 := by rw [hv]; ring
      _ = β ^ 2 * (1 - q) / 2 := by ring
  have h_pointwise : ∀ g y,
      (((∫ a, Real.sinh (((fun i => (Real.sqrt N)⁻¹ * (β * ((a i : ℤ) : ℝ))) ⬝ᵥ y) + h)
            ∂(Measure.count.tilted (skGibbsEnergy N β h g))) /
          (∫ a, Real.cosh (((fun i => (Real.sqrt N)⁻¹ * (β * ((a i : ℤ) : ℝ))) ⬝ᵥ y) + h)
            ∂(Measure.count.tilted (skGibbsEnergy N β h g)))) -
        Real.tanh (((fun i => (Real.sqrt N)⁻¹ *
          (β *
            ∫ b, ((b i : ℤ) : ℝ)
                ∂(Measure.count.tilted (skGibbsEnergy N β h g)))) ⬝ᵥ y) + h)) ^ (2 * k) ≤
        Upper g y := by
    intro g y
    set f := skGibbsEnergy N β h g
    set μ := Measure.count.tilted f
    set m : Fin N → ℝ := fun i => ∫ b, ((b i : ℤ) : ℝ) ∂μ
    set u : (Fin N → ℤˣ) → ℝ := fun a => ((fun i => (Real.sqrt N)⁻¹ * (β * ((a i : ℤ) : ℝ))) ⬝ᵥ y)
    set Sdot : (Fin N → ℤˣ) → ℝ :=
      fun a => ((fun i => (Real.sqrt N)⁻¹ * (((a i : ℤ) : ℝ) - m i)) ⬝ᵥ y)
    set wm : ℝ := ((fun i => (Real.sqrt N)⁻¹ * (β * m i)) ⬝ᵥ y)
    set A' : ℝ := ∫ a, Real.sinh (u a + h) ∂μ
    set B' : ℝ := ∫ a, Real.cosh (u a + h) ∂μ
    set A : ℝ := Real.sinh (wm + h) * E
    set B : ℝ := Real.cosh (wm + h) * E
    set D₁ : ℝ := (∫ a, Real.exp (u a) ∂μ) - E * Real.exp wm
    set D₂ : ℝ := (∫ a, Real.exp (-u a) ∂μ) - E * Real.exp (-wm)
    have hu_neg : ∀ a, -u a = ((fun i => (Real.sqrt N)⁻¹ * ((-1) * β * ((a i : ℤ) : ℝ))) ⬝ᵥ y) := by
      intro a; rw [dotProduct_neg]
    have hwm_neg : -wm = ((fun i => (Real.sqrt N)⁻¹ * ((-1) * β * m i)) ⬝ᵥ y) := by
      rw [dotProduct_neg]
    have hu1 : ∀ a, ((fun i => (Real.sqrt N)⁻¹ * (1 * β * ((a i : ℤ) : ℝ))) ⬝ᵥ y) = u a := by
      intro a; dsimp [u]; simp only [one_mul]
    have hwm1 : Real.exp ((fun i => (Real.sqrt N)⁻¹ * (1 * β * m i)) ⬝ᵥ y) = Real.exp wm := by
      congr 1; dsimp [wm]; simp only [one_mul]
    have hwm2 : Real.exp ((fun i => (Real.sqrt N)⁻¹ * ((-1) * β * m i)) ⬝ᵥ y) = Real.exp (-wm) := by
      rw [hwm_neg]
    have hD1_eq : D₁ =
        ((∫ a, Real.exp (1 * β * Sdot a) ∂μ) -
          ∫ s, Real.exp (1 * β * (v * s)) ∂(gaussianReal 0 1)) *
          Real.exp ((fun i => (Real.sqrt N)⁻¹ * (1 * β * m i)) ⬝ᵥ y) := by
      have h1 : ∀ a : Fin N → ℤˣ,
          Real.exp (1 * β * Sdot a) *
            Real.exp ((fun i => (Real.sqrt N)⁻¹ * (1 * β * m i)) ⬝ᵥ y) =
          Real.exp (u a) := by
        intro a
        rw [exp_dotProduct_ising_split N β 1 y a m, hu1 a]
      have h2 : ∫ a, Real.exp (u a) ∂μ =
          (∫ a, Real.exp (1 * β * Sdot a) ∂μ) *
            Real.exp ((fun i => (Real.sqrt N)⁻¹ * (1 * β * m i)) ⬝ᵥ y) := by
        simp_rw [← h1, integral_mul_const]
      dsimp [D₁]
      rw [h2, h_gauss1, hwm1]
      ring
    have hD2_eq : D₂ =
        ((∫ a, Real.exp ((-1) * β * Sdot a) ∂μ) -
          ∫ s, Real.exp ((-1) * β * (v * s)) ∂(gaussianReal 0 1)) *
          Real.exp ((fun i => (Real.sqrt N)⁻¹ * ((-1) * β * m i)) ⬝ᵥ y) := by
      have h1 : ∀ a : Fin N → ℤˣ,
          Real.exp ((-1) * β * Sdot a) *
            Real.exp ((fun i => (Real.sqrt N)⁻¹ * ((-1) * β * m i)) ⬝ᵥ y) =
          Real.exp (-u a) := by
        intro a
        rw [hu_neg, exp_dotProduct_ising_split N β (-1) y a m]
      have h2 : ∫ a, Real.exp (-u a) ∂μ =
          (∫ a, Real.exp ((-1) * β * Sdot a) ∂μ) *
            Real.exp ((fun i => (Real.sqrt N)⁻¹ * ((-1) * β * m i)) ⬝ᵥ y) := by
        simp_rw [← h1, integral_mul_const]
      dsimp [D₂]
      rw [h2, h_gauss2, hwm2]
      ring
    have hD1_pow : D₁ ^ (2 * k) ≤ Upper₁ g y := by
      rw [hD1_eq]
      exact h_le1 g y
    have hD2_pow : D₂ ^ (2 * k) ≤ Upper₂ g y := by
      rw [hD2_eq]
      exact h_le2 g y
    have hB'1 : 1 ≤ B' := one_le_integral_cosh μ (fun a => u a + h)
    have hB' : 0 < B' := by linarith
    have hB : 1 ≤ B := by
      dsimp [B]
      calc 1 = 1 * 1 := (mul_one 1).symm
        _ ≤ Real.cosh (wm + h) * E :=
          mul_le_mul (Real.one_le_cosh _) hE_ge1 zero_le_one (by positivity)
    have hA' : |A'| ≤ B' := abs_integral_sinh_le_integral_cosh μ (fun a => u a + h)
    have h_diff_A : A' - A = (Real.exp h * D₁ - Real.exp (-h) * D₂) / 2 := by
      dsimp [A', A, D₁, D₂]
      rw [integral_sinh_add μ u h, sinh_add_eq wm h]
      ring
    have h_diff_B : B' - B = (Real.exp h * D₁ + Real.exp (-h) * D₂) / 2 := by
      dsimp [B', B, D₁, D₂]
      rw [integral_cosh_add μ u h, cosh_add_eq wm h]
      ring
    have h_ratio_bound := abs_div_sub_div_le (A := A) hA' hB' hB
    have hAB_eq : A / B = Real.tanh (wm + h) := by
      dsimp [A, B]
      rw [mul_div_mul_right _ _ (Real.exp_pos _).ne']
      exact (Real.tanh_eq_sinh_div_cosh (wm + h)).symm
    rw [hAB_eq] at h_ratio_bound
    have h_sum_diff := abs_sinh_cosh_diff_le A' A B' B D₁ D₂ h h_diff_A h_diff_B
    rw [abs_sub_comm A A', abs_sub_comm B B'] at h_ratio_bound
    have h_abs_le : |A' / B' - Real.tanh (wm + h)| ≤ 2 * Real.cosh h * (|D₁| + |D₂|) :=
      h_ratio_bound.trans h_sum_diff
    have h_pow_le : (|A' / B' - Real.tanh (wm + h)|) ^ (2 * k) ≤
        (2 * Real.cosh h) ^ (2 * k) * 2 ^ (2 * k - 1) * (D₁ ^ (2 * k) + D₂ ^ (2 * k)) := by
      calc (|A' / B' - Real.tanh (wm + h)|) ^ (2 * k)
        _ ≤ (2 * Real.cosh h * (|D₁| + |D₂|)) ^ (2 * k) :=
          pow_le_pow_left₀ (abs_nonneg _) h_abs_le (2 * k)
        _ = (2 * Real.cosh h) ^ (2 * k) * (|D₁| + |D₂|) ^ (2 * k) := mul_pow _ _ _
        _ ≤ (2 * Real.cosh h) ^ (2 * k) * (2 ^ (2 * k - 1) * (|D₁| ^ (2 * k) + |D₂| ^ (2 * k))) :=
          mul_le_mul_of_nonneg_left (add_pow_two_mul_le hk |D₁| |D₂|) (by positivity)
        _ = (2 * Real.cosh h) ^ (2 * k) * 2 ^ (2 * k - 1) * (D₁ ^ (2 * k) + D₂ ^ (2 * k)) := by
          rw [Even.pow_abs ⟨k, by ring⟩ D₁, Even.pow_abs ⟨k, by ring⟩ D₂]
          ring
    have h_pow_eq : (A' / B' - Real.tanh (wm + h)) ^ (2 * k) =
        (|A' / B' - Real.tanh (wm + h)|) ^ (2 * k) := (Even.pow_abs ⟨k, by ring⟩ _).symm
    rw [h_pow_eq]
    refine h_pow_le.trans ?_
    dsimp [Upper, C_k]
    have h_add_le : D₁ ^ (2 * k) + D₂ ^ (2 * k) ≤ Upper₁ g y + Upper₂ g y :=
      add_le_add hD1_pow hD2_pow
    exact mul_le_mul_of_nonneg_left h_add_le (by positivity)
  have h_int_inner : ∀ g, Integrable (Upper g) Q := fun g =>
    ((h_int_inner1 g).add (h_int_inner2 g)).const_mul C_k
  have h_upper_bnd : ∀ g, ∫ y, Upper g y ∂Q ≤ Bnd g := fun g => by
    dsimp [Upper, Bnd]
    rw [integral_const_mul, integral_add (h_int_inner1 g) (h_int_inner2 g)]
    exact mul_le_mul_of_nonneg_left (add_le_add (h_upper_bnd1 g) (h_upper_bnd2 g)) hC_k_pos.le
  have h_inner : ∀ g, ∫ y : Fin N → ℝ,
      (((∫ a, Real.sinh (((fun i => (Real.sqrt N)⁻¹ * (β * ((a i : ℤ) : ℝ))) ⬝ᵥ y) + h)
            ∂(Measure.count.tilted (skGibbsEnergy N β h g))) /
          (∫ a, Real.cosh (((fun i => (Real.sqrt N)⁻¹ * (β * ((a i : ℤ) : ℝ))) ⬝ᵥ y) + h)
            ∂(Measure.count.tilted (skGibbsEnergy N β h g)))) -
        Real.tanh (((fun i => (Real.sqrt N)⁻¹ *
          (β *
            ∫ b, ((b i : ℤ) : ℝ)
                ∂(Measure.count.tilted (skGibbsEnergy N β h g)))) ⬝ᵥ y) + h)) ^ (2 * k) ∂Q ≤
        Bnd g :=
    fun g => (integral_mono_of_nonneg
      (ae_of_all _ fun y => Even.pow_nonneg ⟨k, by ring⟩ _)
      (h_int_inner g) (ae_of_all _ fun y => h_pointwise g y)).trans (h_upper_bnd g)
  have hnonneg : ∀ g, 0 ≤ ∫ y : Fin N → ℝ,
      (((∫ a, Real.sinh (((fun i => (Real.sqrt N)⁻¹ * (β * ((a i : ℤ) : ℝ))) ⬝ᵥ y) + h)
            ∂(Measure.count.tilted (skGibbsEnergy N β h g))) /
          (∫ a, Real.cosh (((fun i => (Real.sqrt N)⁻¹ * (β * ((a i : ℤ) : ℝ))) ⬝ᵥ y) + h)
            ∂(Measure.count.tilted (skGibbsEnergy N β h g)))) -
        Real.tanh (((fun i => (Real.sqrt N)⁻¹ *
          (β *
            ∫ b, ((b i : ℤ) : ℝ)
                ∂(Measure.count.tilted (skGibbsEnergy N β h g)))) ⬝ᵥ y) + h)) ^ (2 * k) ∂Q :=
    fun g => integral_nonneg fun y => Even.pow_nonneg ⟨k, by ring⟩ _
  have h_bnd_int : Integrable Bnd P :=
    (h_bnd_int1.add h_bnd_int2).const_mul C_k
  have h_outer := integral_mono_of_nonneg (ae_of_all _ hnonneg) h_bnd_int (ae_of_all _ h_inner)
  have h_bnd_outer : ∫ g, Bnd g ∂P ≤
      (C_k * (((C₂_1 * K'_1 + M_1) / 2) + ((C₂_2 * K'_2 + M_2) / 2))) / (N : ℝ) ^ k := by
    dsimp [Bnd]
    rw [integral_const_mul, integral_add h_bnd_int1 h_bnd_int2]
    calc C_k * ((∫ g, Bnd₁ g ∂P) + ∫ g, Bnd₂ g ∂P)
      _ ≤ C_k * ((((C₂_1 * K'_1 + M_1) / 2) / (N : ℝ) ^ k) +
          (((C₂_2 * K'_2 + M_2) / 2) / (N : ℝ) ^ k)) :=
        mul_le_mul_of_nonneg_left (add_le_add h_bnd_le1 h_bnd_le2) hC_k_pos.le
      _ = (C_k * (((C₂_1 * K'_1 + M_1) / 2) + ((C₂_2 * K'_2 + M_2) / 2))) / (N : ℝ) ^ k := by ring
  refine h_outer.trans (h_bnd_outer.trans ?_)
  dsimp [Bnd_const]
  gcongr
  linarith

/-- **Talagrand Corollary 1.7.15, Eq. (1.210): Cavity field reaction term approximation.** -/
theorem sk_cavity_field_reaction_approx (β h q : ℝ)
    (hfix : ∫ x : ℝ, Real.tanh (β * Real.sqrt q * x + h) ^ 2 ∂(gaussianReal 0 1) = q)
    (hβ : 4 * β ^ 2 < 1) {k : ℕ} (hk : 1 ≤ k) :
    ∃ K : ℝ, 0 < K ∧ ∀ N : ℕ, 0 < N →
      ∫ g : FinPairs N → ℝ, ∫ y : Fin N → ℝ,
        (((∫ a, ((fun i => (Real.sqrt N)⁻¹ *
              (((a i : ℤ) : ℝ) -
              ∫ b, ((b i : ℤ) : ℝ) ∂(Measure.count.tilted (skGibbsEnergy N β h g)))) ⬝ᵥ y) *
            Real.cosh (((fun i => (Real.sqrt N)⁻¹ * (β * ((a i : ℤ) : ℝ))) ⬝ᵥ y) + h)
            ∂(Measure.count.tilted (skGibbsEnergy N β h g))) /
          (∫ a, Real.cosh (((fun i => (Real.sqrt N)⁻¹ * (β * ((a i : ℤ) : ℝ))) ⬝ᵥ y) + h)
            ∂(Measure.count.tilted (skGibbsEnergy N β h g)))) -
          β * (1 - q) *
            ((∫ a, Real.sinh (((fun i => (Real.sqrt N)⁻¹ * (β * ((a i : ℤ) : ℝ))) ⬝ᵥ y) + h)
                ∂(Measure.count.tilted (skGibbsEnergy N β h g))) /
              (∫ a, Real.cosh (((fun i => (Real.sqrt N)⁻¹ * (β * ((a i : ℤ) : ℝ))) ⬝ᵥ y) + h)
                ∂(Measure.count.tilted (skGibbsEnergy N β h g))))) ^ (2 * k)
        ∂(Measure.pi fun _ : Fin N => gaussianReal 0 1)
      ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1) ≤ K / (N : ℝ) ^ k := by
  have hU1' : ExpTame (fun x => x * Real.exp (1 * β * x)) := by
    simp_rw [one_mul]; exact expTame_id_mul_exp β
  have hU2' : ExpTame (fun x => x * Real.exp ((-1) * β * x)) := by
    simp_rw [neg_one_mul]; exact expTame_id_mul_exp (-β)
  have hU1 : ExpTame (fun x => Real.exp (1 * β * x)) := by
    simp_rw [one_mul]; exact expTame_exp β
  have hU2 : ExpTame (fun x => Real.exp ((-1) * β * x)) := by
    simp_rw [neg_one_mul]; exact expTame_exp (-β)
  have hε1 : (1 : ℝ) ^ 2 = 1 := by norm_num
  have hε2 : (-1 : ℝ) ^ 2 = 1 := by norm_num
  obtain ⟨C₂_1', M_1', K'_1', hC₂_1', hM_1', hK'_1', h_bound1'⟩ :=
    sk_gaussian_fluctuation_upper_bound β h q hfix hβ 1 hε1 hk hU1'
  obtain ⟨C₂_2', M_2', K'_2', hC₂_2', hM_2', hK'_2', h_bound2'⟩ :=
    sk_gaussian_fluctuation_upper_bound β h q hfix hβ (-1) hε2 hk hU2'
  obtain ⟨C₂_1, M_1, K'_1, hC₂_1, hM_1, hK'_1, h_bound1⟩ :=
    sk_gaussian_fluctuation_upper_bound β h q hfix hβ 1 hε1 hk hU1
  obtain ⟨C₂_2, M_2, K'_2, hC₂_2, hM_2, hK'_2, h_bound2⟩ :=
    sk_gaussian_fluctuation_upper_bound β h q hfix hβ (-1) hε2 hk hU2
  set C_k : ℝ := (3 * Real.cosh h) ^ (2 * k) * 4 ^ (2 * k - 1) with hC_k_def
  have hC_k_pos : 0 < C_k := by
    dsimp [C_k]
    have : 0 < Real.cosh h := Real.cosh_pos h
    positivity
  set Bnd_const : ℝ := C_k * (((C₂_1' * K'_1' + M_1') / 2) + ((C₂_2' * K'_2' + M_2') / 2) +
    ((C₂_1 * K'_1 + M_1) / 2) + ((C₂_2 * K'_2 + M_2) / 2)) + 1
  have hBnd_const_pos : 0 < Bnd_const := by positivity
  refine ⟨Bnd_const, hBnd_const_pos, fun N hN => ?_⟩
  obtain ⟨Upper₁', Bnd₁', h_le1', h_int_inner1', h_upper_bnd1', h_bnd_int1', h_bnd_le1'⟩ :=
    h_bound1' N hN
  obtain ⟨Upper₂', Bnd₂', h_le2', h_int_inner2', h_upper_bnd2', h_bnd_int2', h_bnd_le2'⟩ :=
    h_bound2' N hN
  obtain ⟨Upper₁, Bnd₁, h_le1, h_int_inner1, h_upper_bnd1, h_bnd_int1, h_bnd_le1⟩ := h_bound1 N hN
  obtain ⟨Upper₂, Bnd₂, h_le2, h_int_inner2, h_upper_bnd2, h_bnd_int2, h_bnd_le2⟩ := h_bound2 N hN
  set P := Measure.pi fun _ : FinPairs N => gaussianReal 0 1
  set Q := Measure.pi fun _ : Fin N => gaussianReal 0 1
  set Upper := fun g y => C_k * ((Upper₁' g y + Upper₂' g y) + (Upper₁ g y + Upper₂ g y))
  set Bnd := fun g => C_k * ((Bnd₁' g + Bnd₂' g) + (Bnd₁ g + Bnd₂ g))
  have hq := fixedPoint_mem_Icc hfix
  set v : ℝ := Real.sqrt (1 - q)
  have hv : v ^ 2 = 1 - q := Real.sq_sqrt (by linarith [hq.2])
  set E : ℝ := Real.exp (β ^ 2 * (1 - q) / 2) with hE_def
  have hE_ge1 : 1 ≤ E := by
    have : 0 ≤ β ^ 2 * (1 - q) / 2 := by
      have : 0 ≤ 1 - q := by linarith [hq.2]
      positivity
    exact Real.one_le_exp this
  have h_gauss1' : ∫ t, (v * t) * Real.exp (1 * β * (v * t)) ∂(gaussianReal 0 1) =
      β * (1 - q) * E := by
    rw [integral_id_mul_exp_scaled_gaussianReal_zero_one, hv]
    have he : Real.exp ((1 * β) ^ 2 * (1 - q) / 2) = E := by
      congr 1; ring
    rw [he]
    ring
  have h_gauss2' : ∫ t, (v * t) * Real.exp ((-1) * β * (v * t)) ∂(gaussianReal 0 1) =
      - (β * (1 - q) * E) := by
    rw [integral_id_mul_exp_scaled_gaussianReal_zero_one, hv]
    have he : Real.exp (((-1) * β) ^ 2 * (1 - q) / 2) = E := by
      congr 1; ring
    rw [he]
    ring
  have h_gauss1 : ∫ t, Real.exp (1 * β * (v * t)) ∂(gaussianReal 0 1) = E := by
    rw [integral_exp_scaled_gaussianReal_zero_one]
    congr 1
    calc (1 * β) ^ 2 * v ^ 2 / 2
      _ = (1 ^ 2 * β ^ 2) * (1 - q) / 2 := by rw [hv]; ring
      _ = β ^ 2 * (1 - q) / 2 := by ring
  have h_gauss2 : ∫ t, Real.exp ((-1) * β * (v * t)) ∂(gaussianReal 0 1) = E := by
    rw [integral_exp_scaled_gaussianReal_zero_one]
    congr 1
    calc ((-1) * β) ^ 2 * v ^ 2 / 2
      _ = ((-1) ^ 2 * β ^ 2) * (1 - q) / 2 := by rw [hv]; ring
      _ = β ^ 2 * (1 - q) / 2 := by ring
  have h_pointwise : ∀ g y,
      (((∫ a, ((fun i => (Real.sqrt N)⁻¹ *
              (((a i : ℤ) : ℝ) -
              ∫ b, ((b i : ℤ) : ℝ) ∂(Measure.count.tilted (skGibbsEnergy N β h g)))) ⬝ᵥ y) *
            Real.cosh (((fun i => (Real.sqrt N)⁻¹ * (β * ((a i : ℤ) : ℝ))) ⬝ᵥ y) + h)
            ∂(Measure.count.tilted (skGibbsEnergy N β h g))) /
          (∫ a, Real.cosh (((fun i => (Real.sqrt N)⁻¹ * (β * ((a i : ℤ) : ℝ))) ⬝ᵥ y) + h)
            ∂(Measure.count.tilted (skGibbsEnergy N β h g)))) -
        β * (1 - q) *
          ((∫ a, Real.sinh (((fun i => (Real.sqrt N)⁻¹ * (β * ((a i : ℤ) : ℝ))) ⬝ᵥ y) + h)
              ∂(Measure.count.tilted (skGibbsEnergy N β h g))) /
            (∫ a, Real.cosh (((fun i => (Real.sqrt N)⁻¹ * (β * ((a i : ℤ) : ℝ))) ⬝ᵥ y) + h)
              ∂(Measure.count.tilted (skGibbsEnergy N β h g))))) ^ (2 * k) ≤ Upper g y := by
    intro g y
    set f := skGibbsEnergy N β h g
    set μ := Measure.count.tilted f
    set m : Fin N → ℝ := fun i => ∫ b, ((b i : ℤ) : ℝ) ∂μ
    set u : (Fin N → ℤˣ) → ℝ := fun a => ((fun i => (Real.sqrt N)⁻¹ * (β * ((a i : ℤ) : ℝ))) ⬝ᵥ y)
    set Sdot : (Fin N → ℤˣ) → ℝ :=
      fun a => ((fun i => (Real.sqrt N)⁻¹ * (((a i : ℤ) : ℝ) - m i)) ⬝ᵥ y)
    set wm : ℝ := ((fun i => (Real.sqrt N)⁻¹ * (β * m i)) ⬝ᵥ y)
    set A'' : ℝ := ∫ a, Sdot a * Real.cosh (u a + h) ∂μ
    set B' : ℝ := ∫ a, Real.cosh (u a + h) ∂μ
    set A' : ℝ := ∫ a, Real.sinh (u a + h) ∂μ
    set Atgt : ℝ := β * (1 - q) * E * Real.sinh (wm + h)
    set B : ℝ := Real.cosh (wm + h) * E
    set D₁' : ℝ := (∫ a, Sdot a * Real.exp (u a) ∂μ) - β * (1 - q) * E * Real.exp wm
    set D₂' : ℝ := (∫ a, Sdot a * Real.exp (-u a) ∂μ) - (- (β * (1 - q) * E * Real.exp (-wm)))
    set D₁ : ℝ := (∫ a, Real.exp (u a) ∂μ) - E * Real.exp wm
    set D₂ : ℝ := (∫ a, Real.exp (-u a) ∂μ) - E * Real.exp (-wm)
    have hu_neg : ∀ a, -u a = ((fun i => (Real.sqrt N)⁻¹ * ((-1) * β * ((a i : ℤ) : ℝ))) ⬝ᵥ y) := by
      intro a; rw [dotProduct_neg]
    have hwm_neg : -wm = ((fun i => (Real.sqrt N)⁻¹ * ((-1) * β * m i)) ⬝ᵥ y) := by
      rw [dotProduct_neg]
    have hu1 : ∀ a, ((fun i => (Real.sqrt N)⁻¹ * (1 * β * ((a i : ℤ) : ℝ))) ⬝ᵥ y) = u a := by
      intro a; dsimp [u]; simp only [one_mul]
    have hwm1 : Real.exp ((fun i => (Real.sqrt N)⁻¹ * (1 * β * m i)) ⬝ᵥ y) = Real.exp wm := by
      congr 1; dsimp [wm]; simp only [one_mul]
    have hwm2 : Real.exp ((fun i => (Real.sqrt N)⁻¹ * ((-1) * β * m i)) ⬝ᵥ y) = Real.exp (-wm) := by
      rw [hwm_neg]
    have hD1'_eq : D₁' =
        ((∫ a, Sdot a * Real.exp (1 * β * Sdot a) ∂μ) -
          ∫ s, (v * s) * Real.exp (1 * β * (v * s)) ∂(gaussianReal 0 1)) *
          Real.exp ((fun i => (Real.sqrt N)⁻¹ * (1 * β * m i)) ⬝ᵥ y) := by
      have h1 : ∀ a : Fin N → ℤˣ,
          (Sdot a * Real.exp (1 * β * Sdot a)) *
            Real.exp ((fun i => (Real.sqrt N)⁻¹ * (1 * β * m i)) ⬝ᵥ y) =
          Sdot a * Real.exp (u a) := by
        intro a
        rw [mul_assoc, exp_dotProduct_ising_split N β 1 y a m, hu1 a]
      have h2 : ∫ a, Sdot a * Real.exp (u a) ∂μ =
          (∫ a, Sdot a * Real.exp (1 * β * Sdot a) ∂μ) *
            Real.exp ((fun i => (Real.sqrt N)⁻¹ * (1 * β * m i)) ⬝ᵥ y) := by
        simp_rw [← h1, integral_mul_const]
      dsimp [D₁']
      rw [h2, h_gauss1', hwm1]
      ring
    have hD2'_eq : D₂' =
        ((∫ a, Sdot a * Real.exp ((-1) * β * Sdot a) ∂μ) -
          ∫ s, (v * s) * Real.exp ((-1) * β * (v * s)) ∂(gaussianReal 0 1)) *
          Real.exp ((fun i => (Real.sqrt N)⁻¹ * ((-1) * β * m i)) ⬝ᵥ y) := by
      have h1 : ∀ a : Fin N → ℤˣ,
          (Sdot a * Real.exp ((-1) * β * Sdot a)) *
            Real.exp ((fun i => (Real.sqrt N)⁻¹ * ((-1) * β * m i)) ⬝ᵥ y) =
          Sdot a * Real.exp (-u a) := by
        intro a
        rw [mul_assoc, hu_neg, exp_dotProduct_ising_split N β (-1) y a m]
      have h2 : ∫ a, Sdot a * Real.exp (-u a) ∂μ =
          (∫ a, Sdot a * Real.exp ((-1) * β * Sdot a) ∂μ) *
            Real.exp ((fun i => (Real.sqrt N)⁻¹ * ((-1) * β * m i)) ⬝ᵥ y) := by
        simp_rw [← h1, integral_mul_const]
      dsimp [D₂']
      rw [h2, h_gauss2', hwm2]
      ring
    have hD1_eq : D₁ =
        ((∫ a, Real.exp (1 * β * Sdot a) ∂μ) -
          ∫ s, Real.exp (1 * β * (v * s)) ∂(gaussianReal 0 1)) *
          Real.exp ((fun i => (Real.sqrt N)⁻¹ * (1 * β * m i)) ⬝ᵥ y) := by
      have h1 : ∀ a : Fin N → ℤˣ,
          Real.exp (1 * β * Sdot a) *
            Real.exp ((fun i => (Real.sqrt N)⁻¹ * (1 * β * m i)) ⬝ᵥ y) =
          Real.exp (u a) := by
        intro a
        rw [exp_dotProduct_ising_split N β 1 y a m, hu1 a]
      have h2 : ∫ a, Real.exp (u a) ∂μ =
          (∫ a, Real.exp (1 * β * Sdot a) ∂μ) *
            Real.exp ((fun i => (Real.sqrt N)⁻¹ * (1 * β * m i)) ⬝ᵥ y) := by
        simp_rw [← h1, integral_mul_const]
      dsimp [D₁]
      rw [h2, h_gauss1, hwm1]
      ring
    have hD2_eq : D₂ =
        ((∫ a, Real.exp ((-1) * β * Sdot a) ∂μ) -
          ∫ s, Real.exp ((-1) * β * (v * s)) ∂(gaussianReal 0 1)) *
          Real.exp ((fun i => (Real.sqrt N)⁻¹ * ((-1) * β * m i)) ⬝ᵥ y) := by
      have h1 : ∀ a : Fin N → ℤˣ,
          Real.exp ((-1) * β * Sdot a) *
            Real.exp ((fun i => (Real.sqrt N)⁻¹ * ((-1) * β * m i)) ⬝ᵥ y) =
          Real.exp (-u a) := by
        intro a
        rw [hu_neg, exp_dotProduct_ising_split N β (-1) y a m]
      have h2 : ∫ a, Real.exp (-u a) ∂μ =
          (∫ a, Real.exp ((-1) * β * Sdot a) ∂μ) *
            Real.exp ((fun i => (Real.sqrt N)⁻¹ * ((-1) * β * m i)) ⬝ᵥ y) := by
        simp_rw [← h1, integral_mul_const]
      dsimp [D₂]
      rw [h2, h_gauss2, hwm2]
      ring
    have hD1'_pow : D₁' ^ (2 * k) ≤ Upper₁' g y := by
      rw [hD1'_eq]
      exact h_le1' g y
    have hD2'_pow : D₂' ^ (2 * k) ≤ Upper₂' g y := by
      rw [hD2'_eq]
      exact h_le2' g y
    have hD1_pow : D₁ ^ (2 * k) ≤ Upper₁ g y := by
      rw [hD1_eq]
      exact h_le1 g y
    have hD2_pow : D₂ ^ (2 * k) ≤ Upper₂ g y := by
      rw [hD2_eq]
      exact h_le2 g y
    have hB'1 : 1 ≤ B' := one_le_integral_cosh μ (fun a => u a + h)
    have hB' : 0 < B' := by linarith
    have hB : 1 ≤ B := by
      dsimp [B]
      calc 1 = 1 * 1 := (mul_one 1).symm
        _ ≤ Real.cosh (wm + h) * E :=
          mul_le_mul (Real.one_le_cosh _) hE_ge1 zero_le_one (by positivity)
    have hB_pos : 0 < B := by linarith
    have hAtgt_div_B : Atgt / B = β * (1 - q) * Real.tanh (wm + h) := by
      dsimp [Atgt, B]
      calc β * (1 - q) * E * Real.sinh (wm + h) / (Real.cosh (wm + h) * E)
        _ = (β * (1 - q) * Real.sinh (wm + h) * E) / (Real.cosh (wm + h) * E) := by ring
        _ = (β * (1 - q) * Real.sinh (wm + h)) / Real.cosh (wm + h) :=
          mul_div_mul_right _ _ (Real.exp_pos _).ne'
        _ = β * (1 - q) * (Real.sinh (wm + h) / Real.cosh (wm + h)) := by ring
        _ = β * (1 - q) * Real.tanh (wm + h) := by rw [Real.tanh_eq_sinh_div_cosh]
    have h_beta_le : |β * (1 - q)| ≤ 1 := abs_beta_one_sub_q_le hβ hq
    have h_ratio_le : |Atgt / B| ≤ 1 := by
      rw [hAtgt_div_B, abs_mul]
      calc |β * (1 - q)| * |Real.tanh (wm + h)|
        _ ≤ 1 * 1 := mul_le_mul h_beta_le (Real.abs_tanh_lt_one _).le (abs_nonneg _) zero_le_one
        _ = 1 := by norm_num
    have h_diff_Atgt : A'' - Atgt = (Real.exp h * D₁' + Real.exp (-h) * D₂') / 2 := by
      dsimp [A'', Atgt, D₁', D₂']
      have heq_cosh : ∀ a, Sdot a * Real.cosh (u a + h) =
          (Real.exp h * (Sdot a * Real.exp (u a)) +
            Real.exp (-h) * (Sdot a * Real.exp (-u a))) / 2 := by
        intro a; rw [cosh_add_eq]; ring
      simp_rw [heq_cosh]
      rw [integral_div, integral_add Integrable.of_finite Integrable.of_finite,
          integral_const_mul, integral_const_mul, sinh_add_eq wm h]
      ring
    have h_diff_B : B' - B = (Real.exp h * D₁ + Real.exp (-h) * D₂) / 2 := by
      dsimp [B', B, D₁, D₂]
      rw [integral_cosh_add μ u h, cosh_add_eq wm h]
      ring
    have h_sub_Atgt : |A'' - Atgt| ≤ Real.cosh h * (|D₁'| + |D₂'|) :=
      abs_id_mul_exp_cosh_sub_le A'' Atgt D₁' D₂' h h_diff_Atgt
    have h_sub_B : |B' - B| ≤ Real.cosh h * (|D₁| + |D₂|) :=
      abs_cosh_diff_le B' B D₁ D₂ h h_diff_B
    have h_denom_bound := abs_div_sub_div_le_of_denom_ge (A' := A'') hB' hB_pos h_ratio_le
    have h_inv_le1 : (B')⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hB'1
    have h_first_term : |A'' / B' - β * (1 - q) * Real.tanh (wm + h)| ≤
        Real.cosh h * (|D₁'| + |D₂'| + |D₁| + |D₂|) := by
      rw [← hAtgt_div_B]
      calc |A'' / B' - Atgt / B|
        _ ≤ (B')⁻¹ * (|A'' - Atgt| + 1 * |B' - B|) := h_denom_bound
        _ ≤ 1 * (|A'' - Atgt| + 1 * |B' - B|) :=
          mul_le_mul_of_nonneg_right h_inv_le1 (by positivity)
        _ = |A'' - Atgt| + |B' - B| := by ring
        _ ≤ Real.cosh h * (|D₁'| + |D₂'|) + Real.cosh h * (|D₁| + |D₂|) :=
          add_le_add h_sub_Atgt h_sub_B
        _ = Real.cosh h * (|D₁'| + |D₂'| + |D₁| + |D₂|) := by ring
    have hA' : |A'| ≤ B' := abs_integral_sinh_le_integral_cosh μ (fun a => u a + h)
    have h_diff_A : A' - (Real.sinh (wm + h) * E) = (Real.exp h * D₁ - Real.exp (-h) * D₂) / 2 := by
      dsimp [A', D₁, D₂]
      rw [integral_sinh_add μ u h, sinh_add_eq wm h]
      ring
    have h_ratio_bound := abs_div_sub_div_le (A := Real.sinh (wm + h) * E) hA' hB' hB
    have hAB_eq : (Real.sinh (wm + h) * E) / B = Real.tanh (wm + h) := by
      dsimp [B]
      rw [mul_div_mul_right _ _ (Real.exp_pos _).ne']
      exact (Real.tanh_eq_sinh_div_cosh (wm + h)).symm
    rw [hAB_eq] at h_ratio_bound
    have h_sum_diff := abs_sinh_cosh_diff_le A' (Real.sinh (wm + h) * E)
      B' B D₁ D₂ h h_diff_A h_diff_B
    rw [abs_sub_comm (Real.sinh (wm + h) * E) A', abs_sub_comm B B'] at h_ratio_bound
    have h_second_term : |A' / B' - Real.tanh (wm + h)| ≤ 2 * Real.cosh h * (|D₁| + |D₂|) :=
      h_ratio_bound.trans h_sum_diff
    have h_decomp : A'' / B' - β * (1 - q) * (A' / B') =
        (A'' / B' - β * (1 - q) * Real.tanh (wm + h)) -
          β * (1 - q) * (A' / B' - Real.tanh (wm + h)) := by ring
    have h_total_abs : |A'' / B' - β * (1 - q) * (A' / B')| ≤
        3 * Real.cosh h * (|D₁'| + |D₂'| + |D₁| + |D₂|) := by
      rw [h_decomp]
      refine (abs_sub _ _).trans ?_
      rw [abs_mul]
      have h_sec : |β * (1 - q)| * |A' / B' - Real.tanh (wm + h)| ≤
          2 * Real.cosh h * (|D₁| + |D₂|) := by
        calc |β * (1 - q)| * |A' / B' - Real.tanh (wm + h)|
          _ ≤ 1 * (2 * Real.cosh h * (|D₁| + |D₂|)) :=
            mul_le_mul h_beta_le h_second_term (abs_nonneg _) zero_le_one
          _ = 2 * Real.cosh h * (|D₁| + |D₂|) := by ring
      have h_bound_step : Real.cosh h * (|D₁'| + |D₂'| + |D₁| + |D₂|) +
          2 * Real.cosh h * (|D₁| + |D₂|) ≤
          3 * Real.cosh h * (|D₁'| + |D₂'| + |D₁| + |D₂|) := by
        have h_step : Real.cosh h * (|D₁'| + |D₂'|) ≤ 3 * Real.cosh h * (|D₁'| + |D₂'|) := by
          calc Real.cosh h * (|D₁'| + |D₂'|) = 1 * (Real.cosh h * (|D₁'| + |D₂'|)) := by ring
            _ ≤ 3 * (Real.cosh h * (|D₁'| + |D₂'|)) := by gcongr; norm_num
            _ = 3 * Real.cosh h * (|D₁'| + |D₂'|) := by ring
        linarith
      exact (add_le_add h_first_term h_sec).trans h_bound_step
    have h_pow_le : (|A'' / B' - β * (1 - q) * (A' / B')|) ^ (2 * k) ≤
        (3 * Real.cosh h) ^ (2 * k) * 4 ^ (2 * k - 1) *
          (D₁' ^ (2 * k) + D₂' ^ (2 * k) + D₁ ^ (2 * k) + D₂ ^ (2 * k)) := by
      calc (|A'' / B' - β * (1 - q) * (A' / B')|) ^ (2 * k)
        _ ≤ (3 * Real.cosh h * (|D₁'| + |D₂'| + |D₁| + |D₂|)) ^ (2 * k) :=
          pow_le_pow_left₀ (abs_nonneg _) h_total_abs (2 * k)
        _ = (3 * Real.cosh h) ^ (2 * k) * (|D₁'| + |D₂'| + |D₁| + |D₂|) ^ (2 * k) := mul_pow _ _ _
        _ ≤ (3 * Real.cosh h) ^ (2 * k) *
            (4 ^ (2 * k - 1) *
              (|D₁'| ^ (2 * k) + |D₂'| ^ (2 * k) + |D₁| ^ (2 * k) + |D₂| ^ (2 * k))) :=
          mul_le_mul_of_nonneg_left
            (add_pow_four_two_mul_le hk |D₁'| |D₂'| |D₁| |D₂|) (by positivity)
        _ = (3 * Real.cosh h) ^ (2 * k) * 4 ^ (2 * k - 1) *
            (D₁' ^ (2 * k) + D₂' ^ (2 * k) + D₁ ^ (2 * k) + D₂ ^ (2 * k)) := by
          rw [Even.pow_abs ⟨k, by ring⟩ D₁', Even.pow_abs ⟨k, by ring⟩ D₂',
              Even.pow_abs ⟨k, by ring⟩ D₁, Even.pow_abs ⟨k, by ring⟩ D₂]
          ring
    have h_pow_eq : (A'' / B' - β * (1 - q) * (A' / B')) ^ (2 * k) =
        (|A'' / B' - β * (1 - q) * (A' / B')|) ^ (2 * k) := (Even.pow_abs ⟨k, by ring⟩ _).symm
    rw [h_pow_eq]
    refine h_pow_le.trans ?_
    dsimp [Upper, C_k]
    have h_add_le : D₁' ^ (2 * k) + D₂' ^ (2 * k) + D₁ ^ (2 * k) + D₂ ^ (2 * k) ≤
        (Upper₁' g y + Upper₂' g y) + (Upper₁ g y + Upper₂ g y) := by
      rw [show D₁' ^ (2 * k) + D₂' ^ (2 * k) + D₁ ^ (2 * k) + D₂ ^ (2 * k) =
          (D₁' ^ (2 * k) + D₂' ^ (2 * k)) + (D₁ ^ (2 * k) + D₂ ^ (2 * k)) by ring]
      exact add_le_add (add_le_add hD1'_pow hD2'_pow) (add_le_add hD1_pow hD2_pow)
    exact mul_le_mul_of_nonneg_left h_add_le (by positivity)
  have h_int_inner : ∀ g, Integrable (Upper g) Q := fun g =>
    (((h_int_inner1' g).add (h_int_inner2' g)).add
      ((h_int_inner1 g).add (h_int_inner2 g))).const_mul C_k
  have h_upper_bnd : ∀ g, ∫ y, Upper g y ∂Q ≤ Bnd g := fun g => by
    dsimp [Upper, Bnd]
    rw [integral_const_mul]
    have h1 : ∫ y, (Upper₁' g y + Upper₂' g y) + (Upper₁ g y + Upper₂ g y) ∂Q =
        (∫ y, Upper₁' g y + Upper₂' g y ∂Q) + (∫ y, Upper₁ g y + Upper₂ g y ∂Q) :=
      integral_add ((h_int_inner1' g).add (h_int_inner2' g)) ((h_int_inner1 g).add (h_int_inner2 g))
    have h2 : ∫ y, Upper₁' g y + Upper₂' g y ∂Q = (∫ y, Upper₁' g y ∂Q) + ∫ y, Upper₂' g y ∂Q :=
      integral_add (h_int_inner1' g) (h_int_inner2' g)
    have h3 : ∫ y, Upper₁ g y + Upper₂ g y ∂Q = (∫ y, Upper₁ g y ∂Q) + ∫ y, Upper₂ g y ∂Q :=
      integral_add (h_int_inner1 g) (h_int_inner2 g)
    rw [h1, h2, h3]
    exact mul_le_mul_of_nonneg_left
      (add_le_add (add_le_add (h_upper_bnd1' g) (h_upper_bnd2' g))
        (add_le_add (h_upper_bnd1 g) (h_upper_bnd2 g))) hC_k_pos.le
  have h_inner : ∀ g, ∫ y : Fin N → ℝ,
      (((∫ a, ((fun i => (Real.sqrt N)⁻¹ *
              (((a i : ℤ) : ℝ) -
              ∫ b, ((b i : ℤ) : ℝ) ∂(Measure.count.tilted (skGibbsEnergy N β h g)))) ⬝ᵥ y) *
            Real.cosh (((fun i => (Real.sqrt N)⁻¹ * (β * ((a i : ℤ) : ℝ))) ⬝ᵥ y) + h)
            ∂(Measure.count.tilted (skGibbsEnergy N β h g))) /
          (∫ a, Real.cosh (((fun i => (Real.sqrt N)⁻¹ * (β * ((a i : ℤ) : ℝ))) ⬝ᵥ y) + h)
            ∂(Measure.count.tilted (skGibbsEnergy N β h g)))) -
        β * (1 - q) *
          ((∫ a, Real.sinh (((fun i => (Real.sqrt N)⁻¹ * (β * ((a i : ℤ) : ℝ))) ⬝ᵥ y) + h)
              ∂(Measure.count.tilted (skGibbsEnergy N β h g))) /
            (∫ a, Real.cosh (((fun i => (Real.sqrt N)⁻¹ * (β * ((a i : ℤ) : ℝ))) ⬝ᵥ y) + h)
              ∂(Measure.count.tilted (skGibbsEnergy N β h g))))) ^ (2 * k) ∂Q ≤ Bnd g :=
    fun g => (integral_mono_of_nonneg
      (ae_of_all _ fun y => Even.pow_nonneg ⟨k, by ring⟩ _)
      (h_int_inner g) (ae_of_all _ fun y => h_pointwise g y)).trans (h_upper_bnd g)
  have hnonneg : ∀ g, 0 ≤ ∫ y : Fin N → ℝ,
      (((∫ a, ((fun i => (Real.sqrt N)⁻¹ *
              (((a i : ℤ) : ℝ) -
              ∫ b, ((b i : ℤ) : ℝ) ∂(Measure.count.tilted (skGibbsEnergy N β h g)))) ⬝ᵥ y) *
            Real.cosh (((fun i => (Real.sqrt N)⁻¹ * (β * ((a i : ℤ) : ℝ))) ⬝ᵥ y) + h)
            ∂(Measure.count.tilted (skGibbsEnergy N β h g))) /
          (∫ a, Real.cosh (((fun i => (Real.sqrt N)⁻¹ * (β * ((a i : ℤ) : ℝ))) ⬝ᵥ y) + h)
            ∂(Measure.count.tilted (skGibbsEnergy N β h g)))) -
        β * (1 - q) *
          ((∫ a, Real.sinh (((fun i => (Real.sqrt N)⁻¹ * (β * ((a i : ℤ) : ℝ))) ⬝ᵥ y) + h)
              ∂(Measure.count.tilted (skGibbsEnergy N β h g))) /
            (∫ a, Real.cosh (((fun i => (Real.sqrt N)⁻¹ * (β * ((a i : ℤ) : ℝ))) ⬝ᵥ y) + h)
              ∂(Measure.count.tilted (skGibbsEnergy N β h g))))) ^ (2 * k) ∂Q :=
    fun g => integral_nonneg fun y => Even.pow_nonneg ⟨k, by ring⟩ _
  have h_bnd_int : Integrable Bnd P :=
    ((h_bnd_int1'.add h_bnd_int2').add (h_bnd_int1.add h_bnd_int2)).const_mul C_k
  have h_outer := integral_mono_of_nonneg (ae_of_all _ hnonneg) h_bnd_int (ae_of_all _ h_inner)
  have h_bnd_outer : ∫ g, Bnd g ∂P ≤
      (C_k * (((C₂_1' * K'_1' + M_1') / 2) + ((C₂_2' * K'_2' + M_2') / 2) +
        ((C₂_1 * K'_1 + M_1) / 2) + ((C₂_2 * K'_2 + M_2) / 2))) / (N : ℝ) ^ k := by
    dsimp [Bnd]
    rw [integral_const_mul]
    have h1 : ∫ g, (Bnd₁' g + Bnd₂' g) + (Bnd₁ g + Bnd₂ g) ∂P =
        (∫ g, Bnd₁' g + Bnd₂' g ∂P) + (∫ g, Bnd₁ g + Bnd₂ g ∂P) :=
      integral_add (h_bnd_int1'.add h_bnd_int2') (h_bnd_int1.add h_bnd_int2)
    have h2 : ∫ g, Bnd₁' g + Bnd₂' g ∂P = (∫ g, Bnd₁' g ∂P) + ∫ g, Bnd₂' g ∂P :=
      integral_add h_bnd_int1' h_bnd_int2'
    have h3 : ∫ g, Bnd₁ g + Bnd₂ g ∂P = (∫ g, Bnd₁ g ∂P) + ∫ g, Bnd₂ g ∂P :=
      integral_add h_bnd_int1 h_bnd_int2
    rw [h1, h2, h3]
    have h_sum_le := add_le_add (add_le_add h_bnd_le1' h_bnd_le2') (add_le_add h_bnd_le1 h_bnd_le2)
    have h_mul_le := mul_le_mul_of_nonneg_left h_sum_le hC_k_pos.le
    refine h_mul_le.trans_eq ?_
    ring
  refine h_outer.trans (h_bnd_outer.trans ?_)
  dsimp [Bnd_const]
  gcongr
  linarith
end

end SpinGlasses
