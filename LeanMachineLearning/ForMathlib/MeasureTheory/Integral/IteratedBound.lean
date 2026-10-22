/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Pointwise domination of a triple iterated integral

A pointwise bound `|G x y z| ≤ H x y z` passes through three nested integrals
`∫ x, ∫ y, ∫ z, G x y z ∂κ x y ∂ν ∂μ`, where the innermost measure may depend on the outer
variables, as soon as the dominating function has integrable partial integrals.
-/

@[expose] public section

open MeasureTheory

/-- Multiplying both copies of a real-valued integrand by a scalar whose square is one does not
change its second moment. -/
@[simp] theorem integral_mul_self_of_sq_eq_one {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (u : ℝ) (hu : u ^ 2 = 1) (f : X → ℝ) :
    ∫ x, (u * f x) * (u * f x) ∂μ = ∫ x, f x * f x ∂μ := by
  congr 1
  funext x
  calc
    (u * f x) * (u * f x) = u ^ 2 * (f x * f x) := by ring
    _ = f x * f x := by rw [hu, one_mul]

/-- Two scalar factors may be collected outside a real-valued integral. -/
theorem integral_mul_mul_eq_mul_integral {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (u v : ℝ) (f g : X → ℝ) :
    ∫ x, (u * f x) * (v * g x) ∂μ = u * v * ∫ x, f x * g x ∂μ := by
  have hfun : (fun x => (u * f x) * (v * g x)) = fun x => (u * v) * (f x * g x) := by
    funext x
    ring
  rw [hfun, integral_const_mul]

/-- A pointwise bound `|f| ≤ K g` passes through an integral.  The domination hypothesis itself
forces `K g` to be nonnegative, so no separate sign assumptions on `K` or `g` are needed. -/
theorem abs_integral_le_const_mul_integral {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {f g : X → ℝ} {K : ℝ} (hg : Integrable g μ)
    (hfg : ∀ x, |f x| ≤ K * g x) :
    |∫ x, f x ∂μ| ≤ K * ∫ x, g x ∂μ := by
  have h := norm_integral_le_of_norm_le (f := f) (hg.const_mul K)
    (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hfg x)
  simpa only [Real.norm_eq_abs, integral_const_mul] using h

/-- Integrating a constant plus an integrable function over a probability measure preserves the
constant. -/
@[simp] theorem integral_const_add_of_isProbabilityMeasure
    {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (μ : Measure X) [IsProbabilityMeasure μ] (c : E) (f : X → E)
    (hf : Integrable f μ) :
    ∫ x, c + f x ∂μ = c + ∫ x, f x ∂μ := by
  rw [integral_add (integrable_const c) hf, integral_const, probReal_univ, one_smul]

/-- Integrating an integrable function plus a constant over a probability measure preserves the
constant. -/
@[simp] theorem integral_add_const_of_isProbabilityMeasure
    {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (μ : Measure X) [IsProbabilityMeasure μ] (f : X → E) (c : E)
    (hf : Integrable f μ) :
    ∫ x, f x + c ∂μ = (∫ x, f x ∂μ) + c := by
  simpa only [add_comm] using integral_const_add_of_isProbabilityMeasure μ c f hf

/-- Domination of a triple iterated integral by the iterated integral of a dominating function. -/
theorem abs_integral_integral_integral_le {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace Z] (μ : Measure X) (ν : Measure Y) (κ : X → Y → Measure Z)
    {G H : X → Y → Z → ℝ} (hGH : ∀ x y z, |G x y z| ≤ H x y z)
    (h1 : ∀ x y, Integrable (H x y) (κ x y))
    (h2 : ∀ x, Integrable (fun y => ∫ z, H x y z ∂κ x y) ν)
    (h3 : Integrable (fun x => ∫ y, ∫ z, H x y z ∂κ x y ∂ν) μ) :
    |∫ x, ∫ y, ∫ z, G x y z ∂κ x y ∂ν ∂μ| ≤ ∫ x, ∫ y, ∫ z, H x y z ∂κ x y ∂ν ∂μ := by
  have l1 (x y) : |∫ z, G x y z ∂κ x y| ≤ ∫ z, H x y z ∂κ x y := by
    simpa only [Real.norm_eq_abs] using
      norm_integral_le_of_norm_le (f := fun z => G x y z) (h1 x y) (ae_of_all _ fun z => by
        simpa only [Real.norm_eq_abs] using hGH x y z)
  have l2 (x) : |∫ y, ∫ z, G x y z ∂κ x y ∂ν| ≤ ∫ y, ∫ z, H x y z ∂κ x y ∂ν := by
    simpa only [Real.norm_eq_abs] using
      norm_integral_le_of_norm_le (f := fun y => ∫ z, G x y z ∂κ x y) (h2 x)
        (ae_of_all _ fun y => by
        simpa only [Real.norm_eq_abs] using l1 x y)
  simpa only [Real.norm_eq_abs] using
    norm_integral_le_of_norm_le (f := fun x => ∫ y, ∫ z, G x y z ∂κ x y ∂ν) h3
      (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using l2 x)

/-- A nonnegative combination of iterated averages, each bounded by `X`, is bounded by the sum of
the coefficients times `X`. The inner integrals are over finite measures and the outer integrand of
each term is integrable. -/
theorem integral_integral_finset_sum_le {Ω Z ι : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
    (μ : Measure Ω) (κ : Ω → Measure Z) (s : Finset ι) (c : ι → ℝ) (G : ι → Z → ℝ) (X : ℝ)
    (hG : ∀ j g, Integrable (G j) (κ g))
    (hint : ∀ j, Integrable (fun g => ∫ z, G j z ∂κ g) μ)
    (hc : ∀ j ∈ s, 0 ≤ c j) (hX : ∀ j ∈ s, ∫ g, ∫ z, G j z ∂κ g ∂μ ≤ X) :
    ∫ g, ∫ z, ∑ j ∈ s, c j * G j z ∂κ g ∂μ ≤ (∑ j ∈ s, c j) * X := by
  have h1 : ∀ g, ∫ z, ∑ j ∈ s, c j * G j z ∂κ g = ∑ j ∈ s, c j * ∫ z, G j z ∂κ g := fun g => by
    rw [integral_finsetSum _ fun j _ => (hG j g).const_mul (c j)]
    exact Finset.sum_congr rfl fun j _ => integral_const_mul _ _
  simp_rw [h1]
  rw [integral_finsetSum _ fun j _ => (hint j).const_mul (c j)]
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun j hj => ?_
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left (hX j hj) (hc j hj)

/-- Integrating a function of the first coordinate over a product with a probability measure. -/
theorem integral_prod_fun_fst_of_isProbabilityMeasure {X Y E : Type*} [MeasurableSpace X]
    [MeasurableSpace Y] [NormedAddCommGroup E] [NormedSpace ℝ E] (μ : Measure X) [SFinite μ]
    (ν : Measure Y) [IsProbabilityMeasure ν] (f : X → E) :
    ∫ x, f x.1 ∂(μ.prod ν) = ∫ y, f y ∂μ := by
  rw [integral_fun_fst, probReal_univ, one_smul]

/-- Integrating a function of the second coordinate over a product with a probability measure. -/
theorem integral_prod_fun_snd_of_isProbabilityMeasure {X Y E : Type*} [MeasurableSpace X]
    [MeasurableSpace Y] [NormedAddCommGroup E] [NormedSpace ℝ E] (μ : Measure X)
    [IsProbabilityMeasure μ] (ν : Measure Y) [SFinite ν] (f : Y → E) :
    ∫ x, f x.2 ∂(μ.prod ν) = ∫ y, f y ∂ν := by
  rw [integral_fun_snd, probReal_univ, one_smul]

/-- A uniform bound on an observable bounds its iterated average over probability kernels. -/
theorem abs_integral_integral_le_of_forall_le {X Y : Type*} [MeasurableSpace X]
    [MeasurableSpace Y] (μ : Measure X) [IsProbabilityMeasure μ] (κ : X → Measure Y)
    [∀ x, IsProbabilityMeasure (κ x)] (F : Y → ℝ) {M : ℝ} (hF : ∀ y, |F y| ≤ M) :
    |∫ x, ∫ y, F y ∂κ x ∂μ| ≤ M := by
  have hin : ∀ x, ‖∫ y, F y ∂κ x‖ ≤ M := fun x => by
    simpa using norm_integral_le_of_norm_le_const (μ := κ x) (f := F) (C := M)
      (ae_of_all _ fun y => by simpa only [Real.norm_eq_abs] using hF y)
  simpa using norm_integral_le_of_norm_le_const (μ := μ) (f := fun x => ∫ y, F y ∂κ x)
    (C := M) (ae_of_all _ hin)
