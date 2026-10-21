/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Pointwise domination of a triple iterated integral

A pointwise bound `|G x y z| ≤ H x y z` passes through three nested integrals
`∫ x, ∫ y, ∫ z, G x y z ∂κ x y ∂ν ∂μ`, where the innermost measure may depend on the outer
variables, as soon as the dominating function has integrable partial integrals.
-/

@[expose] public section

open MeasureTheory

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

/-- Integrating a function of the second coordinate over a product with a probability measure. -/
theorem integral_prod_fun_snd_of_isProbabilityMeasure {X Y E : Type*} [MeasurableSpace X]
    [MeasurableSpace Y] [NormedAddCommGroup E] [NormedSpace ℝ E] (μ : Measure X)
    [IsProbabilityMeasure μ] (ν : Measure Y) (f : Y → E) :
    ∫ x, f x.2 ∂(μ.prod ν) = ∫ y, f y ∂ν := by
  rw [integral_fun_snd, probReal_univ, one_smul]
