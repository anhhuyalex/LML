/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Analysis.SpecialFunctions.Hyperbolic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Hyperbolic functions integrated against a finite probability measure

For a probability measure on a finite measurable-singleton space, the integrals of
`sinh (u + h)` and `cosh (u + h)` are linear combinations of `∫ exp (±u)`, `1 ≤ ∫ cosh u`, and
`|∫ sinh u| ≤ ∫ cosh u`.
-/

@[expose] public section

open MeasureTheory

/-- The integral of `Ψ * sinh (u + h)` against a finite probability measure. -/
theorem integral_mul_sinh_add {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : Measure α) [IsProbabilityMeasure μ] [Finite α] (Ψ u : α → ℝ) (h : ℝ) :
    ∫ a, Ψ a * Real.sinh (u a + h) ∂μ =
      (Real.exp h * (∫ a, Ψ a * Real.exp (u a) ∂μ) -
        Real.exp (-h) * (∫ a, Ψ a * Real.exp (-u a) ∂μ)) / 2 := by
  have heq : (fun a => Ψ a * Real.sinh (u a + h)) = fun a =>
      (Real.exp h * (Ψ a * Real.exp (u a)) - Real.exp (-h) * (Ψ a * Real.exp (-u a))) / 2 := by
    ext a; rw [Real.sinh_add_eq_exp]; ring
  rw [heq, integral_div, integral_sub Integrable.of_finite Integrable.of_finite,
    integral_const_mul, integral_const_mul]

/-- The integral of `Ψ * cosh (u + h)` against a finite probability measure. -/
theorem integral_mul_cosh_add {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : Measure α) [IsProbabilityMeasure μ] [Finite α] (Ψ u : α → ℝ) (h : ℝ) :
    ∫ a, Ψ a * Real.cosh (u a + h) ∂μ =
      (Real.exp h * (∫ a, Ψ a * Real.exp (u a) ∂μ) +
        Real.exp (-h) * (∫ a, Ψ a * Real.exp (-u a) ∂μ)) / 2 := by
  have heq : (fun a => Ψ a * Real.cosh (u a + h)) = fun a =>
      (Real.exp h * (Ψ a * Real.exp (u a)) + Real.exp (-h) * (Ψ a * Real.exp (-u a))) / 2 := by
    ext a; rw [Real.cosh_add_eq_exp]; ring
  rw [heq, integral_div, integral_add Integrable.of_finite Integrable.of_finite,
    integral_const_mul, integral_const_mul]

/-- The integral of `sinh (u + h)` against a finite probability measure. -/
theorem integral_sinh_add {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : Measure α) [IsProbabilityMeasure μ] [Finite α] (u : α → ℝ) (h : ℝ) :
    ∫ a, Real.sinh (u a + h) ∂μ =
      (Real.exp h * (∫ a, Real.exp (u a) ∂μ) -
        Real.exp (-h) * (∫ a, Real.exp (-u a) ∂μ)) / 2 := by
  simpa using integral_mul_sinh_add μ (fun _ => 1) u h

/-- The integral of `cosh (u + h)` against a finite probability measure. -/
theorem integral_cosh_add {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : Measure α) [IsProbabilityMeasure μ] [Finite α] (u : α → ℝ) (h : ℝ) :
    ∫ a, Real.cosh (u a + h) ∂μ =
      (Real.exp h * (∫ a, Real.exp (u a) ∂μ) +
        Real.exp (-h) * (∫ a, Real.exp (-u a) ∂μ)) / 2 := by
  simpa using integral_mul_cosh_add μ (fun _ => 1) u h

/-- `1 ≤ ∫ cosh u` against a finite probability measure. -/
theorem one_le_integral_cosh {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : Measure α) [IsProbabilityMeasure μ] [Finite α] (u : α → ℝ) :
    1 ≤ ∫ a, Real.cosh (u a) ∂μ := by
  have h1 : (1 : ℝ) = ∫ _ : α, (1 : ℝ) ∂μ := by
    simp only [integral_const, probReal_univ, one_smul]
  rw [h1]
  exact integral_mono (integrable_const 1) Integrable.of_finite (fun a => Real.one_le_cosh (u a))

/-- `|∫ sinh u| ≤ ∫ cosh u` against a finite probability measure. -/
theorem abs_integral_sinh_le_integral_cosh {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] (μ : Measure α) [IsProbabilityMeasure μ]
    [Finite α] (u : α → ℝ) :
    |∫ a, Real.sinh (u a) ∂μ| ≤ ∫ a, Real.cosh (u a) ∂μ := by
  refine abs_integral_le_integral_abs.trans ?_
  exact integral_mono Integrable.of_finite Integrable.of_finite
    (fun a => Real.abs_sinh_le_cosh (u a))

/-- `|∫ φ w| ≤ C ∫ w` for a nonnegative weight `w` and `|φ| ≤ C`, finite space. -/
theorem abs_integral_mul_le_mul_integral {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] (μ : Measure α) [IsProbabilityMeasure μ] [Finite α]
    (φ w : α → ℝ) (hw : ∀ a, 0 ≤ w a) {C : ℝ} (hφ : ∀ a, |φ a| ≤ C) :
    |∫ a, φ a * w a ∂μ| ≤ C * ∫ a, w a ∂μ := by
  rw [← integral_const_mul]
  refine abs_integral_le_integral_abs.trans (integral_mono Integrable.of_finite
    Integrable.of_finite fun a => ?_)
  rw [abs_mul, abs_of_nonneg (hw a)]
  exact mul_le_mul_of_nonneg_right (hφ a) (hw a)

/-- `|⟨sinh u⟩ / ⟨cosh u⟩| ≤ 1`. -/
theorem abs_integral_sinh_div_integral_cosh_le {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] (μ : Measure α) [IsProbabilityMeasure μ] [Finite α]
    (u : α → ℝ) : |(∫ a, Real.sinh (u a) ∂μ) / ∫ a, Real.cosh (u a) ∂μ| ≤ 1 := by
  have hD : 0 < ∫ a, Real.cosh (u a) ∂μ := lt_of_lt_of_le one_pos (one_le_integral_cosh μ u)
  rw [abs_div, abs_of_pos hD, div_le_one hD]
  exact abs_integral_sinh_le_integral_cosh μ u

/-- `|⟨φ cosh u⟩ / ⟨cosh u⟩| ≤ C` when `|φ| ≤ C`. -/
theorem abs_integral_mul_cosh_div_le {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] (μ : Measure α) [IsProbabilityMeasure μ] [Finite α]
    (φ u : α → ℝ) {C : ℝ} (hφ : ∀ a, |φ a| ≤ C) :
    |(∫ a, φ a * Real.cosh (u a) ∂μ) / ∫ a, Real.cosh (u a) ∂μ| ≤ C := by
  have hD : 0 < ∫ a, Real.cosh (u a) ∂μ := lt_of_lt_of_le one_pos (one_le_integral_cosh μ u)
  rw [abs_div, abs_of_pos hD, div_le_iff₀ hD]
  exact abs_integral_mul_le_mul_integral μ φ _ (fun a => (Real.cosh_pos _).le) hφ
