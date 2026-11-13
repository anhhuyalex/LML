/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Pi

/-!
# Independent replicas: the integral of a product of functions of distinct coordinates

For the product measure `Measure.pi fun _ : Fin n => μ` with `μ` a probability measure, the
integral of `f₀ (τ 0) * f₁ (τ 1) * ⋯` is the product of the integrals. These are the cases
`n = 2, 3, 4` of `MeasureTheory.integral_fintype_prod_eq_prod`, in the explicit form needed for
Gibbs averages of two to four replicas.
-/

@[expose] public section

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]

/-- Independent replicas: the average of a product `f₀(σ¹) f₁(σ²)` factorizes. -/
theorem integral_pi_fin_two_mul_fun (f₀ f₁ : α → ℝ) :
    ∫ τ : Fin 2 → α, f₀ (τ 0) * f₁ (τ 1) ∂(Measure.pi fun _ : Fin 2 => μ) =
      (∫ x, f₀ x ∂μ) * ∫ x, f₁ x ∂μ := by
  have := integral_fintype_prod_eq_prod (μ := fun _ : Fin 2 => μ) (fun r : Fin 2 => ![f₀, f₁] r)
  simpa [Fin.prod_univ_two] using this

/-- Independent replicas: the average of a product `f₀(σ¹) f₁(σ²) f₂(σ³)` factorizes. -/
theorem integral_pi_fin_three_mul_fun (f₀ f₁ f₂ : α → ℝ) :
    ∫ τ : Fin 3 → α, f₀ (τ 0) * f₁ (τ 1) * f₂ (τ 2) ∂(Measure.pi fun _ : Fin 3 => μ) =
      (∫ x, f₀ x ∂μ) * (∫ x, f₁ x ∂μ) * ∫ x, f₂ x ∂μ := by
  have := integral_fintype_prod_eq_prod (μ := fun _ : Fin 3 => μ)
    (fun r : Fin 3 => ![f₀, f₁, f₂] r)
  simpa [Fin.prod_univ_three] using this

/-- Independent replicas: the average of a product of four functions of four replicas
factorizes. -/
theorem integral_pi_fin_four_mul_fun (f₀ f₁ f₂ f₃ : α → ℝ) :
    ∫ τ : Fin 4 → α, f₀ (τ 0) * f₁ (τ 1) * f₂ (τ 2) * f₃ (τ 3)
        ∂(Measure.pi fun _ : Fin 4 => μ) =
      (∫ x, f₀ x ∂μ) * (∫ x, f₁ x ∂μ) * (∫ x, f₂ x ∂μ) * ∫ x, f₃ x ∂μ := by
  have := integral_fintype_prod_eq_prod (μ := fun _ : Fin 4 => μ)
    (fun r : Fin 4 => ![f₀, f₁, f₂, f₃] r)
  simpa [Fin.prod_univ_four] using this

end MeasureTheory
