/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Analysis.RCLike.Basic

/-!
# Independent replicas: the integral of a product of functions of distinct coordinates

For a product `Measure.pi μ` of probability measures indexed by `Fin n`, the integral of
`f₀ (τ 0) * f₁ (τ 1) * ⋯` is the product of the integrals. These are the cases `n = 2, 3, 4` of
`MeasureTheory.integral_fintype_prod_eq_prod`, in the explicit form needed for Gibbs averages of
two to four replicas; the statements for a single measure `μ` are their special cases.
-/

@[expose] public section

namespace MeasureTheory

variable {α 𝕜 : Type*} [MeasurableSpace α] [RCLike 𝕜]

section Family

variable {n : ℕ}

/-- The integral of `f₀(σ¹) f₁(σ²)` under a product of two probability measures. -/
theorem integral_pi_fin_two_mul_fun_dep (μ : Fin 2 → Measure α) [∀ r, IsProbabilityMeasure (μ r)]
    (f₀ f₁ : α → 𝕜) :
    ∫ τ : Fin 2 → α, f₀ (τ 0) * f₁ (τ 1) ∂(Measure.pi μ) =
      (∫ x, f₀ x ∂μ 0) * ∫ x, f₁ x ∂μ 1 := by
  have := integral_fintype_prod_eq_prod (μ := μ) (fun r : Fin 2 => ![f₀, f₁] r)
  simpa [Fin.prod_univ_two] using this

/-- The integral of `f₀(σ¹) f₁(σ²) f₂(σ³)` under a product of three probability measures. -/
theorem integral_pi_fin_three_mul_fun_dep (μ : Fin 3 → Measure α)
    [∀ r, IsProbabilityMeasure (μ r)] (f₀ f₁ f₂ : α → 𝕜) :
    ∫ τ : Fin 3 → α, f₀ (τ 0) * f₁ (τ 1) * f₂ (τ 2) ∂(Measure.pi μ) =
      (∫ x, f₀ x ∂μ 0) * (∫ x, f₁ x ∂μ 1) * ∫ x, f₂ x ∂μ 2 := by
  have := integral_fintype_prod_eq_prod (μ := μ) (fun r : Fin 3 => ![f₀, f₁, f₂] r)
  simpa [Fin.prod_univ_three] using this

/-- The integral of a product of four functions under a product of four probability measures. -/
theorem integral_pi_fin_four_mul_fun_dep (μ : Fin 4 → Measure α)
    [∀ r, IsProbabilityMeasure (μ r)] (f₀ f₁ f₂ f₃ : α → 𝕜) :
    ∫ τ : Fin 4 → α, f₀ (τ 0) * f₁ (τ 1) * f₂ (τ 2) * f₃ (τ 3) ∂(Measure.pi μ) =
      (∫ x, f₀ x ∂μ 0) * (∫ x, f₁ x ∂μ 1) * (∫ x, f₂ x ∂μ 2) * ∫ x, f₃ x ∂μ 3 := by
  have := integral_fintype_prod_eq_prod (μ := μ) (fun r : Fin 4 => ![f₀, f₁, f₂, f₃] r)
  simpa [Fin.prod_univ_four] using this

end Family

variable (μ : Measure α) [IsProbabilityMeasure μ]

/-- Independent replicas: the average of a product `f₀(σ¹) f₁(σ²)` factorizes. -/
theorem integral_pi_fin_two_mul_fun (f₀ f₁ : α → 𝕜) :
    ∫ τ : Fin 2 → α, f₀ (τ 0) * f₁ (τ 1) ∂(Measure.pi fun _ : Fin 2 => μ) =
      (∫ x, f₀ x ∂μ) * ∫ x, f₁ x ∂μ :=
  integral_pi_fin_two_mul_fun_dep (fun _ => μ) f₀ f₁

/-- Independent replicas: the average of a product `f₀(σ¹) f₁(σ²) f₂(σ³)` factorizes. -/
theorem integral_pi_fin_three_mul_fun (f₀ f₁ f₂ : α → 𝕜) :
    ∫ τ : Fin 3 → α, f₀ (τ 0) * f₁ (τ 1) * f₂ (τ 2) ∂(Measure.pi fun _ : Fin 3 => μ) =
      (∫ x, f₀ x ∂μ) * (∫ x, f₁ x ∂μ) * ∫ x, f₂ x ∂μ :=
  integral_pi_fin_three_mul_fun_dep (fun _ => μ) f₀ f₁ f₂

/-- Independent replicas: the average of a product of four functions of four replicas
factorizes. -/
theorem integral_pi_fin_four_mul_fun (f₀ f₁ f₂ f₃ : α → 𝕜) :
    ∫ τ : Fin 4 → α, f₀ (τ 0) * f₁ (τ 1) * f₂ (τ 2) * f₃ (τ 3)
        ∂(Measure.pi fun _ : Fin 4 => μ) =
      (∫ x, f₀ x ∂μ) * (∫ x, f₁ x ∂μ) * (∫ x, f₂ x ∂μ) * ∫ x, f₃ x ∂μ :=
  integral_pi_fin_four_mul_fun_dep (fun _ => μ) f₀ f₁ f₂ f₃

end MeasureTheory
