/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Integral of a product over a triple product measure

For `μ₁.prod (μ₂.prod μ₃)` the integral of `F ω.1 * (G ω.2.1 * H ω.2.2)` is the product of the
three integrals. This is `MeasureTheory.integral_prod_mul` used twice; the variant with an
arbitrary integrand `Φ` and a pointwise equation `Φ ω = F ω.1 * (G ω.2.1 * H ω.2.2)` is the form
used to compute covariances of three independent blocks of coordinates.
-/

@[expose] public section

namespace MeasureTheory

variable {α₁ α₂ α₃ : Type*} [MeasurableSpace α₁] [MeasurableSpace α₂] [MeasurableSpace α₃]
  {μ₁ : Measure α₁} {μ₂ : Measure α₂} {μ₃ : Measure α₃}
  [SFinite μ₁] [SFinite μ₂] [SFinite μ₃]

/-- The integral of a function of three independent blocks over `μ₁.prod (μ₂.prod μ₃)`. -/
theorem integral_prod_prod_eq_mul (Φ : α₁ × α₂ × α₃ → ℝ) (F : α₁ → ℝ) (G : α₂ → ℝ)
    (H : α₃ → ℝ) (h : ∀ ω, Φ ω = F ω.1 * (G ω.2.1 * H ω.2.2)) :
    ∫ ω, Φ ω ∂(μ₁.prod (μ₂.prod μ₃)) =
      (∫ x, F x ∂μ₁) * ((∫ x, G x ∂μ₂) * ∫ x, H x ∂μ₃) := by
  have hΦ : Φ = fun ω => F ω.1 * (G ω.2.1 * H ω.2.2) := funext h
  rw [hΦ, integral_prod_mul F (fun x : α₂ × α₃ => G x.1 * H x.2), integral_prod_mul G H]

end MeasureTheory
