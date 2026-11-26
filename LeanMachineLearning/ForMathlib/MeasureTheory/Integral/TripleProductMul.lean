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

/-- The integral of a function of three independent blocks over `μ₁.prod (μ₂.prod μ₃)`, with a
vector-valued third factor. -/
theorem integral_prod_prod_eq_smul {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedSpace 𝕜 E] {Φ : α₁ × α₂ × α₃ → E} (F : α₁ → 𝕜) (G : α₂ → 𝕜)
    (H : α₃ → E) (h : Φ =ᵐ[μ₁.prod (μ₂.prod μ₃)] fun ω => F ω.1 • (G ω.2.1 • H ω.2.2)) :
    ∫ ω, Φ ω ∂(μ₁.prod (μ₂.prod μ₃)) =
      (∫ x, F x ∂μ₁) • ((∫ x, G x ∂μ₂) • ∫ x, H x ∂μ₃) := by
  rw [integral_congr_ae h, integral_prod_smul F (fun x : α₂ × α₃ => G x.1 • H x.2),
    integral_prod_smul G H]

/-- The integral of a function of three independent blocks over `μ₁.prod (μ₂.prod μ₃)`. -/
theorem integral_prod_prod_eq_mul (Φ : α₁ × α₂ × α₃ → ℝ) (F : α₁ → ℝ) (G : α₂ → ℝ)
    (H : α₃ → ℝ) (h : ∀ ω, Φ ω = F ω.1 * (G ω.2.1 * H ω.2.2)) :
    ∫ ω, Φ ω ∂(μ₁.prod (μ₂.prod μ₃)) =
      (∫ x, F x ∂μ₁) * ((∫ x, G x ∂μ₂) * ∫ x, H x ∂μ₃) :=
  integral_prod_prod_eq_smul F G H (ae_of_all _ h)

end MeasureTheory
