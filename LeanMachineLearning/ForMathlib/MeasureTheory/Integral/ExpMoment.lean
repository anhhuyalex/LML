/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# First moments from exponential moments

On a probability space, `1 + c x ≤ exp (c x)` turns an exponential moment bound
`∫ exp (c X) ≤ C` into the first moment bound `c ∫ X ≤ C - 1`.  The pointwise inequality is
stated for an arbitrary integrand `Z`, so that it also applies to conditional expectations.
-/

@[expose] public section

open MeasureTheory

namespace MeasureTheory

/-- If `1 + c * Y ≤ Z` pointwise on a probability space, then `1 + c * ∫ Y ≤ ∫ Z`. -/
theorem one_add_mul_integral_le_integral {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {Y Z : Ω → ℝ} (c : ℝ) (hY : Integrable Y μ) (hZ : Integrable Z μ)
    (h : ∀ ω, 1 + c * Y ω ≤ Z ω) : 1 + c * ∫ ω, Y ω ∂μ ≤ ∫ ω, Z ω ∂μ := by
  have hint : ∫ ω, (1 + c * Y ω) ∂μ ≤ ∫ ω, Z ω ∂μ :=
    integral_mono ((integrable_const 1).add (hY.const_mul c)) hZ h
  rwa [integral_add (integrable_const 1) (hY.const_mul c), integral_const, integral_const_mul,
    probReal_univ, one_smul] at hint

/-- `1 + c ∫ X ≤ ∫ exp (c X)` on a probability space. -/
theorem one_add_mul_integral_le_integral_exp {Ω : Type*} {m : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ} (c : ℝ) (hX : Integrable X μ)
    (hexp : Integrable (fun ω => Real.exp (c * X ω)) μ) :
    1 + c * ∫ ω, X ω ∂μ ≤ ∫ ω, Real.exp (c * X ω) ∂μ :=
  one_add_mul_integral_le_integral c hX hexp fun ω => by
    simpa [add_comm] using Real.add_one_le_exp (c * X ω)

/-- **Two-level version:** for a family of probability measures `μ ω` indexed by a probability
space, `1 + c 𝔼 ∫ X dμ ≤ 𝔼 ∫ exp (c X) dμ`.  This is the passage from an exponential moment of a
random Gibbs average to its second moment. -/
theorem one_add_mul_integral_integral_le {Ω Γ : Type*} {mΩ : MeasurableSpace Ω}
    {mΓ : MeasurableSpace Γ} {P : Measure Ω} [IsProbabilityMeasure P] {μ : Ω → Measure Γ}
    [∀ ω, IsProbabilityMeasure (μ ω)] {X : Γ → ℝ} (c : ℝ) (hX : ∀ ω, Integrable X (μ ω))
    (hexp : ∀ ω, Integrable (fun σ => Real.exp (c * X σ)) (μ ω))
    (hJX : Integrable (fun ω => ∫ σ, X σ ∂μ ω) P)
    (hJexp : Integrable (fun ω => ∫ σ, Real.exp (c * X σ) ∂μ ω) P) :
    1 + c * ∫ ω, ∫ σ, X σ ∂μ ω ∂P ≤ ∫ ω, ∫ σ, Real.exp (c * X σ) ∂μ ω ∂P :=
  one_add_mul_integral_le_integral c hJX hJexp fun ω =>
    one_add_mul_integral_le_integral_exp c (hX ω) (hexp ω)

end MeasureTheory
