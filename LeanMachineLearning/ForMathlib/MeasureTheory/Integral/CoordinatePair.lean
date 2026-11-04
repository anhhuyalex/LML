/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.MeasureTheory.Measure.PiUpdate

/-!
# Integrating two independent coordinates against an invariant factor

The coordinate spaces and measures may vary with the index. Finiteness makes all
integrability conditions automatic. The resampling identity supplies both integrations.
-/

@[expose] public section

namespace MeasureTheory

/-- A two-coordinate factor separates from an observable unchanged by updates at both
coordinates, for a product of probability measures on finite spaces. -/
theorem integral_pi_mul_pair_of_invariant {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X : ι → Type*} [∀ i, Finite (X i)] [(i : ι) → MeasurableSpace (X i)]
    [∀ i, MeasurableSingletonClass (X i)]
    (μ : (i : ι) → Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
    (x y : ι) (hxy : x ≠ y) (f : X x → X y → ℝ) (G : (∀ i, X i) → ℝ)
    (hx : ∀ σ t, G (Function.update σ x t) = G σ)
    (hy : ∀ σ t, G (Function.update σ y t) = G σ) :
    (∫ σ, f (σ x) (σ y) * G σ ∂Measure.pi μ) =
      (∫ a, ∫ b, f a b ∂μ y ∂μ x) * ∫ σ, G σ ∂Measure.pi μ := by
  rw [integral_pi_eq_integral_update μ y Integrable.of_finite]
  simp only [Function.update_self, Function.update_of_ne hxy, hy, integral_mul_const]
  rw [integral_pi_eq_integral_update μ x Integrable.of_finite]
  simp only [Function.update_self, hx, integral_mul_const]
  exact integral_const_mul _ _

end MeasureTheory
