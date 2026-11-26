/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.MeasureTheory.Measure.PiUpdate

/-!
# Integrating two independent coordinates against an invariant factor

The coordinate spaces and measures may vary with the index. A factor of two coordinates splits
off an observable which does not depend on them; the resampling identity supplies both
integrations. On finite spaces every integrability condition is automatic.
-/

@[expose] public section

namespace MeasureTheory

/-- A two-coordinate factor separates from a vector-valued observable unchanged by updates at
both coordinates, for a product of probability measures. -/
theorem integral_pi_smul_pair_of_invariant {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {X : ι → Type*} [(i : ι) → MeasurableSpace (X i)]
    (μ : (i : ι) → Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
    (x y : ι) (hxy : x ≠ y) (f : X x → X y → ℝ) (G : (∀ i, X i) → E)
    (hx : ∀ σ t, G (Function.update σ x t) = G σ)
    (hy : ∀ σ t, G (Function.update σ y t) = G σ)
    (hint : Integrable (fun σ => f (σ x) (σ y) • G σ) (Measure.pi μ)) :
    (∫ σ, f (σ x) (σ y) • G σ ∂Measure.pi μ) =
      (∫ a, ∫ b, f a b ∂μ y ∂μ x) • ∫ σ, G σ ∂Measure.pi μ := by
  have h1 : Integrable (fun σ => (∫ b, f (σ x) b ∂μ y) • G σ) (Measure.pi μ) := by
    refine (integrable_update_pi μ y hint).integral_prod_left.congr (ae_of_all _ fun σ => ?_)
    simp only [Function.update_self, Function.update_of_ne hxy, hy, integral_smul_const]
  rw [integral_pi_eq_integral_update μ y hint]
  simp only [Function.update_self, Function.update_of_ne hxy, hy, integral_smul_const]
  rw [integral_pi_eq_integral_update μ x h1]
  simp only [Function.update_self, hx, integral_smul_const]
  exact integral_smul _ _

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
      (∫ a, ∫ b, f a b ∂μ y ∂μ x) * ∫ σ, G σ ∂Measure.pi μ :=
  integral_pi_smul_pair_of_invariant μ x y hxy f G hx hy Integrable.of_finite

end MeasureTheory
