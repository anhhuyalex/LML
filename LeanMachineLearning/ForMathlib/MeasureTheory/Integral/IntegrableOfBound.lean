/-
Copyright (c) 2026 LML contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Integrability of the integral of a bounded function against random probability measures

If `κ ω` is a probability measure for every `ω` and `f` is bounded, the function
`ω ↦ ∫ f d(κ ω)` is bounded by the same constant, so it is integrable against a finite measure
as soon as it is a.e. measurable. This is the bounded-observable step for Gibbs or replica
averages, where `κ ω` is a random Gibbs measure or a power of one.
-/

@[expose] public section

open MeasureTheory

namespace MeasureTheory

/-- A bounded function integrated against random probability measures gives an integrable
function of the randomness, once that function is a.e. measurable. -/
theorem integrable_integral_of_bound {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    {P : Measure Ω} [IsFiniteMeasure P] {κ : Ω → Measure α} [∀ ω, IsProbabilityMeasure (κ ω)]
    {f : α → ℝ} {C : ℝ} (hC : ∀ x, |f x| ≤ C)
    (hm : AEMeasurable (fun ω => ∫ x, f x ∂κ ω) P) :
    Integrable (fun ω => ∫ x, f x ∂κ ω) P := by
  refine Integrable.of_bound hm.aestronglyMeasurable C (ae_of_all _ fun ω => ?_)
  rw [Real.norm_eq_abs]
  exact (abs_integral_le_integral_abs).trans
    ((integral_mono_of_nonneg (ae_of_all _ fun x => abs_nonneg (f x))
      (integrable_const C) (ae_of_all _ hC)).trans (by simp))

end MeasureTheory
