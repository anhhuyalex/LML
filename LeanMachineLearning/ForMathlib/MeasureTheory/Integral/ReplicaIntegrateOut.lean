/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Pi
public import LeanMachineLearning.ForMathlib.MeasureTheory.Measure.PiUpdate

/-!
# Integrating out one replica of an i.i.d. family

For an i.i.d. family `ρ : R → α` of a finite probability space, a function that does not depend on
the coordinate `d` except through one evaluation `ρ d` can be integrated in `ρ d` first: the
coordinate is replaced by an independent copy and averaged.
-/

@[expose] public section

open MeasureTheory Finset
open scoped BigOperators

namespace MeasureTheory

/-- Resampling integrates out a coordinate when the remaining vector-valued observable is
unchanged by updates there. The coordinate spaces and measures may depend on the index;
integrability is the only analytic input. -/
theorem integral_pi_integrate_out_coordinate {R E : Type*} [Fintype R] [DecidableEq R]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {X : R → Type*} [∀ r, MeasurableSpace (X r)]
    (μ : (r : R) → Measure (X r)) [∀ r, IsProbabilityMeasure (μ r)] (d : R)
    (Φ : (∀ r, X r) → X d → E) (hΦ : ∀ ρ s t, Φ (Function.update ρ d s) t = Φ ρ t)
    (hf : Integrable (fun ρ => Φ ρ (ρ d)) (Measure.pi μ)) :
    ∫ ρ, Φ ρ (ρ d) ∂(Measure.pi μ) = ∫ ρ, (∫ t, Φ ρ t ∂μ d) ∂(Measure.pi μ) := by
  rw [integral_pi_eq_integral_update μ d hf]
  simp only [Function.update_self, hΦ]

/-- Resampling integrates out a coordinate when the remaining observable is unchanged by
updates there. The sample space need not be finite; integrability is the only analytic input. -/
theorem integral_pi_integrate_out_replica_of_integrable {α R : Type*}
    [MeasurableSpace α] [Fintype R] [DecidableEq R]
    (μ : Measure α) [IsProbabilityMeasure μ] (d : R) (Φ : (R → α) → α → ℝ)
    (hΦ : ∀ ρ s t, Φ (Function.update ρ d s) t = Φ ρ t)
    (hf : Integrable (fun ρ => Φ ρ (ρ d)) (Measure.pi fun _ : R => μ)) :
    ∫ ρ, Φ ρ (ρ d) ∂(Measure.pi fun _ : R => μ) =
      ∫ ρ, (∫ t, Φ ρ t ∂μ) ∂(Measure.pi fun _ : R => μ) :=
  integral_pi_integrate_out_coordinate (fun _ => μ) d Φ hΦ hf

variable {α R : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] [Finite α]
  [Fintype R] [DecidableEq R]

/-- **Integrating out one replica.** If `Φ ρ t` does not depend on the coordinate `d` of `ρ`, then
averaging `Φ ρ (ρ d)` over an i.i.d. family equals averaging `ρ ↦ ∫ t, Φ ρ t ∂μ`. -/
theorem integral_pi_integrate_out_replica (μ : Measure α) [IsProbabilityMeasure μ] (d : R)
    (Φ : (R → α) → α → ℝ) (hΦ : ∀ ρ s t, Φ (Function.update ρ d s) t = Φ ρ t) :
    ∫ ρ, Φ ρ (ρ d) ∂(Measure.pi fun _ : R => μ) =
      ∫ ρ, (∫ t, Φ ρ t ∂μ) ∂(Measure.pi fun _ : R => μ) :=
  integral_pi_integrate_out_replica_of_integrable μ d Φ hΦ Integrable.of_finite

end MeasureTheory
