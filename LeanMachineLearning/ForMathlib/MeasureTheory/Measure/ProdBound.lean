/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# Bounds on product measures from sections

Two small tools for conditioning arguments on a product `μ ⊗ ν` of probability spaces:

* `MeasureTheory.measure_prod_le_of_ae_section_le`: if every `ν`-section `{b | (a, b) ∈ s}` of a
  measurable event `s` has measure at most `c`, then `(μ ⊗ ν) s ≤ c`;
* `MeasureTheory.lintegral_min_one_ofReal_le`: a truncated integrand `min 1 (ofReal (f x))` that
  is at most `c` off an event `E` has integral at most `μ E + ofReal c`. This turns the integrated
  Chebyshev bounds of `NTK/Initialization/GaussianConditioning.lean` into probability bounds.
-/

@[expose] public section

open scoped ENNReal

namespace MeasureTheory

/-- **A product measure is bounded by the sup of its sections.** If every section
`{b | (a, b) ∈ s}` of the measurable set `s` has `ν`-measure at most `c` (for `μ`-a.e. `a`), then
`(μ ⊗ ν) s ≤ c`, when `μ` is a probability measure. -/
theorem measure_prod_le_of_ae_section_le {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) [IsProbabilityMeasure μ] (ν : Measure β) [SFinite ν] {s : Set (α × β)}
    (hs : MeasurableSet s) {c : ℝ≥0∞} (h : ∀ᵐ a ∂μ, ν (Prod.mk a ⁻¹' s) ≤ c) :
    (μ.prod ν) s ≤ c := by
  rw [Measure.prod_apply hs]
  calc ∫⁻ a, ν (Prod.mk a ⁻¹' s) ∂μ ≤ ∫⁻ _, c ∂μ := lintegral_mono_ae h
    _ = c := by rw [lintegral_const, measure_univ, mul_one]

/-- **A truncated integrand that is small off an event.** If `f x ≤ c` for all `x ∉ E`, with `E`
measurable and `μ` a probability measure, then `∫⁻ min 1 (ofReal (f x)) ≤ μ E + ofReal c`. -/
theorem lintegral_min_one_ofReal_le {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] {E : Set α} (hE : MeasurableSet E) {f : α → ℝ} {c : ℝ}
    (hf : ∀ x, x ∉ E → f x ≤ c) :
    ∫⁻ x, min 1 (ENNReal.ofReal (f x)) ∂μ ≤ μ E + ENNReal.ofReal c := by
  calc ∫⁻ x, min 1 (ENNReal.ofReal (f x)) ∂μ
      ≤ ∫⁻ x, (E.indicator (1 : α → ℝ≥0∞) x + ENNReal.ofReal c) ∂μ := by
        refine lintegral_mono fun x => ?_
        by_cases hx : x ∈ E
        · simp only [Set.indicator_of_mem hx]
          exact (min_le_left _ _).trans le_self_add
        · simp only [Set.indicator_of_notMem hx, zero_add]
          exact (min_le_right _ _).trans (ENNReal.ofReal_le_ofReal (hf x hx))
    _ = μ E + ENNReal.ofReal c := by
        rw [lintegral_add_right _ measurable_const, lintegral_indicator_one hE, lintegral_const,
          measure_univ, mul_one]

end MeasureTheory

end
