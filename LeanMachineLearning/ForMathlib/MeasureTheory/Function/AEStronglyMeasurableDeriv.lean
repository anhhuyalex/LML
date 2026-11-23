/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.MeasureTheory.Function.AEMeasurableSequence
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable

/-!
# Measurability of a parametric derivative

If `s ↦ G ω s` has a derivative at `x` for almost every parameter `ω` and `ω ↦ G ω s` is a.e. strongly
measurable for every `s`, then the derivative `ω ↦ G' ω` at `x` is a.e. strongly measurable: it is
the limit of the measurable difference quotients along `x + 1/(n+1)`.

* `MeasureTheory.aestronglyMeasurable_of_hasDerivAt_param`.
-/

@[expose] public section

open MeasureTheory Filter Topology

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- **The derivative of a measurable family is measurable.** -/
theorem aestronglyMeasurable_of_hasDerivAt_param {G : α → ℝ → ℝ} {G' : α → ℝ} {x : ℝ}
    (hG : ∀ᵐ ω ∂μ, HasDerivAt (G ω) (G' ω) x) (hm : ∀ s, AEStronglyMeasurable (fun ω => G ω s) μ) :
    AEStronglyMeasurable G' μ := by
  refine aestronglyMeasurable_of_tendsto_ae (atTop : Filter ℕ)
    (f := fun (n : ℕ) (ω : α) => (1 / ((n : ℝ) + 1))⁻¹ • (G ω (x + 1 / ((n : ℝ) + 1)) - G ω x))
    (fun n => by
      have := ((hm (x + 1 / ((n : ℝ) + 1))).sub (hm x)).const_smul (1 / ((n : ℝ) + 1))⁻¹
      exact this) (hG.mono fun ω hω => ?_)
  exact hω.tendsto_slope_zero_right.comp (tendsto_nhdsWithin_iff.2
    ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall fun n => Set.mem_Ioi.2 (by positivity)⟩)

end MeasureTheory
