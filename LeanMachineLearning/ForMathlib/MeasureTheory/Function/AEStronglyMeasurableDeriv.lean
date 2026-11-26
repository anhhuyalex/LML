/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.MeasureTheory.Function.AEMeasurableSequence
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable

/-!
# Measurability of a parametric derivative

If `s ↦ G ω s` has a derivative at `x` for almost every parameter `ω` and `ω ↦ G ω s` is
a.e. strongly measurable for every `s`, then the derivative `ω ↦ G' ω` at `x` is a.e. strongly
measurable: it is
the limit of the measurable difference quotients along `x + 1/(n+1)`.

* `MeasureTheory.aestronglyMeasurable_of_hasDerivAt_param`.
* `MeasureTheory.stronglyMeasurable_of_hasDerivAt_param`: the everywhere version.
* `MeasureTheory.stronglyMeasurable_of_forall_hasDerivAt`: a function which is a derivative
  everywhere is strongly measurable, with values in any real normed space (no completeness).
-/

@[expose] public section

open MeasureTheory Filter Topology

namespace MeasureTheory

variable {α F : Type*} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- The difference quotients of `g` along `x + 1/(n+1)` converge to its derivative at `x`. -/
theorem _root_.HasDerivAt.tendsto_slope_one_div_add_one {g : ℝ → F} {g' : F} {x : ℝ}
    (h : HasDerivAt g g' x) :
    Tendsto (fun n : ℕ => (1 / ((n : ℝ) + 1))⁻¹ • (g (x + 1 / ((n : ℝ) + 1)) - g x))
      atTop (𝓝 g') :=
  h.tendsto_slope_zero_right.comp (tendsto_nhdsWithin_iff.2
    ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall fun n => Set.mem_Ioi.2 (by positivity)⟩)

/-- **The derivative of a measurable family is measurable.** -/
theorem aestronglyMeasurable_of_hasDerivAt_param {G : α → ℝ → F} {G' : α → F} {x : ℝ}
    (hG : ∀ᵐ ω ∂μ, HasDerivAt (G ω) (G' ω) x) (hm : ∀ s, AEStronglyMeasurable (fun ω => G ω s) μ) :
    AEStronglyMeasurable G' μ :=
  aestronglyMeasurable_of_tendsto_ae (atTop : Filter ℕ)
    (fun n => ((hm (x + 1 / ((n : ℝ) + 1))).sub (hm x)).const_smul (1 / ((n : ℝ) + 1))⁻¹)
    (hG.mono fun _ hω => hω.tendsto_slope_one_div_add_one)

/-- **The derivative of a strongly measurable family is strongly measurable.** -/
theorem stronglyMeasurable_of_hasDerivAt_param {G : α → ℝ → F} {G' : α → F} {x : ℝ}
    (hG : ∀ ω, HasDerivAt (G ω) (G' ω) x) (hm : ∀ s, StronglyMeasurable fun ω => G ω s) :
    StronglyMeasurable G' :=
  stronglyMeasurable_of_tendsto (atTop : Filter ℕ)
    (fun n => ((hm (x + 1 / ((n : ℝ) + 1))).sub (hm x)).const_smul (1 / ((n : ℝ) + 1))⁻¹)
    (tendsto_pi_nhds.2 fun ω => (hG ω).tendsto_slope_one_div_add_one)

/-- A function which is everywhere the derivative of another function is strongly measurable. -/
theorem stronglyMeasurable_of_forall_hasDerivAt {f f' : ℝ → F}
    (hf : ∀ y, HasDerivAt f (f' y) y) : StronglyMeasurable f' := by
  have hfc : Continuous f := continuous_iff_continuousAt.2 fun y => (hf y).continuousAt
  exact stronglyMeasurable_of_hasDerivAt_param (G := fun y s => f (y + s)) (x := 0)
    (fun y => HasDerivAt.comp_const_add y 0 (by simpa only [add_zero] using hf y))
    fun s => (hfc.comp (continuous_add_const s)).stronglyMeasurable

end MeasureTheory
