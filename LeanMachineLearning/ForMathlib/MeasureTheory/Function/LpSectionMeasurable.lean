/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.MeasureTheory.Constructions.BorelSpace.MeasurableOfDist
public import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Measurability of the `L²` class of a parametrized family of functions

Mathlib puts no `MeasurableSpace` on `Lp`.  For a jointly measurable `F : α × β → E` whose sections
`F (a, ·)` all lie in `Lᵖ(ν, E)`, we show that the `Lᵖ` class of the section is a measurable
function of the parameter `a` for any Borel structure on the separable space `Lᵖ(ν, E)`.  The proof
is the Pettis argument made explicit: `‖[F (a, ·)] - d‖ = (∫ ‖F (a, b) - d b‖ᵖ dν(b))^{1/p}` is
measurable in `a` (Fubini) for every `d ∈ Lᵖ(ν, E)`, and `measurable_of_measurable_dist` applies.

## Main declarations

* `MeasureTheory.inner_toLp_two`: `⟪[f], [g]⟫ = ∫ f g` for the `L²` classes of `f, g`.
* `MeasureTheory.measurable_toLp_section`: the `Lᵖ` class of a section is measurable in the
  parameter (`1 ≤ p < ∞`, values in a second countable normed group).
-/

@[expose] public section

open scoped RealInnerProductSpace ENNReal

namespace MeasureTheory

variable {β : Type*} [MeasurableSpace β] {ν : Measure β}

/-- The inner product of the `L²` classes of two functions is the integral of their product. -/
theorem inner_toLp_two {f g : β → ℝ} (hf : MemLp f 2 ν) (hg : MemLp g 2 ν) :
    ⟪hf.toLp f, hg.toLp g⟫ = ∫ b, f b * g b ∂ν := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with b hb1 hb2
  simp [hb1, hb2, mul_comm]

/-- The squared `L²` norm of the class of a function is the integral of its square. -/
theorem norm_sq_toLp_two {f : β → ℝ} (hf : MemLp f 2 ν) :
    ‖hf.toLp f‖ ^ 2 = ∫ b, f b ^ 2 ∂ν := by
  rw [← real_inner_self_eq_norm_sq, inner_toLp_two]
  simp only [sq]

/-- **The `Lᵖ` class of a measurable family of `Lᵖ` sections is measurable** in the parameter,
for `1 ≤ p < ∞`, values in a second countable normed group, and any Borel σ-algebra on the
separable space `Lᵖ(ν, E)`. -/
theorem measurable_toLp_section {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] {p : ℝ≥0∞} (hp₀ : p ≠ 0)
    (hp : p ≠ ∞) [Fact (1 ≤ p)] [SFinite ν] [MeasurableSpace (Lp E p ν)] [BorelSpace (Lp E p ν)]
    [TopologicalSpace.SeparableSpace (Lp E p ν)] {F : α × β → E} (hF : Measurable F)
    (hmem : ∀ a, MemLp (fun b => F (a, b)) p ν) :
    Measurable fun a => (hmem a).toLp (fun b => F (a, b)) := by
  refine measurable_of_measurable_dist fun d => ?_
  have hd : MemLp (⇑d) p ν := Lp.memLp d
  have hdist : (fun a => dist ((hmem a).toLp (fun b => F (a, b))) d) =
      fun a => (∫ b, ‖F (a, b) - d b‖ ^ p.toReal ∂ν) ^ p.toReal⁻¹ := by
    ext a
    have key : (hmem a).toLp (fun b => F (a, b)) - d =
        ((hmem a).sub hd).toLp ((fun b => F (a, b)) - ⇑d) := by
      rw [MemLp.toLp_sub (hmem a) hd, Lp.toLp_coeFn d hd]
    rw [dist_eq_norm, key, Lp.norm_toLp, toReal_eLpNorm ((hmem a).sub hd).aestronglyMeasurable,
      lpNorm_eq_integral_norm_rpow_toReal hp₀ hp ((hmem a).sub hd).aestronglyMeasurable]
    rfl
  rw [hdist]
  have hdm : Measurable fun q : α × β => d q.2 :=
    (Lp.stronglyMeasurable d).measurable.comp measurable_snd
  exact ((((hF.sub hdm).norm.pow_const p.toReal).stronglyMeasurable.integral_prod_right').measurable
    ).pow_const _

end MeasureTheory
