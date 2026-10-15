/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.MeasureTheory.Constructions.BorelSpace.MeasurableOfDist
public import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Measurability of the `L²` class of a parametrized family of functions

Mathlib puts no `MeasurableSpace` on `Lp`.  For a jointly measurable `F : α × β → ℝ` whose sections
`F (a, ·)` are all square-integrable, we show that the `L²(ν)` class of the section is a measurable
function of the parameter `a` for any Borel structure on the separable space `L²(ν)`.  The proof
is the Pettis argument made explicit: `‖[F (a, ·)] - d‖² = ∫ (F (a, b) - d b)² dν(b)` is measurable
in `a` (Fubini) for every `d ∈ L²(ν)`, and `measurable_of_measurable_dist` applies.

## Main declarations

* `MeasureTheory.inner_toLp_two`: `⟪[f], [g]⟫ = ∫ f g` for the `L²` classes of `f, g`.
* `MeasureTheory.measurable_toLp_section`: the `L²` class of a section is measurable in the
  parameter.
-/

@[expose] public section

open scoped RealInnerProductSpace

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

/-- **The `L²` class of a measurable family of square-integrable sections is measurable** in the
parameter, for any Borel σ-algebra on the separable space `L²(ν)`. -/
theorem measurable_toLp_section {α : Type*} [MeasurableSpace α] [SFinite ν]
    [MeasurableSpace (Lp ℝ 2 ν)] [BorelSpace (Lp ℝ 2 ν)]
    [TopologicalSpace.SeparableSpace (Lp ℝ 2 ν)]
    {F : α × β → ℝ} (hF : Measurable F) (hmem : ∀ a, MemLp (fun b => F (a, b)) 2 ν) :
    Measurable fun a => (hmem a).toLp (fun b => F (a, b)) := by
  refine measurable_of_measurable_dist fun d => ?_
  have hd : MemLp (⇑d) 2 ν := Lp.memLp d
  have hdist : (fun a => dist ((hmem a).toLp (fun b => F (a, b))) d) =
      fun a => Real.sqrt (∫ b, (F (a, b) - d b) ^ 2 ∂ν) := by
    ext a
    have key : (hmem a).toLp (fun b => F (a, b)) - d =
        ((hmem a).sub hd).toLp ((fun b => F (a, b)) - ⇑d) := by
      rw [MemLp.toLp_sub (hmem a) hd, Lp.toLp_coeFn d hd]
    rw [dist_eq_norm, key, ← Real.sqrt_sq (norm_nonneg _), norm_sq_toLp_two]
    rfl
  rw [hdist]
  have hdm : Measurable fun p : α × β => d p.2 :=
    (Lp.stronglyMeasurable d).measurable.comp measurable_snd
  exact Real.continuous_sqrt.measurable.comp
    (((hF.sub hdm).pow_const 2).stronglyMeasurable.integral_prod_right').measurable

end MeasureTheory
