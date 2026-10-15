/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

/-!
# Measurability into a separable metric space from the distances to points

A map `f` from a measurable space into a separable metric space with its Borel σ-algebra is
measurable as soon as `a ↦ dist (f a) d` is measurable for every point `d`: the open sets are
countable unions of balls centred at points of a countable dense set, and the preimage of a ball is
a sublevel set of a distance function.  This is the form of the Pettis measurability theorem that
is convenient in Hilbert spaces, where `dist² (f a) d` is expressed through inner products and
norms.

## Main declarations

* `measurable_of_measurable_dist`: the criterion above.
-/

@[expose] public section

open Set TopologicalSpace Metric

/-- **Measurability from distances.**  A map into a separable metric space with its Borel
σ-algebra is measurable if its distance to every point is a measurable function. -/
theorem measurable_of_measurable_dist {α β : Type*} [MeasurableSpace α] [PseudoMetricSpace β]
    [MeasurableSpace β] [BorelSpace β] [SeparableSpace β] {f : α → β}
    (hf : ∀ d, Measurable fun a => dist (f a) d) : Measurable f := by
  obtain ⟨D, hDc, hDd⟩ := exists_countable_dense β
  have : Countable D := hDc.to_subtype
  refine measurable_of_isOpen fun U hU => ?_
  have hU' : f ⁻¹' U = ⋃ (d : D) (r : ℚ) (_ : 0 < (r : ℝ) ∧ ball (d : β) r ⊆ U),
      f ⁻¹' ball (d : β) r := by
    ext x
    simp only [mem_preimage, mem_iUnion]
    refine ⟨fun hx => ?_, fun ⟨d, r, ⟨_, hr⟩, hxd⟩ => hr hxd⟩
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU _ hx
    obtain ⟨r, hr0, hrε⟩ := exists_rat_btwn (half_pos hε)
    obtain ⟨d, hdD, hxd⟩ := hDd.exists_dist_lt (f x) (by exact_mod_cast hr0 : (0 : ℝ) < r)
    refine ⟨⟨d, hdD⟩, r, ⟨by exact_mod_cast hr0, fun y hy => hball ?_⟩, hxd⟩
    rw [mem_ball] at hy ⊢
    have := dist_triangle y d (f x)
    rw [dist_comm d] at this
    linarith
  rw [hU']
  exact MeasurableSet.iUnion fun d => MeasurableSet.iUnion fun r => MeasurableSet.iUnion fun _ =>
    measurableSet_lt (hf d) measurable_const
