/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Topology.MetricSpace.OpenUnionBalls
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
  rw [Metric.isOpen_eq_iUnion_ball_dense_rat hDd hU]
  simp only [preimage_iUnion]
  exact MeasurableSet.iUnion fun d => MeasurableSet.iUnion fun r => MeasurableSet.iUnion fun _ =>
    measurableSet_lt (hf d) measurable_const
