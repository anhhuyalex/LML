/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.Topology.Algebra.Order.Archimedean
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.Topology.Order.IsLUB

/-!
# Distance to a finite-dimensional span as a countable infimum

For a vector `v` and a finite family `w` in a real inner product space, the squared distance from
`v` to `span (range w)` is the infimum, over *rational* coefficient vectors `c`, of the quadratic
form `‖v‖² - 2 ∑ cᵢ ⟪v, wᵢ⟫ + ∑ cᵢ cⱼ ⟪wᵢ, wⱼ⟫`. No linear independence of `w` is needed (so no
Gram-matrix inverse or pseudoinverse), and the formula only involves the inner products between
`v` and the `wᵢ`; in particular, when those inner products are measurable functions of some
parameter, so is the distance, being a countable infimum.

## Main declarations

* `infDist_span_range_sq_eq_iInf_rat`: the formula above.
* `measurable_infDist_span_range_sq`: the squared distance is measurable as soon as the inner
  products it involves are.
-/

@[expose] public section

open MeasureTheory Set
open scoped RealInnerProductSpace

theorem ciInf_range_subtype {α β γ : Type*} [ConditionallyCompleteLattice γ] (f : α → β)
    (g : β → γ) : ⨅ y : range f, g y = ⨅ a, g (f a) := by
  rw [← sInf_range, ← sInf_range]
  congr 1
  exact Set.ext fun z => ⟨fun ⟨⟨_, a, rfl⟩, h⟩ => ⟨a, h⟩, fun ⟨a, h⟩ => ⟨⟨f a, a, rfl⟩, h⟩⟩

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {ι : Type*} [Fintype ι]

/-- The squared distance from `v` to the span of a finite family `w` is the infimum, over rational
coefficient vectors `c`, of the quadratic form `‖v - ∑ cᵢ wᵢ‖²`, written in terms of the inner
products `⟪v, v⟫`, `⟪v, wᵢ⟫` and `⟪wᵢ, wⱼ⟫`. -/
theorem infDist_span_range_sq_eq_iInf_rat (v : E) (w : ι → E) :
    Metric.infDist v (Submodule.span ℝ (range w)) ^ 2 =
      ⨅ c : ι → ℚ, (⟪v, v⟫ - 2 * ∑ i, (c i : ℝ) * ⟪v, w i⟫ +
        ∑ i, ∑ j, (c i : ℝ) * (c j : ℝ) * ⟪w i, w j⟫) := by
  set T := Fintype.linearCombination ℝ w with hT
  set Q : (ι → ℝ) → ℝ := fun c => ‖v - T c‖ ^ 2 with hQ
  have hTc : Continuous T := by
    have : (T : (ι → ℝ) → E) = fun c => ∑ i, c i • w i := by
      ext c
      simp [hT, Fintype.linearCombination_apply]
    rw [this]
    fun_prop
  have hQc : Continuous Q := by fun_prop
  have hQ0 : ∀ c, 0 ≤ Q c := fun c => sq_nonneg _
  have hQe : ∀ c : ι → ℝ, Q c = ⟪v, v⟫ - 2 * ∑ i, c i * ⟪v, w i⟫ +
      ∑ i, ∑ j, c i * c j * ⟪w i, w j⟫ := by
    intro c
    have h1 : T c = ∑ i, c i • w i := by simp [hT, Fintype.linearCombination_apply]
    simp only [hQ, h1, ← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right,
      sum_inner, inner_sum, inner_smul_left, inner_smul_right, real_inner_comm v]
    simp only [Finset.mul_sum, RCLike.conj_to_real, mul_assoc]
    have h2 : ∑ x, ∑ y, c x * (c y * ⟪w y, w x⟫) = ∑ x, ∑ y, c x * (c y * ⟪w x, w y⟫) := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    rw [h2, ← Finset.mul_sum]
    ring
  -- The distance to the span is the infimum over all real coefficients.
  have hdist : Metric.infDist v (Submodule.span ℝ (range w)) = ⨅ c, ‖v - T c‖ := by
    rw [← Fintype.range_linearCombination, Metric.infDist_eq_iInf]
    exact (ciInf_range_subtype T fun y => dist v y).trans (by simp [dist_eq_norm])
  have hsq : Metric.infDist v (Submodule.span ℝ (range w)) ^ 2 = ⨅ c, Q c := by
    have hmono : Monotone Real.sqrt := Real.sqrt_monotone
    have h2 : ⨅ c, ‖v - T c‖ = Real.sqrt (⨅ c, Q c) := by
      rw [hmono.map_ciInf_of_continuousAt Real.continuous_sqrt.continuousAt
        ⟨0, fun _ ⟨c, hc⟩ => hc ▸ hQ0 c⟩]
      exact iInf_congr fun c => by simp [hQ, Real.sqrt_sq (norm_nonneg _)]
    rw [hdist, h2, Real.sq_sqrt (le_ciInf hQ0)]
  rw [hsq]
  have hdense : Dense (range (Pi.map fun _ : ι => ((↑) : ℚ → ℝ))) :=
    DenseRange.piMap fun _ => Rat.denseRange_cast
  rw [← hdense.ciInf hQc ⟨0, fun _ ⟨c, hc⟩ => hc ▸ hQ0 c⟩,
    ciInf_range_subtype (Pi.map fun _ : ι => ((↑) : ℚ → ℝ)) Q]
  refine iInf_congr fun c => ?_
  simp [hQe]

omit [Fintype ι] in
/-- The squared distance from a random vector `v x` to the span of a random finite family `w x` is
measurable as soon as the inner products `⟪v x, v x⟫`, `⟪v x, w x i⟫`, `⟪w x i, w x j⟫` are:
it is a countable infimum of measurable functions. -/
theorem measurable_infDist_span_range_sq [Finite ι] {X : Type*} [MeasurableSpace X] (v : X → E)
    (w : X → ι → E) (hvv : Measurable fun x => ⟪v x, v x⟫)
    (hvw : ∀ i, Measurable fun x => ⟪v x, w x i⟫)
    (hww : ∀ i j, Measurable fun x => ⟪w x i, w x j⟫) :
    Measurable fun x => Metric.infDist (v x) (Submodule.span ℝ (range (w x))) ^ 2 := by
  have := Fintype.ofFinite ι
  simp only [infDist_span_range_sq_eq_iInf_rat]
  refine Measurable.iInf fun c => ?_
  fun_prop
