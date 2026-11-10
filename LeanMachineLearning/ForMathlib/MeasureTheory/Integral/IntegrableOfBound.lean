/-
Copyright (c) 2026 LML contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.Analysis.Convex.Integral

/-!
# Integrability of the integral of a bounded function against random probability measures

If `κ ω` is a probability measure for every `ω` and `f` is bounded, the function
`ω ↦ ∫ f d(κ ω)` is bounded by the same constant, so it is integrable against a finite measure
as soon as it is a.e. strongly measurable. This is the bounded-observable step for Gibbs or replica
averages, where `κ ω` is a random Gibbs measure or a power of one.
-/

@[expose] public section

open MeasureTheory

namespace MeasureTheory

/-- A bounded function integrated against random probability measures gives an integrable
function of the randomness, once that function is a.e. strongly measurable (for real values,
a.e. measurable). The values may lie in any normed space. -/
theorem integrable_integral_of_bound {Ω α E : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {P : Measure Ω} [IsFiniteMeasure P] {κ : Ω → Measure α} [∀ ω, IsProbabilityMeasure (κ ω)]
    {f : α → E} {C : ℝ} (hC : ∀ x, ‖f x‖ ≤ C)
    (hm : AEStronglyMeasurable (fun ω => ∫ x, f x ∂κ ω) P) :
    Integrable (fun ω => ∫ x, f x ∂κ ω) P := by
  refine Integrable.of_bound hm C (ae_of_all _ fun ω => ?_)
  exact (norm_integral_le_integral_norm _).trans
    ((integral_mono_of_nonneg (ae_of_all _ fun x => norm_nonneg (f x))
      (integrable_const C) (ae_of_all _ hC)).trans (by simp))

/-- A finite sum can be moved through an inner integral against a measure that depends on the
outer variable, then through the outer integral. Only integrability of the summands is needed. -/
theorem integral_integral_finset_sum {Ω α ι : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (P : Measure Ω) (κ : Ω → Measure α) (s : Finset ι) (f : ι → α → ℝ)
    (hinner : ∀ i ∈ s, ∀ ω, Integrable (f i) (κ ω))
    (houter : ∀ i ∈ s, Integrable (fun ω => ∫ x, f i x ∂κ ω) P) :
    ∫ ω, ∫ x, ∑ i ∈ s, f i x ∂κ ω ∂P =
      ∑ i ∈ s, ∫ ω, ∫ x, f i x ∂κ ω ∂P := by
  have h (ω : Ω) : ∫ x, ∑ i ∈ s, f i x ∂κ ω =
      ∑ i ∈ s, ∫ x, f i x ∂κ ω :=
    integral_finsetSum s fun i hi => hinner i hi ω
  simp_rw [h]
  exact integral_finsetSum s houter

/-- **Jensen's inequality for a finite sum of convex functions**:
`∑ i ∈ s, g i (∫ ω, h i ω ∂P) ≤ ∫ ω, ∑ i ∈ s, g i (h i ω) ∂P` for a probability measure `P`. -/
theorem sum_convex_integral_le {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (s : Finset ι) (h : ι → Ω → ℝ) (g : ι → ℝ → ℝ)
    (hg : ∀ i ∈ s, ConvexOn ℝ Set.univ (g i)) (hgc : ∀ i ∈ s, Continuous (g i))
    (hint1 : ∀ i ∈ s, Integrable (h i) P)
    (hint2 : ∀ i ∈ s, Integrable (fun ω => g i (h i ω)) P) :
    ∑ i ∈ s, g i (∫ ω, h i ω ∂P) ≤ ∫ ω, ∑ i ∈ s, g i (h i ω) ∂P := by
  have hsum : ∑ i ∈ s, ∫ ω, g i (h i ω) ∂P = ∫ ω, ∑ i ∈ s, g i (h i ω) ∂P :=
    (integral_finsetSum s hint2).symm
  rw [← hsum]
  refine Finset.sum_le_sum fun i hi => ?_
  exact (hg i hi).map_integral_le (hgc i hi).continuousOn isClosed_univ
    (Filter.Eventually.of_forall fun _ => Set.mem_univ _) (hint1 i hi) (hint2 i hi)

/-- **Jensen for a vector of bounded functions**: `∑ᵢ (∫ hᵢ)² ≤ ∫ ∑ᵢ hᵢ²` for a probability
measure. -/
theorem sum_sq_integral_le {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] {P : Measure Ω}
    [IsProbabilityMeasure P] (h : ι → Ω → ℝ) (hm : ∀ i, Measurable (h i)) {M : ℝ}
    (hb : ∀ i ω, |h i ω| ≤ M) :
    ∑ i, (∫ ω, h i ω ∂P) ^ 2 ≤ ∫ ω, ∑ i, h i ω ^ 2 ∂P := by
  have hint : ∀ i, Integrable (h i) P := fun i =>
    Integrable.of_bound (hm i).aestronglyMeasurable M
      (Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hb i ω)
  have hint2 : ∀ i, Integrable (fun ω => h i ω ^ 2) P := fun i =>
    Integrable.of_bound ((hm i).pow_const 2).aestronglyMeasurable (M ^ 2)
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (hb i ω) 2)
  exact sum_convex_integral_le Finset.univ h (fun _ t => t ^ 2)
    (fun _ _ => Even.convexOn_pow (𝕜 := ℝ) (by decide : Even 2))
    (fun _ _ => continuous_pow 2)
    (fun i _ => hint i) (fun i _ => hint2 i)

end MeasureTheory
