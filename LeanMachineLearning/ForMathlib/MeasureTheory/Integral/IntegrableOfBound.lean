/-
Copyright (c) 2026 LML contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML contributors
-/
module

public import Mathlib.Data.Fintype.Prod
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn

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

/-- A bounded measurable real function against a finite measure is integrable.
This is Mathlib's `Integrable.of_bound` combined with `Real.norm_eq_abs`. -/
theorem integrable_of_measurable_bound {β : Type*} [MeasurableSpace β] {m : Measure β}
    [IsFiniteMeasure m] {G : β → ℝ} (hG : Measurable G) {M : ℝ} (hM : ∀ x, |G x| ≤ M) :
    Integrable G m :=
  (integrable_const M).mono' hG.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hM x)

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

/-- A finite sum with scalar coefficients can be moved through an inner integral against a
measure depending on the outer variable, then through the outer integral. -/
theorem integral_integral_finset_sum_mul {Ω α ι : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (P : Measure Ω) (κ : Ω → Measure α) (s : Finset ι) (c : ι → ℝ) (f : ι → α → ℝ)
    (hinner : ∀ i ∈ s, ∀ ω, Integrable (f i) (κ ω))
    (houter : ∀ i ∈ s, Integrable (fun ω => ∫ x, f i x ∂κ ω) P) :
    ∫ ω, ∫ x, ∑ i ∈ s, c i * f i x ∂κ ω ∂P =
      ∑ i ∈ s, c i * ∫ ω, ∫ x, f i x ∂κ ω ∂P := by
  have hlin := integral_integral_finset_sum P κ s (fun i x => c i * f i x)
    (fun i hi ω => (hinner i hi ω).const_mul _)
    (fun i hi => by
      simp_rw [integral_const_mul]
      exact (houter i hi).const_mul _)
  simp_rw [integral_const_mul] at hlin
  exact hlin

/-- For a probability kernel and bounded measurable functions, swapping a double integral
with a finite sum requires only that the outer integrals are integrable. -/
theorem integral_integral_finset_sum_of_bound {Ω α ι : Type*} [MeasurableSpace Ω]
    [MeasurableSpace α] (P : Measure Ω) (κ : Ω → Measure α) [∀ ω, IsProbabilityMeasure (κ ω)]
    (s : Finset ι) (f : ι → α → ℝ) (hf : ∀ i ∈ s, Measurable (f i))
    (hfb : ∀ i ∈ s, ∃ M, ∀ x, |f i x| ≤ M)
    (houter : ∀ i ∈ s, Integrable (fun ω => ∫ x, f i x ∂κ ω) P) :
    ∫ ω, ∫ x, ∑ i ∈ s, f i x ∂κ ω ∂P =
      ∑ i ∈ s, ∫ ω, ∫ x, f i x ∂κ ω ∂P :=
  integral_integral_finset_sum P κ s f
    (fun i hi _ => integrable_of_measurable_bound (hf i hi) (hfb i hi).choose_spec)
    houter

/-- A double finite sum can be moved through an inner integral against a probability kernel,
then through the outer integral, for bounded measurable functions. -/
theorem integral_integral_sum_sum_of_bound {Ω α ι κ : Type*} [MeasurableSpace Ω]
    [MeasurableSpace α] [Fintype ι] [Fintype κ] (P : Measure Ω) (Q : Ω → Measure α)
    [∀ ω, IsProbabilityMeasure (Q ω)] (f : ι → κ → α → ℝ)
    (hf : ∀ i j, Measurable (f i j)) (hfb : ∀ i j, ∃ M, ∀ x, |f i j x| ≤ M)
    (houter : ∀ i j, Integrable (fun ω => ∫ x, f i j x ∂Q ω) P) :
    ∫ ω, ∫ x, ∑ i, ∑ j, f i j x ∂Q ω ∂P =
      ∑ i, ∑ j, ∫ ω, ∫ x, f i j x ∂Q ω ∂P := by
  have := integral_integral_finset_sum_of_bound P Q (Finset.univ : Finset (ι × κ))
    (fun p x => f p.1 p.2 x) (fun p _ => hf p.1 p.2) (fun p _ => hfb p.1 p.2)
    (fun p _ => houter p.1 p.2)
  simpa only [Fintype.sum_prod_type] using this

end MeasureTheory
