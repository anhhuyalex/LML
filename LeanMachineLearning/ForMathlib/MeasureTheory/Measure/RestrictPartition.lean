/-
Copyright (c) 2026 LML contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML contributors
-/
module

public import Mathlib.MeasureTheory.Measure.GiryMonad
public import Mathlib.Probability.ConditionalProbability

/-!
# Restricting measures to the cells of a partition

* `MeasureTheory.Measure.measurable_restrict`: `μ ↦ μ.restrict s` is measurable for the Giry
  σ-algebra.
* `ProbabilityTheory.sum_meas_smul_cond_of_iUnion_eq_univ`: the law of total probability for a
  countable measurable partition, `μ = ∑ᵢ μ(Aᵢ) • μ[|Aᵢ]`. Mathlib's
  `sum_meas_smul_cond_fiber` covers only finitely many cells of a finite measure.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {α : Type*} [MeasurableSpace α]

/-- Restriction to a fixed measurable set is a measurable map on the space of measures. -/
theorem MeasureTheory.Measure.measurable_restrict {s : Set α} (hs : MeasurableSet s) :
    Measurable fun μ : Measure α => μ.restrict s :=
  Measure.measurable_of_measurable_coe _ fun t ht => by
    simp_rw [Measure.restrict_apply ht]
    exact Measure.measurable_coe (ht.inter hs)

namespace ProbabilityTheory

/-- **Law of total probability** for a countable measurable partition into sets of finite mass:
`μ = ∑ᵢ μ(Aᵢ) • μ[|Aᵢ]`. -/
theorem sum_meas_smul_cond_of_iUnion_eq_univ {ι : Type*} [Countable ι] {μ : Measure α}
    {A : ι → Set α} (hA : ∀ i, MeasurableSet (A i)) (hdisj : Pairwise (Function.onFun Disjoint A))
    (hcover : ⋃ i, A i = Set.univ) (hfin : ∀ i, μ (A i) ≠ ∞) :
    (Measure.sum fun i => μ (A i) • μ[|A i]) = μ := by
  ext t ht
  rw [Measure.sum_apply _ ht]
  have hterm : ∀ i, (μ (A i) • μ[|A i]) t = μ (A i ∩ t) := fun i => by
    rw [Measure.smul_apply, cond_apply (hA i), smul_eq_mul]
    by_cases h0 : μ (A i) = 0
    · simp [h0, measure_mono_null Set.inter_subset_left h0]
    · rw [← mul_assoc, ENNReal.mul_inv_cancel h0 (hfin i), one_mul]
  simp_rw [hterm]
  rw [← measure_iUnion (fun i j hij => (hdisj hij).mono Set.inter_subset_left
    Set.inter_subset_left) (fun i => (hA i).inter ht), ← Set.iUnion_inter, hcover,
    Set.univ_inter]

end ProbabilityTheory
