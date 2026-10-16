/-
Copyright (c) 2026 LML contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML contributors
-/
module

public import Mathlib.MeasureTheory.Measure.GiryMonad
public import Mathlib.Order.Disjointed
public import Mathlib.Probability.ConditionalProbability

/-!
# Restricting measures to the cells of a partition

* `MeasureTheory.Measure.measurable_restrict`: `μ ↦ μ.restrict s` is measurable for the Giry
  σ-algebra.
* `ProbabilityTheory.sum_meas_smul_cond`, `sum_meas_smul_cond_of_iUnion_eq_univ`: the law of total
  probability for a countable measurable family of disjoint sets,
  `∑ᵢ μ(Aᵢ) • μ[|Aᵢ] = μ.restrict (⋃ᵢ Aᵢ)` (`= μ` for a partition). Mathlib's
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

/-- Scaling the conditional measure `μ[|s]` by `μ s` recovers the restricted measure `μ.restrict s`,
provided `μ s ≠ ∞`. -/
theorem MeasureTheory.Measure.smul_cond_eq_restrict (μ : Measure α) {s : Set α} (hs : μ s ≠ ∞) :
    μ s • μ[|s] = μ.restrict s := by
  by_cases h0 : μ s = 0
  · simp [h0]
  · simp [cond, smul_smul, ENNReal.mul_inv_cancel h0 hs]

namespace ProbabilityTheory

/-- **Law of total probability** for a countable measurable family of pairwise disjoint sets of
finite mass: `∑ᵢ μ(Aᵢ) • μ[|Aᵢ] = μ.restrict (⋃ᵢ Aᵢ)`. -/
theorem sum_meas_smul_cond {ι : Type*} [Countable ι] {μ : Measure α} {A : ι → Set α}
    (hA : ∀ i, MeasurableSet (A i)) (hdisj : Pairwise (Function.onFun Disjoint A))
    (hfin : ∀ i, μ (A i) ≠ ∞) :
    (Measure.sum fun i => μ (A i) • μ[|A i]) = μ.restrict (⋃ i, A i) := by
  simp_rw [Measure.smul_cond_eq_restrict _ (hfin _)]
  exact (Measure.restrict_iUnion hdisj hA).symm

/-- The covering case: for a countable measurable partition into sets of finite mass,
`μ = ∑ᵢ μ(Aᵢ) • μ[|Aᵢ]`. -/
theorem sum_meas_smul_cond_of_iUnion_eq_univ {ι : Type*} [Countable ι] {μ : Measure α}
    {A : ι → Set α} (hA : ∀ i, MeasurableSet (A i)) (hdisj : Pairwise (Function.onFun Disjoint A))
    (hcover : ⋃ i, A i = Set.univ) (hfin : ∀ i, μ (A i) ≠ ∞) :
    (Measure.sum fun i => μ (A i) • μ[|A i]) = μ := by
  rw [sum_meas_smul_cond hA hdisj hfin, hcover, Measure.restrict_univ]

end ProbabilityTheory

/-- A σ-finite measure admits a countable measurable partition into sets of finite mass. (The
cells may have mass zero; for a finite nonzero measure they cannot all have positive mass.) -/
theorem MeasureTheory.exists_measurable_partition_of_sigmaFinite (μ : Measure α) [SigmaFinite μ] :
    ∃ A : ℕ → Set α, (∀ i, MeasurableSet (A i)) ∧ Pairwise (Function.onFun Disjoint A) ∧
      ⋃ i, A i = Set.univ ∧ ∀ i, μ (A i) < ∞ :=
  ⟨disjointed (spanningSets μ), MeasurableSet.disjointed (measurableSet_spanningSets μ),
    disjoint_disjointed _, by rw [iUnion_disjointed, iUnion_spanningSets],
    fun i => (measure_mono (disjointed_subset _ i)).trans_lt (measure_spanningSets_lt_top μ i)⟩
