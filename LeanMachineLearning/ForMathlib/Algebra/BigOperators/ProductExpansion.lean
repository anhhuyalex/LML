/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset


/-!
# Separating the constant, linear and higher terms of a finite product

This is the exact algebra behind last-site product expansions. The remainder is the
explicit sum over subsets containing at least two corrections, not an existential error.
-/

@[expose] public section

open scoped BigOperators

namespace Finset

/-- Expand a product, retaining the terms containing zero or one correction and summing
explicitly over all terms with at least two corrections. Valid over any commutative semiring. -/
theorem prod_add_eq_prod_add_single_add_rest {ι K : Type*} [DecidableEq ι] [CommSemiring K]
    (s : Finset ι) (u v : ι → K) :
    (∏ i ∈ s, (u i + v i)) = (∏ i ∈ s, u i) +
      (∑ i ∈ s, v i * ∏ j ∈ s.erase i, u j) +
      ∑ t ∈ s.powerset with 2 ≤ t.card, (∏ i ∈ t, v i) * ∏ j ∈ s \ t, u j := by
  let Q : Finset ι → K := fun t => (∏ i ∈ t, v i) * ∏ j ∈ s \ t, u j
  have hzero : (s.powerset.filter fun t => t.card = 0) = {∅} := by
    ext t
    simp only [mem_filter, mem_powerset, card_eq_zero, mem_singleton]
    exact ⟨fun h => h.2, fun h => ⟨h ▸ empty_subset s, h⟩⟩
  have hone : (s.powerset.filter fun t => t.card = 1) = s.image singleton := by
    ext t
    simp only [mem_filter, mem_powerset, mem_image]
    constructor
    · rintro ⟨ht, hc⟩
      obtain ⟨i, rfl⟩ := card_eq_one.mp hc
      exact ⟨i, ht (mem_singleton_self i), rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨singleton_subset_iff.mpr hi, card_singleton i⟩
  have hpart : (∑ t ∈ s.powerset, Q t) =
      (∑ t ∈ s.powerset with t.card = 0, Q t) +
      (∑ t ∈ s.powerset with t.card = 1, Q t) +
      ∑ t ∈ s.powerset with 2 ≤ t.card, Q t := by
    simp only [sum_filter]
    rw [← sum_add_distrib, ← sum_add_distrib]
    apply sum_congr rfl
    intro t ht
    by_cases h0 : t.card = 0
    · simp [h0]
    by_cases h1 : t.card = 1
    · simp [h1]
    have h2 : 2 ≤ t.card := by omega
    simp [h0, h1, h2]
  rw [show (∏ i ∈ s, (u i + v i)) = ∑ t ∈ s.powerset, Q t by
    simpa only [add_comm] using prod_add v u s, hpart, hzero, hone]
  simp only [sum_singleton, Q, prod_empty, sdiff_empty, one_mul]
  congr 1
  rw [sum_image (fun i _ j _ hij => singleton_injective hij)]
  simp only [prod_singleton, sdiff_singleton_eq_erase]

end Finset
