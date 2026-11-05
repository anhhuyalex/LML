/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
# Grouping a finite sum by a relation on its support

A summand need only belong to a unique class when it is nonzero. This avoids choosing
arbitrary class labels for zero terms when a combinatorial classification is conditional.
-/

@[expose] public section

open scoped BigOperators
namespace Finset

/-- Group a sum by relation classes, assuming unique membership only on its support.
The index sets are arbitrary finite sets and the values lie in any additive commutative monoid. -/
theorem sum_eq_sum_filter_of_existsUnique {ι κ M : Type*} [AddCommMonoid M]
    (s : Finset ι) (t : Finset κ) (R : ι → κ → Prop)
    [∀ i k, Decidable (R i k)] (f : ι → M)
    (h : ∀ i ∈ s, f i ≠ 0 → ∃! k, k ∈ t ∧ R i k) :
    (∑ i ∈ s, f i) = ∑ k ∈ t, ∑ i ∈ s with R i k, f i := by
  calc
    _ = ∑ i ∈ s, ∑ k ∈ t, if R i k then f i else 0 := by
      apply sum_congr rfl
      intro i hi
      by_cases hz : f i = 0
      · simp only [hz, ite_self, sum_const_zero]
      · obtain ⟨k, hk, hu⟩ := h i hi hz
        symm
        rw [sum_eq_single k]
        · exact ite_eq_left hk.2
        · intro j hj hne
          exact ite_eq_right (fun hR => hne (hu j ⟨hj, hR⟩))
        · intro hnot
          exact False.elim (hnot hk.1)
    _ = _ := by rw [sum_comm]; simp only [sum_filter]

end Finset
