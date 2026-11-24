/-
Copyright (c) 2026 LML contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Order.Interval.Finset.Fin

/-!
# Swapping with the last element of `Fin (L + 1)` on an upper interval

Swapping `n < Fin.last L` with `Fin.last L` bijects the upper interval `Finset.Ici ⟨n + 1, _⟩`
onto `(Finset.Ici n).erase (Fin.last L)`. This is the reindexing behind site-exchangeability
arguments that peel off the last coordinate of a partial sum over `Finset.Ici n`.
-/

@[expose] public section

namespace Finset

/-- **Last-element swap on upper intervals.** For `n < Fin.last L`, the sum of `g` over
`(Ici n).erase (Fin.last L)` equals the sum of `g ∘ swap n (Fin.last L)` over `Ici (n + 1)`. -/
theorem sum_Ici_erase_last_eq_sum_Ici_succ_swap {L : ℕ} {β : Type*} [AddCommMonoid β]
    (n : Fin (L + 1)) (hn : n.1 < L) (g : Fin (L + 1) → β) :
    ∑ i ∈ (Ici n).erase (Fin.last L), g i =
      ∑ j ∈ Ici (⟨n.1 + 1, by omega⟩ : Fin (L + 1)), g (Equiv.swap n (Fin.last L) j) := by
  symm
  refine Finset.sum_equiv (Equiv.swap n (Fin.last L)) (fun j => ?_) (fun j _ => rfl)
  have hnl : n ≠ Fin.last L := fun h => by simp [h] at hn
  rw [Finset.mem_Ici, Finset.mem_erase, Finset.mem_Ici, Equiv.swap_apply_def]
  by_cases h1 : j = n
  · subst h1; simp [hnl, Fin.le_def]
  · by_cases h2 : j = Fin.last L
    · subst h2; simp [h1, hnl, Fin.le_def, Fin.last]; omega
    · simp only [h1, h2, if_false, ne_eq, not_false_eq_true, true_and, Fin.le_def]
      have : j.1 ≠ n.1 := fun h => h1 (Fin.ext h)
      omega

end Finset
