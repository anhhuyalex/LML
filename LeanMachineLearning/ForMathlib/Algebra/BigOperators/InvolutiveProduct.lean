/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.BigOperators

/-! # Removing repeated factors from products of involutions -/

@[expose] public section

open Finset

/-- A product of involutions indexed with repetitions has a square-free support
independent of their values. This support has size at most the number of factors. -/
theorem Finset.exists_prod_eq_prod_of_mul_self_eq_one {ι κ G : Type*} [CommMonoid G]
    (s : Finset ι) (p : ι → κ) :
    ∃ J : Finset κ, J.card ≤ s.card ∧
      ∀ f : κ → G, (∀ i, f i * f i = 1) → (∏ j ∈ s, f (p j)) = ∏ i ∈ J, f i := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨∅, by simp, by simp⟩
  | @insert i s hi ih =>
    obtain ⟨J, hcard, heq⟩ := ih
    by_cases hpi : p i ∈ J
    · refine ⟨J.erase (p i), ?_, ?_⟩
      · rw [Finset.card_insert_of_notMem hi]
        exact (Finset.card_erase_le).trans (hcard.trans (Nat.le_succ _))
      · intro f hf
        rw [Finset.prod_insert hi, heq f hf]
        calc
          f (p i) * ∏ j ∈ J, f j =
              f (p i) * (f (p i) * ∏ j ∈ J.erase (p i), f j) := by
            rw [Finset.mul_prod_erase _ _ hpi]
          _ = _ := by rw [← mul_assoc, hf, one_mul]
    · refine ⟨insert (p i) J, ?_, ?_⟩
      · rw [Finset.card_insert_of_notMem hi, Finset.card_insert_of_notMem hpi]
        exact Nat.succ_le_succ hcard
      · intro f hf
        rw [Finset.prod_insert hi, Finset.prod_insert hpi, heq f hf]


/-- Products of pairs of involutions admit a square-free support of size at most
twice the number of pairs, even when the pairs share or repeat indices. -/
theorem Finset.exists_pair_prod_eq_prod_of_mul_self_eq_one {ι κ G : Type*}
    [CommMonoid G]
    (s : Finset ι) (p : ι → κ × κ) :
    ∃ J : Finset κ, J.card ≤ 2 * s.card ∧
      ∀ f : κ → G, (∀ i, f i * f i = 1) →
        (∏ j ∈ s, f (p j).1 * f (p j).2) = ∏ i ∈ J, f i := by
  let q : ι × Bool → κ := fun x => if x.2 then (p x.1).1 else (p x.1).2
  obtain ⟨J, hJ, heq⟩ :=
    Finset.exists_prod_eq_prod_of_mul_self_eq_one (G := G) (s.product Finset.univ) q
  refine ⟨J, by simpa [Finset.card_product, Nat.mul_comm] using hJ, ?_⟩
  intro f hf
  simpa [q, Finset.prod_product, Fintype.prod_bool, mul_comm] using heq f hf
