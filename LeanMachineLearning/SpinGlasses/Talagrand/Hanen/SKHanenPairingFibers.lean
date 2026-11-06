/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.Hanen.SKHanenCriticalChoices
public import LeanMachineLearning.ForMathlib.Data.Sym.Sym2

/-!
# Endpoint choices inside an ordered-pairing class

Each derivative pair joining two difference labels is one of the sorted endpoint choices
between those two disjoint replica pairs. Sorting forgets orientation, not endpoint identity.
-/

@[expose] public section

open Finset
open scoped BigOperators
namespace SpinGlasses

/-- A derivative pair belongs to a specified two-label block exactly when it is one of
the sorted cross choices of endpoints. No temperature or spin-integral hypotheses occur. -/
theorem skCavityPairing_fiber_pair_mem_iff {m n : ℕ}
    (pairMap : Fin (2 * m) → Fin n × Fin n)
    (hdisj : ∀ u v : Fin (2 * m), u ≠ v →
      (pairMap u).1 ≠ (pairMap v).1 ∧ (pairMap u).1 ≠ (pairMap v).2 ∧
      (pairMap u).2 ≠ (pairMap v).1 ∧ (pairMap u).2 ≠ (pairMap v).2)
    (u v : Fin (2 * m)) (huv : u ≠ v) (p : FinPairs n) :
    (∀ w, w ∈ ({u, v} : Finset (Fin (2 * m))) ↔
      p.val.1 ∈ ({(pairMap w).1, (pairMap w).2} : Finset (Fin n)) ∨
      p.val.2 ∈ ({(pairMap w).1, (pairMap w).2} : Finset (Fin n))) ↔
    p.val ∈ (({(pairMap u).1, (pairMap u).2} : Finset (Fin n)).product
      {(pairMap v).1, (pairMap v).2}).image (fun ab => (min ab.1 ab.2, max ab.1 ab.2)) := by
  let S : Fin (2 * m) → Set (Fin n) := fun w => {(pairMap w).1, (pairMap w).2}
  have hd : Pairwise fun i j => Disjoint (S i) (S j) :=
    Finpartition.pairwise_disjoint_pair_endpoints pairMap hdisj
  have hsorted : (min p.val.1 p.val.2, max p.val.1 p.val.2) = p.val := by
    rw [min_eq_left p.property.le, max_eq_right p.property.le]
  conv_rhs => rw [← hsorted]
  simp only [mem_image, minmax_pair_eq_iff, Prod.exists]
  have h := hits_pair_iff_of_pairwiseDisjoint S hd huv p.val.1 p.val.2
  simp only [mem_insert, mem_singleton, S, Set.mem_insert_iff, Set.mem_singleton_iff] at h ⊢
  rw [h]
  constructor
  · rintro (⟨ha, hb⟩ | ⟨ha, hb⟩)
    · refine ⟨p.val.1, p.val.2, Finset.mem_product.mpr ?_, Or.inl ⟨rfl, rfl⟩⟩
      simpa only [mem_insert, mem_singleton] using And.intro ha hb
    · refine ⟨p.val.2, p.val.1, Finset.mem_product.mpr ?_, Or.inr ⟨rfl, rfl⟩⟩
      simpa only [mem_insert, mem_singleton] using And.intro hb ha
  · rintro ⟨a, b, hp, hE⟩
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hp
    simp only [mem_insert, mem_singleton] at ha hb
    rcases hE with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h1 ▸ ha, h2 ▸ hb⟩
    · exact Or.inr ⟨h2 ▸ hb, h1 ▸ ha⟩

/-- Each ordered-pairing class is a product of four-element sets of sorted endpoint
choices. The finite-set description can be used directly with `Finset.prod_univ_sum`. -/
theorem skCavityPairing_fiber_eq_piFinset {m n : ℕ}
    (pairMap : Fin (2 * m) → Fin n × Fin n)
    (hxy : ∀ v, (pairMap v).1 ≠ (pairMap v).2)
    (hdisj : ∀ u v : Fin (2 * m), u ≠ v →
      (pairMap u).1 ≠ (pairMap v).1 ∧ (pairMap u).1 ≠ (pairMap v).2 ∧
      (pairMap u).2 ≠ (pairMap v).1 ∧ (pairMap u).2 ≠ (pairMap v).2)
    (Pe : Σ P : Finpartition.Pairing (univ : Finset (Fin (2 * m))), Fin m ≃ P.val.parts) :
    ∃ u v : Fin m → Fin (2 * m), (∀ i, u i ≠ v i ∧ (Pe.2 i).val = {u i, v i}) ∧
      let S := fun i => (univ : Finset (FinPairs n)).filter fun p =>
        p.val ∈ (({(pairMap (u i)).1, (pairMap (u i)).2} : Finset (Fin n)).product
          {(pairMap (v i)).1, (pairMap (v i)).2}).image
            (fun ab => (min ab.1 ab.2, max ab.1 ab.2))
      (∀ i, (S i).card = 4) ∧
        (univ.filter fun p : Fin m → FinPairs n => ∀ i w, w ∈ (Pe.2 i).val ↔
          (p i).val.1 ∈ ({(pairMap w).1, (pairMap w).2} : Finset (Fin n)) ∨
          (p i).val.2 ∈ ({(pairMap w).1, (pairMap w).2} : Finset (Fin n))) =
          Fintype.piFinset S := by
  choose u v hne hB using fun i => card_eq_two.mp (Pe.1.property _ (Pe.2 i).property)
  refine ⟨u, v, (fun i => ⟨hne i, hB i⟩), ?_⟩
  intro S
  constructor
  · intro i
    have hd : Disjoint ({(pairMap (u i)).1, (pairMap (u i)).2} : Finset (Fin n))
        {(pairMap (v i)).1, (pairMap (v i)).2} := by
      simpa only [disjoint_insert_left, disjoint_singleton_left, mem_insert,
        mem_singleton, not_or, and_assoc] using hdisj (u i) (v i) (hne i)
    rw [Finset.card_orderedPairs_sorted_product _ _ hd, card_pair (hxy _), card_pair (hxy _)]
  · ext p
    simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset]
    apply forall_congr'
    intro i
    rw [hB i]
    simpa only [S, mem_filter, mem_univ, true_and] using
      skCavityPairing_fiber_pair_mem_iff pairMap hdisj (u i) (v i) (hne i) (p i)

end SpinGlasses
