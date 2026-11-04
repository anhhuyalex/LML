/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Set.Disjoint

/-!
# Transversals at the cardinality threshold

A list hitting every set in a disjoint family of the same size contains exactly one point
per set. The list has no repetitions or points outside the family.
-/

@[expose] public section

/-- If a list hits every set in an equally large disjoint family, its positions are in
bijection with the sets, with exactly one position in each set. Its values are distinct.
The sets and their ambient type need not be finite. -/
theorem exists_equiv_of_pairwiseDisjoint_of_hits {ι κ α : Type*} [Fintype ι] [Fintype κ]
    (S : ι → Set α) (p : κ → α) (hcard : Fintype.card ι = Fintype.card κ)
    (hdisj : Pairwise fun i j => Disjoint (S i) (S j))
    (hhit : ∀ i, ∃ j, p j ∈ S i) :
    ∃ e : ι ≃ κ, (∀ i j, p j ∈ S i ↔ e i = j) ∧ Function.Injective p := by
  choose g hg using hhit
  have hinj : Function.Injective g := by
    intro i j he
    by_contra hne
    exact Set.disjoint_left.mp (hdisj hne) (hg i) (he ▸ hg j)
  let e : ι ≃ κ := Equiv.ofBijective g
    ((Fintype.bijective_iff_injective_and_card g).mpr ⟨hinj, hcard⟩)
  have he (i : ι) : p (e i) ∈ S i := hg i
  have hiff (i : ι) (j : κ) : p j ∈ S i ↔ e i = j := by
    constructor
    · intro hj
      obtain ⟨k, rfl⟩ := e.surjective j
      have hki : k = i := by
        by_contra hne
        exact Set.disjoint_left.mp (hdisj hne) (he k) hj
      rw [hki]
    · rintro rfl
      exact he i
  refine ⟨e, hiff, ?_⟩
  intro j k heq
  obtain ⟨i, rfl⟩ := e.surjective j
  apply (hiff i k).mp
  rw [← heq]
  exact he i
