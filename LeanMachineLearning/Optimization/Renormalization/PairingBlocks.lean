/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.Renormalization.PairingOrderings

/-!
# Pairings as indexed disjoint blocks

An indexed family of disjoint two-element sets covering `s` specifies a pairing together
with an ordering of its blocks. The index type can be any finite type. This is the finite
enumeration bridge needed when a derivative expansion initially produces tuples of pairs.
-/

@[expose] public section

open Finset
open scoped BigOperators
namespace Finpartition

variable {α ι : Type*} [DecidableEq α] [Fintype ι]

/-- A pairing with an indexed ordering of its parts is exactly an indexed family of
disjoint two-element blocks covering the set. No linear order on the ambient set is needed.
The equivalence retains the block ordering needed to reindex finite sums; it reuses the
existing pairing type rather than introducing another representation as a named type. -/
noncomputable def Pairing.equivOrderedBlocks (s : Finset α) :
    (Σ P : Pairing s, ι ≃ P.val.parts) ≃
      {b : ι → Finset α // (∀ i, (b i).card = 2) ∧
        (Pairwise fun i j => Disjoint (b i) (b j)) ∧ univ.biUnion b = s} := by
  let f : (Σ P : Pairing s, ι ≃ P.val.parts) →
      {b : ι → Finset α // (∀ i, (b i).card = 2) ∧
        (Pairwise fun i j => Disjoint (b i) (b j)) ∧ univ.biUnion b = s} := fun Pe =>
    ⟨fun i => (Pe.2 i).val, (fun i => Pe.1.property _ (Pe.2 i).property),
      (by
        intro i j hij
        apply Pe.1.val.disjoint (Pe.2 i).property (Pe.2 j).property
        intro he
        exact hij (Pe.2.injective (Subtype.ext he))), (by
        calc
          _ = Pe.1.val.parts.biUnion id := by
            ext x
            simp only [mem_biUnion, mem_univ, true_and, id_eq]
            constructor
            · rintro ⟨i, hi⟩
              exact ⟨_, (Pe.2 i).property, hi⟩
            · rintro ⟨B, hB, hx⟩
              exact ⟨Pe.2.symm ⟨B, hB⟩, by simpa using hx⟩
          _ = s := Pe.1.val.biUnion_parts)⟩
  apply Equiv.ofBijective f
  constructor
  · rintro ⟨P, e⟩ ⟨Q, d⟩ h
    have hb : ∀ i, (e i).val = (d i).val := fun i => congrFun (congrArg Subtype.val h) i
    have hP : P = Q := by
      apply Subtype.ext
      apply Finpartition.ext
      ext B
      constructor
      · intro hB
        have he := hb (e.symm ⟨B, hB⟩)
        rw [e.apply_symm_apply] at he
        simpa only [← he] using (d (e.symm ⟨B, hB⟩)).property
      · intro hB
        have he := hb (d.symm ⟨B, hB⟩)
        rw [d.apply_symm_apply] at he
        simpa only [he] using (e (d.symm ⟨B, hB⟩)).property
    subst Q
    have he : e = d := by
      apply Equiv.ext
      intro i
      exact Subtype.ext (hb i)
    subst d
    rfl
  · rintro ⟨b, hc, hd, hcover⟩
    have hne (i) : (b i).Nonempty := card_pos.mp (by rw [hc]; decide)
    let P0 : Finpartition s :=
      ofExistsUnique (univ.image b)
        (by
          rintro B hB x hx
          obtain ⟨i, _, rfl⟩ := mem_image.mp hB
          rw [← hcover]
          exact mem_biUnion.mpr ⟨i, mem_univ _, hx⟩)
        (by
          intro x hx
          rw [← hcover] at hx
          obtain ⟨i, _, hi⟩ := mem_biUnion.mp hx
          refine ⟨b i, ⟨mem_image.mpr ⟨i, mem_univ _, rfl⟩, hi⟩, ?_⟩
          rintro B ⟨hB, hxB⟩
          obtain ⟨j, _, rfl⟩ := mem_image.mp hB
          have hji : j = i := by
            by_contra hji
            exact disjoint_left.mp (hd hji) hxB hi
          exact congrArg b hji)
        (by
          intro h
          obtain ⟨i, _, hi⟩ := mem_image.mp h
          exact (hne i).ne_empty hi)
    let P : Pairing s := ⟨P0, by
      intro B hB
      obtain ⟨i, _, rfl⟩ := mem_image.mp hB
      exact hc i⟩
    let e : ι ≃ P.val.parts := Equiv.ofBijective
      (fun i => ⟨b i, mem_image.mpr ⟨i, mem_univ _, rfl⟩⟩) ⟨by
        intro i j hij
        by_contra hneij
        have he : b i = b j := congrArg Subtype.val hij
        obtain ⟨x, hx⟩ := hne i
        exact disjoint_left.mp (hd hneij) hx (he ▸ hx), by
        rintro ⟨B, hB⟩
        obtain ⟨i, _, rfl⟩ := mem_image.mp hB
        exact ⟨i, rfl⟩⟩
    exact ⟨⟨P, e⟩, rfl⟩

/-- The equivalence retains the specified block at each index. -/
@[simp] theorem Pairing.equivOrderedBlocks_apply (s : Finset α)
    (Pe : Σ P : Pairing s, ι ≃ P.val.parts) (i : ι) :
    ((Pairing.equivOrderedBlocks s) Pe).val i = (Pe.2 i).val := rfl

/-- Disjoint two-element blocks covering a set specify a unique pairing and block ordering.
This is the inverse characterization needed to recover a pairing from derivative tuples. -/
theorem existsUnique_pairing_ordering (s : Finset α) (b : ι → Finset α)
    (hc : ∀ i, (b i).card = 2) (hd : Pairwise fun i j => Disjoint (b i) (b j))
    (hcover : univ.biUnion b = s) :
    ∃! Pe : Σ P : Pairing s, ι ≃ P.val.parts, ∀ i, (Pe.2 i).val = b i := by
  let e := Pairing.equivOrderedBlocks (ι := ι) s
  let B := (⟨b, hc, hd, hcover⟩ :
    {b : ι → Finset α // (∀ i, (b i).card = 2) ∧
      (Pairwise fun i j => Disjoint (b i) (b j)) ∧ univ.biUnion b = s})
  refine ⟨e.symm B, ?_, ?_⟩
  · intro i
    exact congrFun (congrArg Subtype.val (e.apply_symm_apply B)) i
  · intro Pe hPe
    apply e.injective
    apply Subtype.ext
    funext i
    exact (hPe i).trans (congrFun (congrArg Subtype.val (e.apply_symm_apply B)) i).symm

omit [Fintype ι] in
/-- Grouping a bijection to pairs of endpoint positions gives a unique pairing and block
ordering. The Boolean component orients a block, and is forgotten in this characterization. -/
theorem existsUnique_pairing_ordering_of_equiv [Fintype α] (e : α ≃ ι × Bool) :
    ∃! Pe : Σ P : Pairing (univ : Finset α), ι ≃ P.val.parts, ∀ i v,
      v ∈ (Pe.2 i).val ↔ (e v).1 = i := by
  let : Fintype ι := Fintype.ofInjective (fun i => e.symm (i, true))
    (fun _ _ h => congrArg Prod.fst (e.symm.injective h))
  let b : ι → Finset α := fun i => {e.symm (i, true), e.symm (i, false)}
  have hc (i) : (b i).card = 2 := by
    apply card_pair
    intro h
    have := e.symm.injective h
    simp at this
  have hd : Pairwise fun i j => Disjoint (b i) (b j) := by
    intro i j hij
    rw [disjoint_left]
    intro x hx hy
    simp only [b, mem_insert, mem_singleton] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with hy | hy
    all_goals exact hij (congrArg Prod.fst (e.symm.injective hy))
  have hm (i : ι) (v : α) : v ∈ b i ↔ (e v).1 = i := by
    simp only [b, mem_insert, mem_singleton, e.eq_symm_apply]
    constructor
    · rintro (h | h) <;> exact congrArg Prod.fst h
    · intro hi
      cases hb : (e v).2
      · exact Or.inr (Prod.ext hi hb)
      · exact Or.inl (Prod.ext hi hb)
  have hcover : univ.biUnion b = (univ : Finset α) := by
    ext v
    simp only [mem_biUnion, mem_univ, true_and, hm, iff_true]
    exact ⟨(e v).1, rfl⟩
  obtain ⟨Pe, hPe, hu⟩ := existsUnique_pairing_ordering univ b hc hd hcover
  refine ⟨Pe, ?_, ?_⟩
  · intro i v
    rw [hPe]
    exact hm i v
  · intro Q hQ
    apply hu Q
    intro i
    ext v
    exact (hQ i v).trans (hm i v).symm

end Finpartition
