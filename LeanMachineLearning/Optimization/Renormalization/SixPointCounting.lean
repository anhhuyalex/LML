/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.Renormalization.NearlyGaussian
public import Mathlib.Data.Finset.Powerset

/-!
# Counting `(4,2)`-partitions of six labelled positions

`card_fourTwoPartition_fin_six` is not used by any other theorem in this project; it exists only
to record the count claimed informally in `NearlyGaussian.lean`'s six-point worked example. It
used to be proved by `native_decide` directly over `IsFourTwoPartition`, which was expensive to
*compile* (minutes and 100GB+ of memory, even though the runtime search itself was fast). It is
proved here instead by the honest bijective argument the theorem's own docstring already
describes: a `(4,2)`-partition is determined by its two-element block, whose complement is the
four-element block, so counting them reduces to `Finset.card_powersetCard`. This file remains a
separate leaf module so that editing `NearlyGaussian.lean` never forces recompiling this proof
(and so that any future reintroduction of an expensive `decide`/`native_decide` call elsewhere
stays similarly contained).
-/

@[expose] public section

noncomputable section

namespace Renormalization

-- The `(4,2)`-partition of `Fin 6` whose two-element block is `B`.
private noncomputable def pairPartition (B : Finset (Fin 6)) (hB : B.card = 2) :
    Finpartition (Finset.univ : Finset (Fin 6)) := by
  classical
  have hdisj :
      (↑({B, Finset.univ \ B} : Finset (Finset (Fin 6))) : Set (Finset (Fin 6))).PairwiseDisjoint
        id := by
    intro x hx y hy hxy
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hx hy
    rcases hx with hx | hx <;> rcases hy with hy | hy <;> subst hx <;> subst hy
    · exact absurd rfl hxy
    · exact Finset.disjoint_sdiff
    · exact Finset.disjoint_sdiff.symm
    · exact absurd rfl hxy
  have hsup : ({B, Finset.univ \ B} : Finset (Finset (Fin 6))).sup id = Finset.univ := by
    rw [Finset.sup_insert, Finset.sup_singleton]
    exact Finset.union_sdiff_of_subset (Finset.subset_univ B)
  exact Finpartition.ofErase ({B, Finset.univ \ B} : Finset (Finset (Fin 6)))
    (Finset.supIndep_iff_pairwiseDisjoint.mpr hdisj) hsup

private lemma pairPartition_parts (B : Finset (Fin 6)) (hB : B.card = 2) :
    (pairPartition B hB).parts = {B, Finset.univ \ B} := by
  unfold pairPartition
  simp only [Finpartition.ofErase_parts]
  apply Finset.erase_eq_of_notMem
  simp only [Finset.mem_insert, Finset.mem_singleton]
  rintro (h | h)
  · rw [← h] at hB
    simp at hB
  · have hcard : (Finset.univ \ B).card = 4 := by simp [Finset.card_sdiff, hB]
    rw [← h] at hcard
    simp at hcard

private lemma isFourTwoPartition_pairPartition (B : Finset (Fin 6)) (hB : B.card = 2) :
    IsFourTwoPartition (pairPartition B hB) := by
  rw [IsFourTwoPartition, pairPartition_parts]
  have hne : B ≠ Finset.univ \ B := by
    intro h
    have hcard : (Finset.univ \ B).card = 4 := by simp [Finset.card_sdiff, hB]
    rw [← h] at hcard
    omega
  refine ⟨Finset.card_pair hne, ?_⟩
  intro C hC
  simp only [Finset.mem_insert, Finset.mem_singleton] at hC
  rcases hC with hC | hC
  · left; rw [hC, hB]
  · right
    rw [hC]
    simp [Finset.card_sdiff, hB]

-- Every `(4,2)`-partition of `Fin 6` is `pairPartition B _` for its (unique) two-element block.
private lemma exists_twoBlock_of_isFourTwoPartition
    (P : Finpartition (Finset.univ : Finset (Fin 6))) (hP : IsFourTwoPartition P) :
    ∃ B, B.card = 2 ∧ P.parts = {B, Finset.univ \ B} := by
  obtain ⟨B, C, hBC, hPparts⟩ := Finset.card_eq_two.mp hP.1
  have hBmem : B ∈ P.parts := by rw [hPparts]; simp
  have hCmem : C ∈ P.parts := by rw [hPparts]; simp
  have hdisj : Disjoint B C := by
    have hsi := P.supIndep
    rw [Finset.supIndep_iff_pairwiseDisjoint] at hsi
    exact hsi (hPparts ▸ hBmem) (hPparts ▸ hCmem) hBC
  have hunion : B ∪ C = Finset.univ := by
    rw [← P.sup_parts, hPparts, Finset.sup_insert, Finset.sup_singleton, id_eq, id_eq,
      Finset.sup_eq_union]
  have hCeq : C = Finset.univ \ B := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
    constructor
    · intro hxC hxB
      exact (Finset.disjoint_left.mp hdisj hxB) hxC
    · intro hxB
      have hxuniv : x ∈ (Finset.univ : Finset (Fin 6)) := Finset.mem_univ x
      rw [← hunion] at hxuniv
      rcases Finset.mem_union.mp hxuniv with h | h
      · exact absurd h hxB
      · exact h
  have hsum6 : ∑ D ∈ P.parts, D.card = 6 := by simpa using P.sum_card_parts
  rw [hPparts, Finset.sum_insert (by simp [hBC]), Finset.sum_singleton] at hsum6
  rcases hP.2 B hBmem with hB2 | hB4
  · exact ⟨B, hB2, by rw [hPparts, hCeq]⟩
  · have hC2 : C.card = 2 := by omega
    refine ⟨C, hC2, ?_⟩
    have hBeq : B = Finset.univ \ C := by
      rw [hCeq, Finset.sdiff_sdiff_eq_self (Finset.subset_univ B)]
    rw [hPparts, hBeq, Finset.pair_comm]

/-- There are fifteen partitions of type `(4,2)` on six labelled positions.

Informal proof: such a partition is uniquely determined by its two-element block; its complement
is the four-element block.  There are `choose 6 2 = 15` choices.  Source: the fifteen `(4,2)`
terms in equation `eq:C6` of `docs/Renormalization.md`.
-/
theorem card_fourTwoPartition_fin_six :
    fourTwoPartitions.card = 15 := by
  classical
  have hbij : ((Finset.univ : Finset (Fin 6)).powersetCard 2).card = fourTwoPartitions.card := by
    apply Finset.card_bij (fun B hB => pairPartition B (Finset.mem_powersetCard.mp hB).2)
    · intro B hB
      simp only [fourTwoPartitions, Finset.mem_filter, Finset.mem_univ, true_and]
      exact isFourTwoPartition_pairPartition B _
    · intro B1 hB1 B2 hB2 heq
      have h1 := (Finset.mem_powersetCard.mp hB1).2
      have h2 := (Finset.mem_powersetCard.mp hB2).2
      have hparts : ({B1, Finset.univ \ B1} : Finset (Finset (Fin 6))) =
          {B2, Finset.univ \ B2} := by
        rw [← pairPartition_parts B1 h1, ← pairPartition_parts B2 h2, heq]
      have hB1mem : B1 ∈ ({B2, Finset.univ \ B2} : Finset (Finset (Fin 6))) := by
        rw [← hparts]; simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hB1mem
      rcases hB1mem with h | h
      · exact h
      · exfalso
        have hcard4 : (Finset.univ \ B2).card = 4 := by simp [Finset.card_sdiff, h2]
        rw [← h] at hcard4
        omega
    · intro P hP
      simp only [fourTwoPartitions, Finset.mem_filter, Finset.mem_univ, true_and] at hP
      obtain ⟨B, hB2, hBparts⟩ := exists_twoBlock_of_isFourTwoPartition P hP
      refine ⟨B, ?_, ?_⟩
      · rw [Finset.mem_powersetCard]; exact ⟨Finset.subset_univ B, hB2⟩
      · apply Finpartition.ext
        rw [pairPartition_parts B hB2, hBparts]
  rw [← hbij, Finset.card_powersetCard]
  decide

end Renormalization

end

end
