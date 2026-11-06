/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.Renormalization.PairingBlocks
public import LeanMachineLearning.Optimization.Renormalization.PairingWick

/-!
# Restricting a pairing to a subset of its blocks

A subset `S` of the blocks of a pairing `P` of a finite type `α` covers `2 |S|` elements. This
module relabels those elements by `Fin (2 |S|)`, so that statements proved for pairings of
`Fin (2 m)` apply to `S`: there is an injective relabelling `w : Fin (2 |S|) → α` onto the
elements covered by `S` and a pairing `Q` of `Fin (2 |S|)` such that, for every symmetric kernel
`C`, the block product of `Q` for the pulled-back kernel is the product of the block weights
over `S`.
-/

@[expose] public section

open Finset
open scoped BigOperators
namespace Renormalization

variable {α : Type*} [DecidableEq α] [Fintype α]

/-- **Relabelling a subset of the blocks of a pairing.** See the module docstring. -/
theorem exists_relabel_pairing_subset (P : Finpartition.Pairing (univ : Finset α))
    (S : Finset (Finset α)) (hS : S ⊆ P.val.parts) :
    ∃ (w : Fin (2 * S.card) → α) (Q : Finpartition.Pairing (univ : Finset (Fin (2 * S.card)))),
      Function.Injective w ∧ (∀ a, a ∈ Set.range w ↔ ∃ B ∈ S, a ∈ B) ∧
      ∀ C : α → α → ℝ, (∀ i j, C i j = C j i) →
        Q.blockProduct (pairWeight fun a b => C (w a) (w b)) = ∏ B ∈ S, pairWeight C B := by
  classical
  have hcard : ∀ B ∈ S, B.card = 2 := fun B hB => P.2 B (hS hB)
  let F : Fin S.card ≃ S := (S.equivFin).symm
  choose u v huv hb using fun i : Fin S.card =>
    Finset.card_eq_two.1 (hcard (F i).1 (F i).2)
  let e : Fin (2 * S.card) ≃ Fin S.card × Bool :=
    Fintype.equivOfCardEq (by simp [mul_comm])
  let w : Fin (2 * S.card) → α := fun k => if (e k).2 then u (e k).1 else v (e k).1
  have hw (i : Fin S.card) (b : Bool) : w (e.symm (i, b)) = if b then u i else v i := by
    simp [w]
  have hwB (k : Fin (2 * S.card)) : w k ∈ (F (e k).1).1 := by
    rw [hb]
    by_cases h : (e k).2 <;> simp [w, h]
  obtain ⟨Pe, hPe, -⟩ := Finpartition.existsUnique_pairing_ordering_of_equiv (ι := Fin S.card) e
  refine ⟨w, Pe.1, ?_, ?_, ?_⟩
  · intro k k' hkk
    by_cases hi : (e k).1 = (e k').1
    · have hb2 : (e k).2 = (e k').2 := by
        have hk : w k = w k' := hkk
        simp only [w, ← hi] at hk
        cases h1 : (e k).2 <;> cases h2 : (e k').2 <;> simp only [h1, h2] at hk ⊢
        · exact (huv _ hk.symm).elim
        · exact (huv _ hk).elim
      exact e.injective (Prod.ext hi hb2)
    · exfalso
      have hne : (F (e k).1).1 ≠ (F (e k').1).1 := fun h =>
        hi (F.injective (Subtype.ext h))
      have hd := P.val.disjoint (hS (F (e k).1).2) (hS (F (e k').1).2) hne
      rw [Function.onFun, id, id, Finset.disjoint_left] at hd
      exact hd (hwB k) (hkk ▸ hwB k')
  · intro a
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨(F (e k).1).1, (F (e k).1).2, hwB k⟩
    · rintro ⟨B, hB, ha⟩
      let i : Fin S.card := F.symm ⟨B, hB⟩
      have hBi : B = (F i).1 := by simp [i]
      rw [hBi, hb] at ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl
      · exact ⟨e.symm (i, true), by rw [hw]; simp⟩
      · exact ⟨e.symm (i, false), by rw [hw]; simp⟩
  · intro C hC
    rw [← Pe.1.prod_equiv_eq_blockProduct Pe.2]
    calc _ = ∏ i : Fin S.card, pairWeight C (F i).1 := by
          refine Finset.prod_congr rfl fun i _ => ?_
          have hset : (Pe.2 i).val = {e.symm (i, true), e.symm (i, false)} := by
            ext k
            rw [hPe i k]
            constructor
            · intro h
              have : e k = (i, (e k).2) := Prod.ext h rfl
              cases hk : (e k).2
              · have : k = e.symm (i, false) := by
                  rw [← hk, ← h]; simp
                simp [this]
              · have : k = e.symm (i, true) := by
                  rw [← hk, ← h]; simp
                simp [this]
            · intro h
              simp only [Finset.mem_insert, Finset.mem_singleton] at h
              rcases h with rfl | rfl <;> simp
          have hne : e.symm (i, true) ≠ e.symm (i, false) := fun h => by
            simpa using e.symm.injective h
          rw [hset, pairWeight_pair _ (fun a b => hC _ _) hne, hw, hw, hb,
            pairWeight_pair C hC (huv i)]
          simp
      _ = ∏ B ∈ S, pairWeight C B := by
          rw [← Finset.prod_coe_sort S]
          exact Fintype.prod_equiv F _ _ (fun i => rfl)

end Renormalization
