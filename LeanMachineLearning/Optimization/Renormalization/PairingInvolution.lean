/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.Renormalization.Finpartition

/-!
# Pair partitions and fixed-point-free involutions

The partner involution and the partition into two-element blocks are equivalent
representations. This bridge lets involution-based applications reuse the weighted
pairing recursion without duplicating the combinatorics.
-/

@[expose] public section

open Finset
namespace Finpartition

variable {α : Type*} [DecidableEq α]

/-- Following the partner map twice returns the original element, for a pairing of any
finite set. -/
@[simp] theorem Pairing.partner_partner {s : Finset α} (P : Pairing s) {a : α} (ha : a ∈ s) :
    (P.partner (mem_of_mem_erase (P.partner ha).property)).val = a := by
  let b := P.partner ha
  have hb : b.val ∈ s := mem_of_mem_erase b.property
  have hne : a ≠ b.val := (mem_erase.mp b.property).1.symm
  have hab : P.val.part a = {a, b.val} := (P.partnerData ha).property.2
  have hba : P.val.part b.val = {b.val, a} := by
    rw [P.val.part_eq_of_mem (P.val.part_mem.mpr ha) (by rw [hab]; simp)]
    exact hab.trans (pair_comm _ _)
  have hd := P.partnerData_eq hb ha hne hba
  change (P.partnerData hb).val = a
  rw [hd]

/-- Construct the partition into the two-element orbits of a fixed-point-free involution.
The construction requires no ordering on the finite type. -/
noncomputable def Pairing.ofInvolution [Fintype α] (f : α → α)
    (hf : Function.Involutive f) (hne : ∀ a, f a ≠ a) : Pairing (univ : Finset α) := by
  let blocks : Finset (Finset α) := univ.image fun a => {a, f a}
  have hblock (a b : α) (ha : a ∈ ({b, f b} : Finset α)) :
      ({b, f b} : Finset α) = {a, f a} := by
    simp only [mem_insert, mem_singleton] at ha
    rcases ha with rfl | rfl
    · rfl
    · rw [hf b, pair_comm]
  refine ⟨Finpartition.ofExistsUnique blocks (fun _ _ => subset_univ _) ?_ ?_, ?_⟩
  · intro a _
    refine ⟨{a, f a}, ⟨mem_image.mpr ⟨a, mem_univ _, rfl⟩, by simp⟩, ?_⟩
    intro B hB
    obtain ⟨b, _, rfl⟩ := mem_image.mp hB.1
    exact hblock a b hB.2
  · intro h
    obtain ⟨a, _, ha⟩ := mem_image.mp h
    have hm : a ∈ ({a, f a} : Finset α) := by simp
    rw [ha] at hm
    exact notMem_empty a hm
  · intro B hB
    obtain ⟨a, _, rfl⟩ := mem_image.mp hB
    exact card_pair (hne a).symm

/-- The block containing `a` in the orbit partition is `{a,f a}`. -/
@[simp] theorem Pairing.part_ofInvolution [Fintype α] (f : α → α)
    (hf : Function.Involutive f) (hne : ∀ a, f a ≠ a) (a : α) :
    (Pairing.ofInvolution f hf hne).val.part a = {a, f a} := by
  apply Finpartition.part_eq_of_mem
  · exact mem_image.mpr ⟨a, mem_univ _, rfl⟩
  · simp

/-- The partner in the orbit partition is the original involution. -/
@[simp] theorem Pairing.partner_ofInvolution [Fintype α] (f : α → α)
    (hf : Function.Involutive f) (hne : ∀ a, f a ≠ a) (a : α) :
    ((Pairing.ofInvolution f hf hne).partner (mem_univ a)).val = f a := by
  have hd := (Pairing.ofInvolution f hf hne).partnerData_eq (mem_univ a)
    (mem_univ (f a)) (hne a) (Pairing.part_ofInvolution f hf hne a)
  change ((Pairing.ofInvolution f hf hne).partnerData (mem_univ a)).val = f a
  rw [hd]

/-- Pair partitions of a finite type are equivalent to its fixed-point-free involutions. -/
noncomputable def Pairing.equivInvolution [Fintype α] :
    Pairing (univ : Finset α) ≃
      {f : α → α // Function.Involutive f ∧ ∀ a, f a ≠ a} where
  toFun P := ⟨fun a => (P.partner (mem_univ a)).val,
    (fun a => P.partner_partner (mem_univ a)),
    (fun a => (mem_erase.mp (P.partner (mem_univ a)).property).1)⟩
  invFun f := Pairing.ofInvolution f.val f.property.1 f.property.2
  left_inv P := by
    apply Subtype.ext
    apply Finpartition.ext
    ext B
    constructor
    · intro hB
      obtain ⟨a, _, rfl⟩ := mem_image.mp hB
      rw [← (P.partnerData (mem_univ a)).property.2]
      exact P.val.part_mem.mpr (mem_univ a)
    · intro hB
      obtain ⟨a, ha⟩ := P.val.nonempty_of_mem_parts hB
      have he := P.val.part_eq_of_mem hB ha
      rw [(P.partnerData (mem_univ a)).property.2] at he
      exact mem_image.mpr ⟨a, mem_univ _, he⟩
  right_inv f := by
    apply Subtype.ext
    funext a
    exact Pairing.partner_ofInvolution f.val f.property.1 f.property.2 a

/-- The block product of an orbit pairing can be computed by choosing the lesser endpoint
of every pair. This works for arbitrary commutative-monoid block weights. -/
theorem Pairing.blockProduct_ofInvolution {R : Type*} [CommMonoid R]
    [Fintype α] [LinearOrder α] (f : α → α)
    (hf : Function.Involutive f) (hne : ∀ a, f a ≠ a) (w : Finset α → R) :
    (Pairing.ofInvolution f hf hne).blockProduct w =
      ∏ a ∈ univ.filter (fun a => a < f a), w {a, f a} := by
  symm
  unfold Pairing.blockProduct Finpartition.blockProduct
  apply prod_bij (fun a _ => ({a, f a} : Finset α))
  · intro a _
    exact mem_image.mpr ⟨a, mem_univ _, rfl⟩
  · intro a ha b hb he
    have hma : a ∈ ({b, f b} : Finset α) := he ▸ (by simp)
    simp only [mem_insert, mem_singleton] at hma
    rcases hma with rfl | rfl
    · rfl
    · have hfa := (mem_filter.mp ha).2
      rw [hf b] at hfa
      exact False.elim (lt_asymm hfa (mem_filter.mp hb).2)
  · intro B hB
    obtain ⟨a, _, rfl⟩ := mem_image.mp hB
    by_cases ha : a < f a
    · exact ⟨a, mem_filter.mpr ⟨mem_univ _, ha⟩, rfl⟩
    · refine ⟨f a, mem_filter.mpr ⟨mem_univ _, ?_⟩, ?_⟩
      · rw [hf a]
        exact lt_of_le_of_ne (le_of_not_gt ha) (hne a)
      · rw [hf a, pair_comm]
  · intro _ _
    rfl

end Finpartition
