/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.SKOverlapCLTGlobalCounting
public import LeanMachineLearning.SpinGlasses.SKOverlapCLTGlobalTermI

/-!
# Bookkeeping of the block structure for the global recurrence

The `k` blocks `{e (inl u), e (inr u)}` exhaust the `n = 2k` replicas. The leading block is
`p`; the remaining blocks are indexed by `{u // u ≠ p}`. A replica lies in a remaining block iff
it is not a member of the leading block, and the partner of a replica outside the leading block is
obtained by swapping the two sides of the block. These elementary facts connect the classification
of `SKOverlapCLTGlobalClassify.lean` to the counting of `SKOverlapCLTGlobalCounting.lean`.
-/

@[expose] public section

open Finset
open scoped BigOperators

namespace SpinGlasses

variable {V R : Type*} (e : V ⊕ V ≃ R) (p : V)

/-- A replica lies in a remaining block iff it is not in the leading block. -/
theorem exists_block_iff (r : R) :
    (∃ u : {u // u ≠ p}, r = e (.inl u.1) ∨ r = e (.inr u.1)) ↔
      ¬(r = e (.inl p) ∨ r = e (.inr p)) := by
  constructor
  · rintro ⟨u, h | h⟩ <;> rintro (h' | h')
    · exact u.2 (Sum.inl_injective (e.injective (h.symm.trans h')))
    · exact absurd (e.injective (h.symm.trans h')) (by simp)
    · exact absurd (e.injective (h.symm.trans h')) (by simp)
    · exact u.2 (Sum.inr_injective (e.injective (h.symm.trans h')))
  · intro h
    obtain ⟨s, rfl⟩ := e.surjective r
    rcases s with u | u
    · exact ⟨⟨u, fun hu => h (Or.inl (by rw [hu]))⟩, Or.inl rfl⟩
    · exact ⟨⟨u, fun hu => h (Or.inr (by rw [hu]))⟩, Or.inr rfl⟩

/-- The partner of a replica in its block. -/
def blockPartner (r : R) : R := e (Sum.swap (e.symm r))

/-- Swapping the two copies of an arbitrary index type twice is the identity. -/
theorem blockPartner_involutive : Function.Involutive (blockPartner e) := by
  intro r
  simp [blockPartner]

/-- The two disjoint copies ensure that the partner map has no fixed points. -/
theorem blockPartner_ne_self (r : R) : blockPartner e r ≠ r := by
  intro h
  have hs : Sum.swap (e.symm r) = e.symm r := by
    simpa only [Equiv.symm_apply_apply] using congrArg e.symm h
  have hswap : ∀ s : V ⊕ V, Sum.swap s ≠ s := by
    intro s
    cases s <;> simp
  exact hswap _ hs

/-- The partner map is an involution without fixed points on the remaining blocks. -/
theorem blockPartner_spec (r : R) (h1 : r ≠ e (.inl p)) (h2 : r ≠ e (.inr p)) :
    blockPartner e r ≠ r ∧ blockPartner e r ≠ e (.inl p) ∧ blockPartner e r ≠ e (.inr p) ∧
      blockPartner e (blockPartner e r) = r := by
  obtain ⟨s, rfl⟩ := e.surjective r
  have hs1 : s ≠ .inl p := fun h => h1 (by rw [h])
  have hs2 : s ≠ .inr p := fun h => h2 (by rw [h])
  refine ⟨blockPartner_ne_self e _, ?_, ?_, blockPartner_involutive e _⟩
  all_goals simp only [blockPartner, Equiv.symm_apply_apply]
  · intro h
    have := e.injective h
    rcases s with u | u
    · simp only [Sum.swap_inl, reduceCtorEq] at this
    · simp only [Sum.swap_inr, Sum.inl.injEq] at this
      exact hs2 (by rw [this])
  · intro h
    have := e.injective h
    rcases s with u | u
    · simp only [Sum.swap_inl, Sum.inr.injEq] at this
      exact hs1 (by rw [this])
    · simp only [Sum.swap_inr, reduceCtorEq] at this

/-- Two replicas form a remaining block iff the first is outside the leading block and the second
is its partner. -/
theorem exists_block_pair_iff (r s : R) :
    (∃ u : {u // u ≠ p}, (r = e (.inl u.1) ∧ s = e (.inr u.1)) ∨
        (r = e (.inr u.1) ∧ s = e (.inl u.1))) ↔
      (r ≠ e (.inl p) ∧ r ≠ e (.inr p) ∧ s = blockPartner e r) := by
  constructor
  · rintro ⟨u, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
    · refine ⟨fun h => u.2 (Sum.inl_injective (e.injective (h1.symm.trans h))),
        fun h => absurd (e.injective (h1.symm.trans h)) (by simp), ?_⟩
      simp [blockPartner, h1, h2]
    · refine ⟨fun h => absurd (e.injective (h1.symm.trans h)) (by simp),
        fun h => u.2 (Sum.inr_injective (e.injective (h1.symm.trans h))), ?_⟩
      simp [blockPartner, h1, h2]
  · rintro ⟨h1, h2, h3⟩
    obtain ⟨t, rfl⟩ := e.surjective r
    rcases t with u | u
    · refine ⟨⟨u, fun hu => h1 (by rw [hu])⟩, Or.inl ⟨rfl, ?_⟩⟩
      simpa [blockPartner] using h3
    · refine ⟨⟨u, fun hu => h2 (by rw [hu])⟩, Or.inr ⟨rfl, ?_⟩⟩
      simpa [blockPartner] using h3

end SpinGlasses
