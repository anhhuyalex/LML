/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Tactic.Ring

/-!
# Separating the constant, linear and higher terms of a finite product

This is the exact algebra behind last-site product expansions. The remainder is the
explicit sum over subsets containing at least two corrections, not an existential error.
-/

@[expose] public section

open scoped BigOperators

namespace Finset

/-- Expand a product, retaining the terms containing zero or one correction and summing
explicitly over all terms with at least two corrections. Valid over any commutative semiring. -/
theorem prod_add_eq_prod_add_single_add_rest {ι K : Type*} [DecidableEq ι] [CommSemiring K]
    (s : Finset ι) (u v : ι → K) :
    (∏ i ∈ s, (u i + v i)) = (∏ i ∈ s, u i) +
      (∑ i ∈ s, v i * ∏ j ∈ s.erase i, u j) +
      ∑ t ∈ s.powerset with 2 ≤ t.card, (∏ i ∈ t, v i) * ∏ j ∈ s \ t, u j := by
  let Q : Finset ι → K := fun t => (∏ i ∈ t, v i) * ∏ j ∈ s \ t, u j
  have hzero : (s.powerset.filter fun t => t.card = 0) = {∅} := by
    rw [← powersetCard_eq_filter, powersetCard_zero]
  have hone : (s.powerset.filter fun t => t.card = 1) = s.image singleton := by
    rw [← powersetCard_eq_filter, powersetCard_one, map_eq_image]
    rfl
  have hpart : (∑ t ∈ s.powerset, Q t) =
      (∑ t ∈ s.powerset with t.card = 0, Q t) +
      (∑ t ∈ s.powerset with t.card = 1, Q t) +
      ∑ t ∈ s.powerset with 2 ≤ t.card, Q t := by
    simp only [sum_filter]
    rw [← sum_add_distrib, ← sum_add_distrib]
    apply sum_congr rfl
    intro t ht
    by_cases h0 : t.card = 0
    · simp [h0]
    by_cases h1 : t.card = 1
    · simp [h1]
    have h2 : 2 ≤ t.card := by omega
    simp [h0, h1, h2]
  rw [show (∏ i ∈ s, (u i + v i)) = ∑ t ∈ s.powerset, Q t by
    simpa only [add_comm] using prod_add v u s, hpart, hzero, hone]
  simp only [sum_singleton, Q, prod_empty, sdiff_empty, one_mul]
  congr 1
  rw [sum_image (fun i _ j _ hij => singleton_injective hij)]
  simp only [prod_singleton, sdiff_singleton_eq_erase]

/-- A product perturbation is the sum over nonempty sets of corrected factors. -/
theorem prod_add_sub_prod_eq_sum_nonempty {ι K : Type*} [DecidableEq ι] [CommRing K]
    (s : Finset ι) (u v : ι → K) :
    (∏ i ∈ s, (u i + v i)) - (∏ i ∈ s, u i) =
      ∑ t ∈ s.powerset with 1 ≤ t.card, (∏ i ∈ t, v i) * ∏ j ∈ s \ t, u j := by
  let Q : Finset ι → K := fun t => (∏ i ∈ t, v i) * ∏ j ∈ s \ t, u j
  have hz : s.powerset.filter (fun t => ¬1 ≤ t.card) = {∅} := by
    simpa only [Nat.not_le, Nat.lt_one_iff] using
      (powersetCard_eq_filter (s := s) (n := 0)).symm.trans (powersetCard_zero s)
  have hp := sum_filter_add_sum_filter_not s.powerset (fun t => 1 ≤ t.card) Q
  rw [hz, sum_singleton] at hp
  have he : (∏ i ∈ s, (u i + v i)) = ∑ t ∈ s.powerset, Q t := by
    simpa only [add_comm] using prod_add v u s
  rw [he]
  simpa [Q] using (eq_sub_iff_add_eq.mpr hp).symm

/-- Removing either of two equal factors gives the same product, even if the factors
vanish. No cancellation or division is needed. -/
theorem prod_erase_eq_of_eq {J M : Type*} [DecidableEq J] [CommMonoid M]
    (s : Finset J) (f : J → M) {u v : J} (hu : u ∈ s) (hv : v ∈ s)
    (he : f u = f v) : (∏ j ∈ s.erase u, f j) = ∏ j ∈ s.erase v, f j := by
  by_cases huv : u = v
  · subst v; rfl
  have hvu : v ≠ u := fun h => huv h.symm
  have hv' : v ∈ s.erase u := by simp [hvu, hv]
  have hu' : u ∈ s.erase v := by simp [huv, hu]
  rw [← Finset.mul_prod_erase _ f hv', ← Finset.mul_prod_erase _ f hu',
    Finset.erase_right_comm, he]

/-- Expand a flagged fresh-overlap factor into centered pair terms. The four flag
choices include pair, single and global factors. Valid over every commutative ring. -/
theorem sum_centered_pairs_eq_fresh_overlap {R J I X K : Type*} [Fintype I] [CommRing K]
    (v : X → I → K) (σ : R ⊕ (J ⊕ J) → X) (a b : R) (j : J)
    (L S : Bool) (t q : K) :
    let A : Bool × Bool → R ⊕ (J ⊕ J) := fun i =>
      if L && i.1 then .inl a else .inr (.inl j)
    let B : Bool × Bool → R ⊕ (J ⊕ J) := fun i =>
      if S && i.2 then .inl b else .inr (.inr j)
    let c : Bool × Bool → K := fun i =>
      (if L then if i.1 then 1 else -1 else if i.1 then 1 else 0) *
      (if S then if i.2 then 1 else -1 else if i.2 then 1 else 0)
    (∑ i : Bool × Bool, c i * (t * ∑ k, v (σ (A i)) k * v (σ (B i)) k - q)) =
      (t * ∑ k, (if L then v (σ (.inl a)) k - v (σ (.inr (.inl j))) k
        else v (σ (.inr (.inl j))) k) *
        (if S then v (σ (.inl b)) k - v (σ (.inr (.inr j))) k
        else v (σ (.inr (.inr j))) k)) - (if L || S then 0 else q) := by
  intro A B c
  cases L <;> cases S <;>
    simp [Fintype.sum_prod_type, A, B, c, sub_mul, mul_sub,
      Finset.sum_sub_distrib] <;> ring

end Finset
