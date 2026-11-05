/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Data.Sym.Sym2
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Tactic.Ring

/-!
# Signed sums of cross choices

The four signed choices between two disjoint pairs give a rectangular kernel difference.
Sorting the chosen endpoints has no effect for symmetric kernels.
-/

@[expose] public section

open scoped BigOperators
namespace Finset

/-- The signed sum over the four sorted cross choices is a rectangle of a symmetric kernel.
This identity holds over any commutative ring and any finite linearly ordered index type. -/
theorem sum_signed_orderedPairs_product {α R : Type*} [Fintype α] [LinearOrder α]
    [CommRing R] (x₀ x₁ y₀ y₁ : α) (hx : x₀ ≠ x₁) (hy : y₀ ≠ y₁)
    (hd : Disjoint ({x₀, x₁} : Finset α) {y₀, y₁})
    (K : α → α → R) (hK : ∀ a b, K a b = K b a) :
    (∑ p ∈ (univ : Finset {p : α × α // p.1 < p.2}).filter (fun p =>
        p.val ∈ (({x₀, x₁} : Finset α).product {y₀, y₁}).image
          (fun ab => (min ab.1 ab.2, max ab.1 ab.2))),
      (if x₀ ∈ ({p.val.1, p.val.2} : Finset α) then (1 : R) else -1) *
      (if y₀ ∈ ({p.val.1, p.val.2} : Finset α) then (1 : R) else -1) *
      K p.val.1 p.val.2) = K x₀ y₀ - K x₁ y₀ - K x₀ y₁ + K x₁ y₁ := by
  rw [sum_orderedPairs_sorted_product _ _ hd (fun ab : α × α =>
    (if x₀ ∈ ({ab.1, ab.2} : Finset α) then (1 : R) else -1) *
      (if y₀ ∈ ({ab.1, ab.2} : Finset α) then (1 : R) else -1) * K ab.1 ab.2)]
  have hs (a b : α) :
      (if x₀ ∈ ({min a b, max a b} : Finset α) then (1 : R) else -1) *
        (if y₀ ∈ ({min a b, max a b} : Finset α) then (1 : R) else -1) *
        K (min a b) (max a b) =
      (if x₀ ∈ ({a, b} : Finset α) then (1 : R) else -1) *
        (if y₀ ∈ ({a, b} : Finset α) then (1 : R) else -1) * K a b := by
    rcases le_total a b with hab | hba
    · rw [min_eq_left hab, max_eq_right hab]
    · rw [min_eq_right hba, max_eq_left hba, pair_comm b a, hK b a]
  simp_rw [hs]
  have hd' : (x₀ ≠ y₀ ∧ x₀ ≠ y₁) ∧ x₁ ≠ y₀ ∧ x₁ ≠ y₁ := by
    simpa only [disjoint_insert_left, disjoint_singleton_left,
      mem_insert, mem_singleton, not_or] using hd
  trace_state
  simp only [sum_product, sum_pair hx, sum_pair hy]
  simp only [mem_insert, mem_singleton, hx, hy, hd'.1.1, hd'.1.2,
    hd'.2.1, hd'.2.2, Ne.symm hd'.1.1, Ne.symm hd'.2.1, or_self,
    eq_self, true_or, or_true, false_or, or_false, ite_true, ite_false,
    one_mul, neg_one_mul, neg_mul, neg_neg]
  ring

end Finset
