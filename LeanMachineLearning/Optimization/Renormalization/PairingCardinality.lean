/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.Renormalization.Finpartition
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity

/-!
# Counting pair partitions of finite sets

The weighted pairing recursion gives the count for any finite set of even cardinality.
No order, probability, or choice of enumeration is needed.
-/

@[expose] public section

open Finset
namespace Finpartition

variable {α : Type*} [DecidableEq α]

/-- The empty set has one pair partition. -/
@[simp] theorem Pairing.card_empty : Fintype.card (Pairing (∅ : Finset α)) = 1 := by
  have : Unique (Finpartition (∅ : Finset α)) := by
    change Unique (Finpartition (⊥ : Finset α))
    infer_instance
  refine Fintype.card_eq_one_iff.mpr ⟨⟨default, ?_⟩, ?_⟩
  · intro B hB
    have he : (default : Finpartition (∅ : Finset α)) = ⊥ := Subsingleton.elim _ _
    rw [he] at hB
    simp at hB
  · intro y
    apply Subtype.ext
    exact Subsingleton.elim _ _

/-- The empty pairing product is one, for weights in any commutative semiring. -/
@[simp] theorem pairingSum_empty {R : Type*} [CommSemiring R] (w : Finset α → R) :
    pairingSum w (∅ : Finset α) = 1 := by
  have hp (P : Pairing (∅ : Finset α)) : P.val.parts = ∅ :=
    P.val.parts_eq_empty_iff.mpr rfl
  simp only [pairingSum, Pairing.blockProduct, blockProduct, hp, prod_empty,
    sum_const, card_univ, Pairing.card_empty, one_nsmul]

/-- Count pairings by choosing the partner of a distinguished element.
This is the constant-weight instance of the existing weighted pairing recursion. -/
theorem Pairing.card_erase (s : Finset α) {a : α} (ha : a ∈ s) :
    Fintype.card (Pairing s) =
      ∑ b ∈ s.erase a, Fintype.card (Pairing ((s.erase a).erase b)) := by
  simpa [pairingSum, Pairing.blockProduct, Finpartition.blockProduct] using
    (pairingSum_erase (R := ℕ) (fun _ => 1) s ha)

/-- Counting ordered lists and orientations of the blocks of a pairing gives `(2m)!`.
Equivalently, an even set has `(2m)!/(2^m m!)` pair partitions. -/
theorem Pairing.card_mul_two_pow_mul_factorial (m : ℕ) (s : Finset α) (hs : s.card = 2 * m) :
    Fintype.card (Pairing s) * (2 ^ m * m.factorial) = (2 * m).factorial := by
  induction m generalizing s with
  | zero =>
    have he : s = ∅ := card_eq_zero.mp (by omega)
    simp [he]
  | succ m ih =>
    obtain ⟨a, ha⟩ := card_pos.mp (show 0 < s.card by omega)
    have hres (b : α) (hb : b ∈ s.erase a) :
        ((s.erase a).erase b).card = 2 * m := by
      rw [card_erase_of_mem hb, card_erase_of_mem ha]
      omega
    rw [Pairing.card_erase s ha, pow_succ, Nat.factorial_succ]
    calc
      _ = (2 * (m + 1)) *
          ∑ b ∈ s.erase a, Fintype.card (Pairing ((s.erase a).erase b)) *
            (2 ^ m * m.factorial) := by rw [← sum_mul]; ring
      _ = (2 * (m + 1)) * ∑ b ∈ s.erase a, (2 * m).factorial := by
        congr 1
        exact sum_congr rfl fun b hb => ih _ (hres b hb)
      _ = (2 * (m + 1)) * ((2 * m + 1) * (2 * m).factorial) := by
        simp only [sum_const, smul_eq_mul, card_erase_of_mem ha]
        congr 2
        omega
      _ = (2 * (m + 1)).factorial := by
        rw [show 2 * (m + 1) = (2 * m + 1) + 1 by omega,
          Nat.factorial_succ, Nat.factorial_succ]

/-- The number of pair partitions of any set with `2m` elements. -/
theorem Pairing.card_eq_factorial_div (m : ℕ) (s : Finset α) (hs : s.card = 2 * m) :
    Fintype.card (Pairing s) = (2 * m).factorial / (2 ^ m * m.factorial) := by
  rw [← Pairing.card_mul_two_pow_mul_factorial m s hs]
  exact (Nat.mul_div_cancel _ (by positivity)).symm

/-- A pairing of a set with `2 * m` elements has `m` blocks. -/
theorem Pairing.card_parts_of_card_eq {α : Type*} [DecidableEq α] {s : Finset α} {m : ℕ}
    (P : Pairing s) (hs : s.card = 2 * m) : P.val.parts.card = m := by
  have hp := P.two_mul_card_parts
  omega

/-- Indexing the blocks of a pairing by any equivalence does not change the product of a
block weight. -/
theorem Pairing.prod_equiv_eq_blockProduct {α R ι : Type*} [DecidableEq α] [CommMonoid R]
    [Fintype ι] {s : Finset α} (P : Pairing s) (e : ι ≃ P.val.parts) (w : Finset α → R) :
    (∏ i : ι, w (e i).val) = P.blockProduct w := by
  calc
    _ = ∏ B : P.val.parts, w B.val := e.prod_comp (fun B : P.val.parts => w B.val)
    _ = _ := Finset.prod_coe_sort P.val.parts w

end Finpartition
