/-
Copyright (c) 2026 LML contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML contributors
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.Card
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity

/-!
# Bounds on finite sums and products
-/

@[expose] public section

namespace Finset

variable {ι R : Type*}

/-- A finite sum of terms that are each within `B` of `L` is within `card * B` of `card * L`. -/
theorem abs_sum_sub_card_mul_le_of_abs_sub_le [Fintype ι] [Ring R] [LinearOrder R]
    [IsOrderedRing R] (W : ι → R) (L B : R) (h : ∀ i, |W i - L| ≤ B) :
    |∑ i, W i - (Fintype.card ι : R) * L| ≤ (Fintype.card ι : R) * B := by
  have e : ∑ i, W i - (Fintype.card ι : R) * L = ∑ i, (W i - L) := by
    rw [sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul]
  rw [e]
  refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum fun i _ => h i).trans_eq ?_)
  rw [sum_const, card_univ, nsmul_eq_mul]

/-- **Termwise bound on a finite sum.** If `|f i| ≤ g i` on `s` then
`|∑ i ∈ s, f i| ≤ ∑ i ∈ s, g i`. -/
theorem abs_sum_le_sum_of_abs_le {G : Type*} [AddCommGroup G] [LinearOrder G]
    [IsOrderedAddMonoid G] (s : Finset ι) {f g : ι → G} (h : ∀ i ∈ s, |f i| ≤ g i) :
    |∑ i ∈ s, f i| ≤ ∑ i ∈ s, g i :=
  (abs_sum_le_sum_abs _ _).trans (sum_le_sum h)

/-- A finite sum of uniformly bounded terms is bounded by cardinality times the bound. -/
theorem abs_sum_le_card_mul_of_abs_le [Fintype ι] [Ring R] [LinearOrder R] [IsOrderedRing R]
    (f : ι → R) {C : R} (h : ∀ i, |f i| ≤ C) : |∑ i, f i| ≤ (Fintype.card ι : R) * C := by
  simpa using abs_sum_sub_card_mul_le_of_abs_sub_le f 0 C (by simpa using h)

/-- **Normalized partial sums of bounded terms.** If `#S ≤ n` and the terms on `S` are bounded
by `c ≥ 0`, the `n⁻¹`-normalized sum over `S` is bounded by `c`. -/
theorem abs_inv_natCast_mul_sum_le {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {S : Finset ι} {n : ℕ} (hS : S.card ≤ n) {f : ι → K} {c : K} (hc : 0 ≤ c)
    (hf : ∀ i ∈ S, |f i| ≤ c) : |(n : K)⁻¹ * ∑ i ∈ S, f i| ≤ c := by
  rw [abs_mul, abs_inv, Nat.abs_cast]
  refine inv_mul_le_of_le_mul₀ (Nat.cast_nonneg n) hc ?_
  calc |∑ i ∈ S, f i| ≤ ∑ _i ∈ S, c := abs_sum_le_sum_of_abs_le S hf
    _ = (S.card : K) * c := by rw [sum_const, nsmul_eq_mul]
    _ ≤ (n : K) * c := mul_le_mul_of_nonneg_right (Nat.cast_le.2 hS) hc

/-- **A replica combination of bounded terms:** if `|f j| ≤ b` for all `j` and `|g| ≤ b`, then
`|∑ⱼ f j - |ι| g| ≤ 2 |ι| b`. -/
theorem abs_sum_sub_card_mul_le_of_abs_le [Fintype ι] [Ring R] [LinearOrder R] [IsOrderedRing R]
    (f : ι → R) (g b : R) (hf : ∀ j, |f j| ≤ b) (hg : |g| ≤ b) :
    |∑ j, f j - (Fintype.card ι : R) * g| ≤ 2 * (Fintype.card ι : R) * b := by
  have := abs_sum_sub_card_mul_le_of_abs_sub_le f g (2 * b) fun j =>
    (abs_sub _ _).trans ((add_le_add (hf j) hg).trans_eq (two_mul b).symm)
  exact this.trans_eq (by rw [← mul_assoc, Nat.cast_comm (Fintype.card ι) (2 : R)])

/-- A product of factors of absolute value at most `C` has absolute value at most `C ^ #s`. -/
theorem abs_prod_le_pow_card [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    (s : Finset ι) {f : ι → R} {C : R} (hf : ∀ i ∈ s, |f i| ≤ C) :
    |∏ i ∈ s, f i| ≤ C ^ s.card := by
  rw [abs_prod, ← prod_const]
  exact prod_le_prod₀ (fun _ _ => abs_nonneg _) hf

end Finset
