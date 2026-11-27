/-
Copyright (c) 2026 LML contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML contributors
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.Card
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity

/-!
# Bounds on finite sums and products
-/

@[expose] public section

namespace Finset

/-- A finite sum of terms that are each within `B` of `L` is within `card * B` of `card * L`. -/
theorem abs_sum_sub_card_mul_le_of_abs_sub_le {ι : Type*} [Fintype ι] (W : ι → ℝ) (L B : ℝ)
    (h : ∀ i, |W i - L| ≤ B) :
    |∑ i, W i - (Fintype.card ι : ℝ) * L| ≤ (Fintype.card ι : ℝ) * B := by
  have e : ∑ i, W i - (Fintype.card ι : ℝ) * L = ∑ i, (W i - L) := by
    rw [sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul]
  rw [e]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ i, |W i - L| ≤ ∑ _i : ι, B := sum_le_sum fun i _ => h i
    _ = _ := by simp

/-- **Termwise bound on a finite sum.** If `|f i| ≤ g i` on `s` then
`|∑ i ∈ s, f i| ≤ ∑ i ∈ s, g i`. -/
theorem abs_sum_le_sum_of_abs_le {ι G : Type*} [AddCommGroup G] [LinearOrder G]
    [IsOrderedAddMonoid G] (s : Finset ι) {f g : ι → G} (h : ∀ i ∈ s, |f i| ≤ g i) :
    |∑ i ∈ s, f i| ≤ ∑ i ∈ s, g i :=
  (abs_sum_le_sum_abs _ _).trans (sum_le_sum h)

/-- A finite sum of uniformly bounded real terms is bounded by cardinality times the bound. -/
theorem abs_sum_le_card_mul_of_abs_le {ι : Type*} [Fintype ι] (f : ι → ℝ) {C : ℝ}
    (h : ∀ i, |f i| ≤ C) : |∑ i, f i| ≤ (Fintype.card ι : ℝ) * C := by
  simpa using abs_sum_sub_card_mul_le_of_abs_sub_le f 0 C (by simpa using h)

/-- **Normalized partial sums of bounded terms.** For `f` bounded by `c` on `Fin (L + 1)`, the
`(L + 1)⁻¹`-normalized sum over any subset `S` is bounded by `c`. -/
theorem abs_inv_card_mul_sum_le {L : ℕ} (S : Finset (Fin (L + 1))) {f : Fin (L + 1) → ℝ} {c : ℝ}
    (hf : ∀ i, |f i| ≤ c) : |((L + 1 : ℕ) : ℝ)⁻¹ * ∑ i ∈ S, f i| ≤ c := by
  have hc : 0 ≤ c := (abs_nonneg _).trans (hf 0)
  have hL : (0 : ℝ) < ((L + 1 : ℕ) : ℝ) := by positivity
  have hcard : (S.card : ℝ) ≤ ((L + 1 : ℕ) : ℝ) := by
    exact_mod_cast (S.card_le_univ).trans_eq (Fintype.card_fin _)
  rw [abs_mul, abs_of_pos (inv_pos.2 hL), inv_mul_le_iff₀ hL]
  calc |∑ i ∈ S, f i| ≤ ∑ _i ∈ S, c := abs_sum_le_sum_of_abs_le S fun i _ => hf i
    _ = (S.card : ℝ) * c := by rw [sum_const, nsmul_eq_mul]
    _ ≤ ((L + 1 : ℕ) : ℝ) * c := mul_le_mul_of_nonneg_right hcard hc

/-- **A replica combination of bounded terms:** if `|f j| ≤ b` for all `j` and `|g| ≤ b`, then
`|∑ⱼ f j - |ι| g| ≤ 2 |ι| b`. -/
theorem abs_sum_sub_card_mul_le_of_abs_le {ι : Type*} [Fintype ι] (f : ι → ℝ) (g b : ℝ)
    (hf : ∀ j, |f j| ≤ b) (hg : |g| ≤ b) :
    |∑ j, f j - (Fintype.card ι : ℝ) * g| ≤ 2 * (Fintype.card ι : ℝ) * b := by
  have := abs_sum_sub_card_mul_le_of_abs_sub_le f g (2 * b) fun j =>
    (abs_sub _ _).trans ((add_le_add (hf j) hg).trans_eq (two_mul b).symm)
  exact this.trans_eq (by ring)

/-- Triangle-inequality bound on the difference between a finite sum and a scaled multiple. -/
theorem abs_sum_sub_card_mul_le {ι α : Type*} [Fintype ι] {M : ℝ} (Q : α → ℝ) (hQ0 : ∀ a, 0 ≤ Q a)
    (hQM : ∀ a, Q a ≤ M) (x : ι → α) (y : α) :
    |∑ i, Q (x i) - (Fintype.card ι : ℝ) * Q y| ≤ 2 * (Fintype.card ι : ℝ) * M :=
  abs_sum_sub_card_mul_le_of_abs_le (fun i => Q (x i)) (Q y) M
    (fun _ => (abs_of_nonneg (hQ0 _)).le.trans (hQM _))
    ((abs_of_nonneg (hQ0 _)).le.trans (hQM _))

/-- A product of factors of absolute value at most `C` has absolute value at most `C ^ #s`. -/
theorem abs_prod_le_pow_card {ι R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    (s : Finset ι) {f : ι → R} {C : R} (hf : ∀ i ∈ s, |f i| ≤ C) :
    |∏ i ∈ s, f i| ≤ C ^ s.card := by
  rw [abs_prod, ← prod_const]
  exact prod_le_prod₀ (fun _ _ => abs_nonneg _) hf

end Finset
