/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Exponential penalties on a finite set

For a finite set `A` and a cost `c : A → ℝ` with `0 ≤ c a`, the penalized sum
`∑ a, exp (-β * c a)` tends, as `β → ∞`, to the number of states of cost zero.  The proof
handles each summand separately (cost zero or positive), so no Gibbs-measure or
thermodynamic-limit machinery is needed.  For natural-number costs there is an explicit error
bound.

## Main declarations

* `tendsto_sum_exp_neg_mul_atTop_card_filter_eq_zero`: the limit.
* `sum_exp_neg_mul_sub_card_filter_le`: for costs in `ℕ` and `β ≥ 0`,
  `0 ≤ ∑ a, exp (-β c a) - #{c = 0} ≤ (|A| - #{c = 0}) exp (-β)`.
-/

@[expose] public section

open Filter Finset
open scoped Topology

/-- **Finite exponential penalties select the zero-cost states.**  For a finite type and a
nonnegative cost, `∑ a, exp (-β * c a) → #{a | c a = 0}` as `β → ∞`. -/
theorem tendsto_sum_exp_neg_mul_atTop_card_filter_eq_zero {A : Type*} [Fintype A] (c : A → ℝ)
    (hc : ∀ a, 0 ≤ c a) :
    Tendsto (fun β : ℝ => ∑ a, Real.exp (-β * c a)) atTop
      (𝓝 ((univ.filter fun a => c a = 0).card : ℝ)) := by
  classical
  have h : ∀ a, Tendsto (fun β : ℝ => Real.exp (-β * c a)) atTop
      (𝓝 (if c a = 0 then 1 else 0)) := fun a => by
    by_cases h0 : c a = 0
    · simp [h0]
    · have hpos : 0 < c a := lt_of_le_of_ne (hc a) (Ne.symm h0)
      simp only [h0, ite_false]
      exact (Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_id.atTop_mul_const hpos)).congr fun β => by simp [neg_mul]
  have hsum := tendsto_finsetSum (univ : Finset A) fun a _ => h a
  rwa [Finset.sum_boole] at hsum

/-- **Explicit error for natural-number costs.**  For `β ≥ 0`,
`0 ≤ ∑ a, exp (-β c a) - #{c = 0} ≤ (|A| - #{c = 0}) exp (-β)`. -/
theorem sum_exp_neg_mul_sub_card_filter_le {A : Type*} [Fintype A] (c : A → ℕ) {β : ℝ}
    (hβ : 0 ≤ β) :
    0 ≤ ∑ a, Real.exp (-β * c a) - (univ.filter fun a => c a = 0).card ∧
      ∑ a, Real.exp (-β * c a) - (univ.filter fun a => c a = 0).card ≤
        ((Fintype.card A : ℝ) - (univ.filter fun a => c a = 0).card) * Real.exp (-β) := by
  classical
  have hsplit : ∑ a, Real.exp (-β * c a) =
      ∑ a, (if c a = 0 then (1 : ℝ) else 0) +
        ∑ a, (if c a = 0 then (0 : ℝ) else Real.exp (-β * c a)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases h0 : c a = 0 <;> simp [h0]
  rw [hsplit, Finset.sum_boole, add_sub_cancel_left]
  have hnonneg : ∀ a, 0 ≤ (if c a = 0 then (0 : ℝ) else Real.exp (-β * c a)) := fun a => by
    split_ifs <;> positivity
  refine ⟨Finset.sum_nonneg fun a _ => hnonneg a, ?_⟩
  have hle : ∀ a, (if c a = 0 then (0 : ℝ) else Real.exp (-β * c a)) ≤
      if ¬ c a = 0 then Real.exp (-β) else 0 := fun a => by
    by_cases h0 : c a = 0
    · simp [h0]
    · simp only [h0, not_false_eq_true, ite_true, ite_false]
      refine Real.exp_le_exp.2 ?_
      have : (1 : ℝ) ≤ c a := Nat.one_le_cast.2 (Nat.pos_of_ne_zero h0)
      nlinarith
  calc _ ≤ ∑ a, (if ¬ c a = 0 then Real.exp (-β) else 0) :=
        Finset.sum_le_sum fun a _ => hle a
    _ = ((univ.filter fun a => ¬ c a = 0).card : ℝ) * Real.exp (-β) := by
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    _ = _ := by
      rw [Finset.filter_not, Finset.card_sdiff_of_subset (Finset.filter_subset _ _),
        Finset.card_univ, Nat.cast_sub (Finset.card_le_univ _)]
