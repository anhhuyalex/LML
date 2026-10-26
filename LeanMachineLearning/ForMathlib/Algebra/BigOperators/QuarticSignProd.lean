/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Products of four signs

If `ε r ^ 2 = 1` for all `r`, a product of four signs `ε x ε y ε a ε b` with `x ≠ y` and `a ≠ b` is
a product `∏_{r ∈ I} ε r` over a set `I` with `|I| = 4 - 2 c`, where `c` is the number of
coincidences among `x, y, a, b`.  This is the combinatorial input to the algebra of Talagrand's
Section 1.8 (the decoupled average of `ε_x ε_y ε_a ε_b` is `𝔼 tanh^{|I|}`).
-/

@[expose] public section

open Finset

/-- **Products of four signs.** -/
theorem exists_finset_prod_eq_quartic {R A : Type*} [DecidableEq R] [CommRing A] {x y a b : R}
    (hxy : x ≠ y) (hab : a ≠ b) :
    ∃ I : Finset R, I.card + 2 * ((if x = a then 1 else 0) + (if x = b then 1 else 0) +
        (if y = a then 1 else 0) + (if y = b then 1 else 0)) = 4 ∧
      ∀ ε : R → A, (∀ r, ε r ^ 2 = 1) →
        ε x * ε y * ε a * ε b = ∏ r ∈ I, ε r := by
  by_cases h1 : x = a
  · subst h1
    by_cases h4 : y = b
    · subst h4
      refine ⟨∅, by simp [hxy, hxy.symm], fun ε hε => ?_⟩
      rw [prod_empty]
      calc ε x * ε y * ε x * ε y = ε x ^ 2 * ε y ^ 2 := by ring
        _ = 1 := by rw [hε, hε]; norm_num
    · refine ⟨{y, b}, ?_, fun ε hε => ?_⟩
      · rw [card_pair h4]; simp [hab, hxy.symm, h4]
      · rw [prod_pair h4]
        calc ε x * ε y * ε x * ε b = ε x ^ 2 * (ε y * ε b) := by ring
          _ = _ := by rw [hε, one_mul]
  · by_cases h2 : x = b
    · subst h2
      by_cases h3 : y = a
      · subst h3
        refine ⟨∅, by simp [hxy, hxy.symm], fun ε hε => ?_⟩
        rw [prod_empty]
        calc ε x * ε y * ε y * ε x = ε x ^ 2 * ε y ^ 2 := by ring
          _ = 1 := by rw [hε, hε]; norm_num
      · refine ⟨{y, a}, ?_, fun ε hε => ?_⟩
        · rw [card_pair h3]; simp [h1, hxy.symm, h3]
        · rw [prod_pair h3]
          calc ε x * ε y * ε a * ε x = ε x ^ 2 * (ε y * ε a) := by ring
            _ = _ := by rw [hε, one_mul]
    · by_cases h3 : y = a
      · subst h3
        refine ⟨{x, b}, ?_, fun ε hε => ?_⟩
        · rw [card_pair h2]; simp [h1, h2, hab]
        · rw [prod_pair h2]
          calc ε x * ε y * ε y * ε b = ε y ^ 2 * (ε x * ε b) := by ring
            _ = _ := by rw [hε, one_mul]
      · by_cases h4 : y = b
        · subst h4
          refine ⟨{x, a}, ?_, fun ε hε => ?_⟩
          · rw [card_pair h1]; simp [h1, h2, h3]
          · rw [prod_pair h1]
            calc ε x * ε y * ε a * ε y = ε y ^ 2 * (ε x * ε a) := by ring
              _ = _ := by rw [hε, one_mul]
        · refine ⟨{x, y, a, b}, ?_, fun ε hε => ?_⟩
          · rw [card_insert_of_notMem, card_insert_of_notMem, card_pair hab]
            · simp [h1, h2, h3, h4]
            · simp [h3, h4]
            · simp [hxy, h1, h2]
          · rw [prod_insert, prod_insert, prod_pair hab]
            · ring
            · simp [h3, h4]
            · simp [hxy, h1, h2]
