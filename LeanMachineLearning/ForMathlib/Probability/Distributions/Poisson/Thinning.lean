/-
Copyright (c) 2026 LML contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML contributors
-/
module

public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Probability.Distributions.Poisson.Basic

/-!
# Poisson thinning

This file isolates the algebraic law underlying finite Poisson thinning. Rather than introducing a
categorical-distribution wrapper, the main theorem states the probability mass calculation directly.
-/

@[expose] public section

open MeasureTheory Real
open scoped NNReal Nat

namespace ProbabilityTheory

/-- If prescribed multiplicities have total zero, there is exactly one word with those
multiplicities. This is the base case for the finite categorical count law. -/
theorem multinomial_eq_card_words_zero {ι : Type*} [Fintype ι] [DecidableEq ι] (m : ι → ℕ)
    (hm : ∑ i, m i = 0) :
    Nat.multinomial Finset.univ m =
      Fintype.card {x : Fin 0 → ι // ∀ i, (List.ofFn x).count i = m i} := by
  have hm0 : m = 0 := by
    funext i
    apply Nat.eq_zero_of_le_zero
    have hi : m i ≤ ∑ j, m j :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    simpa [hm] using hi
  subst m
  rw [Nat.multinomial]
  simp

/-- The Poisson-weighted multinomial mass factors into independent Poisson masses. This is the
algebraic core of finite Poisson thinning. -/
theorem poisson_mul_multinomial_eq_prod_poisson {ι : Type*} [Fintype ι]
    (r : ℝ≥0) (p : ι → ℝ≥0) (hp : ∑ i, p i = 1) (m : ι → ℕ) :
    Po(r) ({Finset.univ.sum m} : Set ℕ) *
        ENNReal.ofNNReal (Nat.multinomial Finset.univ m) *
        Finset.univ.prod (fun i => ENNReal.ofNNReal (p i) ^ m i) =
      Finset.univ.prod (fun i => Po(r * p i) ({m i} : Set ℕ)) := by
  classical
  simp only [poissonMeasure_singleton]
  push_cast
  rw [← ENNReal.ofReal_natCast]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun _ _ => by positivity)]
  rw [show Finset.univ.prod (fun i => ENNReal.ofNNReal (p i) ^ m i) =
    ENNReal.ofReal (Finset.univ.prod fun i => (p i : ℝ) ^ m i) by
      rw [ENNReal.ofReal_prod_of_nonneg]
      · apply Finset.prod_congr rfl
        intro i hi
        rw [ENNReal.ofReal_pow (NNReal.zero_le_coe)]
        simp
      · intro i hi
        positivity]
  rw [← ENNReal.ofReal_mul (by positivity)]
  rw [← ENNReal.ofReal_mul (by positivity)]
  apply (ENNReal.ofReal_eq_ofReal_iff (by positivity) (by positivity)).2
  have hp' : ∑ i, (p i : ℝ) = 1 := by exact_mod_cast hp
  rw [Finset.prod_div_distrib]
  rw [Finset.prod_mul_distrib]
  rw [← Real.exp_sum]
  rw [show (∑ x, -(↑r * (p x : ℝ))) = -(↑r * ∑ x, (p x : ℝ)) by
    rw [Finset.mul_sum, Finset.sum_neg_distrib]]
  rw [hp', mul_one]
  simp_rw [mul_pow]
  rw [Finset.prod_mul_distrib]
  rw [← Finset.prod_pow_eq_pow_sum]
  rw [← Nat.cast_prod]
  have hmult : ((∏ i, (m i)!) : ℝ) * Nat.multinomial Finset.univ m =
      (Finset.univ.sum m)! := by
    exact_mod_cast Nat.multinomial_spec Finset.univ m
  rw [← hmult]
  have hmn : (Nat.multinomial Finset.univ m : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.multinomial_pos Finset.univ m))
  field_simp [hmn]
  push_cast
  ring

end ProbabilityTheory
