/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.DecoupledSystems.SKFirstMoment
public import LeanMachineLearning.ForMathlib.Algebra.BigOperators.OffDiag
public import
  LeanMachineLearning.SpinGlasses.Talagrand.GuerraReplicaSymmetric.SKReplicaSymmetricBound

/-!
# Finite algebra for the replica computation (Talagrand, Eq. (1.397))

For `n` replicas of `N` spins,
`∑_{i<j} (∑_ℓ σ^ℓ_i σ^ℓ_j)² = (n N² - n² N) / 2 + ∑_{ℓ<ℓ'} (σ^ℓ · σ^ℓ')²`.
-/

@[expose] public section

open Finset
open scoped BigOperators

namespace SpinGlasses

/-- A symmetric double sum is the diagonal plus twice the sum over pairs `ℓ < ℓ'`. -/
theorem sum_fin_symm_eq_diag_add_two_sum_finPairs (n : ℕ) (f : Fin n → Fin n → ℝ)
    (hf : ∀ l l', f l l' = f l' l) :
    ∑ l, ∑ l', f l l' = ∑ l, f l l + 2 * ∑ p : FinPairs n, f p.val.1 p.val.2 := by
  have h1 : ∑ l, ∑ l', f l l' = ∑ l, ∑ l', ((if l = l' then f l l' else 0) +
      (if l = l' then 0 else f l l')) :=
    Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun l' _ => by
      by_cases h : l = l' <;> simp [h]
  rw [h1]
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [sum_sum_offDiag_eq_two_sum_lt f hf,
    ← sum_filter_lt_eq_sum_subtype fun p : Fin n × Fin n => f p.1 p.2]

/-- **Eq. (1.397).** For `n` replicas of `N` spins `s l i` with `s l i ^ 2 = 1`,
`∑_{i<j} (∑_ℓ s_ℓi s_ℓj)² = (n N² - n² N) / 2 + ∑_{ℓ<ℓ'} (∑_i s_ℓi s_ℓ'i)²`. -/
theorem sum_finPairs_sq_replicas (n N : ℕ) (s : Fin n → Fin N → ℝ) (hs : ∀ l i, s l i ^ 2 = 1) :
    ∑ p : FinPairs N, (∑ l, s l p.val.1 * s l p.val.2) ^ 2 =
      ((n : ℝ) * N ^ 2 - (n : ℝ) ^ 2 * N) / 2 +
        ∑ q : FinPairs n, (∑ i, s q.val.1 i * s q.val.2 i) ^ 2 := by
  set R : Fin n → Fin n → ℝ := fun l l' => ∑ i, s l i * s l' i with hR
  have hRsymm : ∀ l l', R l l' = R l' l := fun l l' => by
    simp only [hR, mul_comm]
  have hRdiag : ∀ l, R l l = N := fun l => by
    simp only [hR, ← sq, hs, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  have step1 : ∑ p : FinPairs N, (∑ l, s l p.val.1 * s l p.val.2) ^ 2 =
      ∑ l, ∑ l', ∑ p : FinPairs N,
        (s l p.val.1 * s l' p.val.1) * (s l p.val.2 * s l' p.val.2) := by
    simp_rw [sq, Finset.sum_mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l' _ => ?_
    refine Finset.sum_congr rfl fun p _ => ?_
    ring
  have step2 (l l' : Fin n) : ∑ p : FinPairs N,
      (s l p.val.1 * s l' p.val.1) * (s l p.val.2 * s l' p.val.2) = (R l l' ^ 2 - N) / 2 := by
    have := sum_finPairs_mul_eq_sub_sum_sq_div_two N (fun i => s l i * s l' i)
    rw [this]
    have hsq : ∑ i, (s l i * s l' i) ^ 2 = N := by
      simp only [mul_pow, hs, mul_one, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [hsq]
  simp_rw [step2] at step1
  rw [step1, sum_fin_symm_eq_diag_add_two_sum_finPairs n (fun l l' => (R l l' ^ 2 - N) / 2)
    (fun l l' => by simp only [hRsymm l l'])]
  simp only [hRdiag, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hq : ∑ q : FinPairs n, (R q.val.1 q.val.2 ^ 2 - N) / 2 =
      (∑ q : FinPairs n, R q.val.1 q.val.2 ^ 2) / 2 - (N : ℝ) * (n * (n - 1) / 2) / 2 := by
    rw [← Finset.sum_div, Finset.sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul,
      cast_card_finPairs]
    ring
  rw [hq]
  ring

end SpinGlasses
