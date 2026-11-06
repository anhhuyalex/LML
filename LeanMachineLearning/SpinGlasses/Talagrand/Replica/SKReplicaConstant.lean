/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.Replica.SKReplicaBridge

/-!
# Constant couplings (Talagrand, the end of the proof of Theorem 1.13.1)

For the constant matrix with off-diagonal entries `V = β q ≥ 0`,
`∑_ε exp (β V ∑_{ℓ<ℓ'} ε_ℓ ε_ℓ' + h ∑ ε) = exp (- n β V / 2) 𝔼 (2 ch (√(β V) z + h))^n`.
-/

@[expose] public section

open Finset Real MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace SpinGlasses

variable {n : ℕ}

/-- The quadratic form of a constant coupling matrix: `∑_{ℓ≠ℓ'} a_ℓ a_ℓ' = (∑ a)² - ∑ a²`. -/
theorem sum_const_coupling (V : ℝ) (a : Fin n → ℝ) :
    ∑ l, ∑ l', (if l = l' then 0 else V) * a l * a l' = V * ((∑ l, a l) ^ 2 - ∑ l, a l ^ 2) := by
  have h1 : ∀ l l' : Fin n, (if l = l' then (0 : ℝ) else V) * a l * a l' =
      V * (a l * a l') - (if l = l' then V * (a l * a l') else 0) := by
    intro l l'
    by_cases h : l = l' <;> simp [h]
    ring
  have h2 : ∑ x, ∑ x', V * (a x * a x') = V * (∑ l, a l) ^ 2 := by
    rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
  simp_rw [h1, Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [h2, ← Finset.mul_sum]
  simp only [sq]
  ring

/-- **Step (e) of the proof of Theorem 1.13.1.** For constant off-diagonal couplings `V` with
`β V ≥ 0`, `exp A = exp (- n β V / 2) 𝔼 (2 ch (√(β V) z + h))^n`. -/
theorem exp_skReplicaMatLogPartition_const (β h V : ℝ) (hβV : 0 ≤ β * V) :
    Real.exp (skReplicaMatLogPartition n β h (fun l l' => if l = l' then 0 else V)) =
      Real.exp (-(n * β * V) / 2) * ∫ z : ℝ, (2 * cosh (Real.sqrt (β * V) * z + h)) ^ n
        ∂(gaussianReal 0 1) := by
  unfold skReplicaMatLogPartition
  rw [Real.exp_log (Finset.sum_pos (fun ε _ => Real.exp_pos _) Finset.univ_nonempty)]
  have hsq : Real.sqrt (β * V) ^ 2 = β * V := Real.sq_sqrt hβV
  have hterm (ε : Fin n → ℤˣ) :
      Real.exp (β / 2 * ∑ l, ∑ l', (if l = l' then 0 else V) * ((ε l : ℤ) : ℝ) *
        ((ε l' : ℤ) : ℝ) + h * ∑ l, ((ε l : ℤ) : ℝ)) =
      Real.exp (-(n * β * V) / 2) * ∫ z : ℝ, Real.exp ((Real.sqrt (β * V) * z + h) *
        ∑ l, ((ε l : ℤ) : ℝ)) ∂(gaussianReal 0 1) := by
    have hsum : ∑ l, ((ε l : ℤ) : ℝ) ^ 2 = n := by
      simp [units_cast_sq]
    rw [sum_const_coupling V (fun l => ((ε l : ℤ) : ℝ)), hsum]
    have hz : ∀ z : ℝ, Real.exp ((Real.sqrt (β * V) * z + h) * ∑ l, ((ε l : ℤ) : ℝ)) =
        Real.exp (h * ∑ l, ((ε l : ℤ) : ℝ)) *
          Real.exp ((Real.sqrt (β * V) * ∑ l, ((ε l : ℤ) : ℝ)) * z) := fun z => by
      rw [← Real.exp_add]; congr 1; ring
    simp_rw [hz]
    rw [integral_const_mul, integral_exp_mul_gaussianReal_zero_one, mul_pow, hsq,
      ← mul_assoc, mul_comm (Real.exp (-(n * β * V) / 2)), mul_assoc, ← Real.exp_add,
      ← Real.exp_add]
    congr 1
    ring
  simp_rw [hterm]
  rw [← Finset.mul_sum]
  congr 1
  rw [← integral_finsetSum]
  · refine integral_congr_ae (ae_of_all _ fun z => ?_)
    exact sum_exp_h_mul_spin _
  · intro ε _
    have hz : ∀ z : ℝ, Real.exp ((Real.sqrt (β * V) * z + h) * ∑ l, ((ε l : ℤ) : ℝ)) =
        Real.exp (h * ∑ l, ((ε l : ℤ) : ℝ)) *
          Real.exp ((Real.sqrt (β * V) * ∑ l, ((ε l : ℤ) : ℝ)) * z) := fun z => by
      rw [← Real.exp_add]; congr 1; ring
    simp_rw [hz]
    exact (integrable_exp_mul_gaussianReal _).const_mul _

theorem sum_sq_const_coupling (V : ℝ) :
    ∑ l : Fin n, ∑ l' : Fin n, (if l = l' then (0 : ℝ) else V) ^ 2 = n * (n - 1) * V ^ 2 := by
  have h1 : ∀ l l' : Fin n, (if l = l' then (0 : ℝ) else V) ^ 2 =
      V ^ 2 - (if l = l' then V ^ 2 else 0) := by
    intro l l'
    by_cases h : l = l' <;> simp [h]
  simp_rw [h1, Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  ring

/-- **The value of `B` at a constant matrix** (step (e)): for `β > 0` and `q ≥ 0`,
`B = n log 2 + Φ_n(q) - n β²/4`, where
`Φ_n(q) = n β² (1-q)²/4 - n² β² q²/4 + log 𝔼 ch^n(β z √q + h)`. -/
theorem skReplicaMatObjective_const (β h q : ℝ) (hβ : 0 < β) (hq : 0 ≤ q) :
    skReplicaMatObjective n β h (fun l l' => if l = l' then 0 else β * q) =
      n * Real.log 2 + (n * β ^ 2 * (1 - q) ^ 2 / 4 - n ^ 2 * β ^ 2 * q ^ 2 / 4 +
        Real.log (∫ z : ℝ, cosh (β * z * Real.sqrt q + h) ^ n ∂(gaussianReal 0 1))) -
          n * β ^ 2 / 4 := by
  have hβq : 0 ≤ β * (β * q) := by positivity
  have hsq : Real.sqrt (β * (β * q)) = β * Real.sqrt q := by
    rw [← mul_assoc, ← sq, Real.sqrt_mul (sq_nonneg β), Real.sqrt_sq hβ.le]
  have hexp := exp_skReplicaMatLogPartition_const (n := n) β h (β * q) hβq
  have hint : ∫ z : ℝ, (2 * cosh (Real.sqrt (β * (β * q)) * z + h)) ^ n ∂(gaussianReal 0 1) =
      2 ^ n * ∫ z : ℝ, cosh (β * z * Real.sqrt q + h) ^ n ∂(gaussianReal 0 1) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    simp only [mul_pow, hsq]
    congr 3
    ring
  rw [hint] at hexp
  have hApos : 0 < Real.exp (skReplicaMatLogPartition n β h
      (fun l l' => if l = l' then 0 else β * q)) := Real.exp_pos _
  rw [hexp] at hApos
  have hI : 0 < ∫ z : ℝ, cosh (β * z * Real.sqrt q + h) ^ n ∂(gaussianReal 0 1) := by
    by_contra hnot
    have : ∫ z : ℝ, cosh (β * z * Real.sqrt q + h) ^ n ∂(gaussianReal 0 1) ≤ 0 := not_lt.1 hnot
    have h2 : Real.exp (-(n * β * (β * q)) / 2) * (2 ^ n * ∫ z : ℝ,
        cosh (β * z * Real.sqrt q + h) ^ n ∂(gaussianReal 0 1)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
        (mul_nonpos_of_nonneg_of_nonpos (pow_pos two_pos n).le this)
    linarith
  have hA : skReplicaMatLogPartition n β h (fun l l' => if l = l' then 0 else β * q) =
      -(n * β * (β * q)) / 2 + (n * Real.log 2 +
        Real.log (∫ z : ℝ, cosh (β * z * Real.sqrt q + h) ^ n ∂(gaussianReal 0 1))) := by
    apply Real.exp_injective
    rw [hexp, Real.exp_add, Real.exp_add, Real.exp_log hI, ← Real.log_pow,
      Real.exp_log (by positivity)]
  unfold skReplicaMatObjective
  rw [hA, sum_sq_const_coupling]
  ring

end SpinGlasses
