/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.Replica.Variational.FinitePartition
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Derivative of the replica objective

Talagrand, *Spin Glasses* Vol. I, Section 1.13, Eq. (1.408): the derivative of the smooth
extension of the replica objective `Φ_n` to all real `q`, equal to
`n (n - 1) β² / 2 * (R_n(q) - q)` for `q ≥ 0`.
-/

@[expose] public section

open Finset Real MeasureTheory ProbabilityTheory Filter Topology Set
open scoped BigOperators

namespace SpinGlasses

theorem hasDerivAt_skReplicaSum (n : ℕ) (β h q : ℝ) :
    HasDerivAt (fun x => skReplicaSum n β h x)
      (∑ ε : Fin n → ℤˣ, Real.exp (h * ∑ l, ((ε l : ℤ) : ℝ) +
        β ^ 2 * (∑ l, ((ε l : ℤ) : ℝ)) ^ 2 * q / 2) *
        (β ^ 2 * (∑ l, ((ε l : ℤ) : ℝ)) ^ 2 / 2)) q := by
  simp only [skReplicaSum_def]
  refine HasDerivAt.fun_sum fun ε _ => ?_
  simpa only [mul_one, zero_add, Pi.add_apply, id_eq] using
    ((hasDerivAt_const q (h * ∑ l, ((ε l : ℤ) : ℝ))).add
      (((hasDerivAt_id q).const_mul
        (β ^ 2 * (∑ l, ((ε l : ℤ) : ℝ)) ^ 2)).div_const 2)).exp

theorem skReplicaSum_deriv_eq (n : ℕ) (β h q : ℝ) (hq : 0 ≤ q) :
    (∑ ε : Fin n → ℤˣ, Real.exp (h * ∑ l, ((ε l : ℤ) : ℝ) +
      β ^ 2 * (∑ l, ((ε l : ℤ) : ℝ)) ^ 2 * q / 2) *
      (β ^ 2 * (∑ l, ((ε l : ℤ) : ℝ)) ^ 2 / 2)) =
    (n : ℝ) * β ^ 2 / 2 * skReplicaSum n β h q +
      (n : ℝ) * ((n : ℝ) - 1) * β ^ 2 / 2 * (2 : ℝ) ^ n *
        ∫ z : ℝ, cosh (β * z * Real.sqrt q + h) ^ n *
          tanh (β * z * Real.sqrt q + h) ^ 2 ∂(gaussianReal 0 1) := by
  have hsplit (ε : Fin n → ℤˣ) :
      (∑ l, ((ε l : ℤ) : ℝ)) ^ 2 =
        (n : ℝ) + ((∑ l, ((ε l : ℤ) : ℝ)) ^ 2 - (n : ℝ)) := by ring
  have hsum : (∑ ε : Fin n → ℤˣ, Real.exp (h * ∑ l, ((ε l : ℤ) : ℝ) +
        β ^ 2 * (∑ l, ((ε l : ℤ) : ℝ)) ^ 2 * q / 2) *
        (β ^ 2 * (∑ l, ((ε l : ℤ) : ℝ)) ^ 2 / 2)) =
      β ^ 2 / 2 * ∑ ε : Fin n → ℤˣ, (∑ l, ((ε l : ℤ) : ℝ)) ^ 2 *
        Real.exp (h * ∑ l, ((ε l : ℤ) : ℝ) +
          β ^ 2 * (∑ l, ((ε l : ℤ) : ℝ)) ^ 2 * q / 2) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ε _ => by ring
  rw [hsum]
  have hsum2 : (∑ ε : Fin n → ℤˣ, (∑ l, ((ε l : ℤ) : ℝ)) ^ 2 *
        Real.exp (h * ∑ l, ((ε l : ℤ) : ℝ) +
          β ^ 2 * (∑ l, ((ε l : ℤ) : ℝ)) ^ 2 * q / 2)) =
      (n : ℝ) * skReplicaSum n β h q +
        ∑ ε : Fin n → ℤˣ, ((∑ l, ((ε l : ℤ) : ℝ)) ^ 2 - (n : ℝ)) *
          Real.exp (h * ∑ l, ((ε l : ℤ) : ℝ) +
            β ^ 2 * (∑ l, ((ε l : ℤ) : ℝ)) ^ 2 * q / 2) := by
    rw [skReplicaSum_def]
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ε _ => ?_
    rw [hsplit ε]
    ring
  rw [hsum2, sum_spin_sq_exp_integral n β h q hq]
  ring

theorem hasDerivAt_log_skReplicaSum (n : ℕ) (β h q : ℝ) :
    HasDerivAt (fun x => Real.log (skReplicaSum n β h x))
      ((∑ ε : Fin n → ℤˣ, Real.exp (h * ∑ l, ((ε l : ℤ) : ℝ) +
        β ^ 2 * (∑ l, ((ε l : ℤ) : ℝ)) ^ 2 * q / 2) *
        (β ^ 2 * (∑ l, ((ε l : ℤ) : ℝ)) ^ 2 / 2)) / skReplicaSum n β h q) q :=
  (hasDerivAt_skReplicaSum n β h q).log (skReplicaSum_pos n β h q).ne'

theorem hasDerivAt_log_skReplicaSum_of_nonneg (n : ℕ) (β h q : ℝ) (hq : 0 ≤ q) :
    HasDerivAt (fun x => Real.log (skReplicaSum n β h x))
      ((n : ℝ) * β ^ 2 / 2 +
        (n : ℝ) * ((n : ℝ) - 1) * β ^ 2 / 2 *
          ((∫ z : ℝ, cosh (β * z * Real.sqrt q + h) ^ n *
            tanh (β * z * Real.sqrt q + h) ^ 2 ∂(gaussianReal 0 1)) /
          (∫ z : ℝ, cosh (β * z * Real.sqrt q + h) ^ n ∂(gaussianReal 0 1)))) q := by
  have hlog := hasDerivAt_log_skReplicaSum n β h q
  have hderiv_eq := skReplicaSum_deriv_eq n β h q hq
  have hS_eq := skReplicaSum_eq_integral n β h q hq
  have h2n_ne : (2 : ℝ) ^ n ≠ 0 := (pow_pos two_pos n).ne'
  have hint_ne : (∫ z : ℝ, cosh (β * z * Real.sqrt q + h) ^ n ∂(gaussianReal 0 1)) ≠ 0 :=
    (integral_cosh_pow_sk_pos n β h q).ne'
  have h_eq : ((∑ ε : Fin n → ℤˣ, Real.exp (h * ∑ l, ((ε l : ℤ) : ℝ) +
        β ^ 2 * (∑ l, ((ε l : ℤ) : ℝ)) ^ 2 * q / 2) *
        (β ^ 2 * (∑ l, ((ε l : ℤ) : ℝ)) ^ 2 / 2)) / skReplicaSum n β h q) =
      ((n : ℝ) * β ^ 2 / 2 +
        (n : ℝ) * ((n : ℝ) - 1) * β ^ 2 / 2 *
          ((∫ z : ℝ, cosh (β * z * Real.sqrt q + h) ^ n *
            tanh (β * z * Real.sqrt q + h) ^ 2 ∂(gaussianReal 0 1)) /
          (∫ z : ℝ, cosh (β * z * Real.sqrt q + h) ^ n ∂(gaussianReal 0 1)))) := by
    rw [hderiv_eq, hS_eq]
    have hprod_ne : (2 : ℝ) ^ n *
        (∫ z : ℝ, cosh (β * z * Real.sqrt q + h) ^ n ∂(gaussianReal 0 1)) ≠ 0 :=
      mul_ne_zero h2n_ne hint_ne
    rw [add_div]
    congr 1
    · exact mul_div_cancel_right₀ _ hprod_ne
    · rw [mul_assoc ((n : ℝ) * ((n : ℝ) - 1) * β ^ 2 / 2), mul_div_assoc]
      congr 1
      exact mul_div_mul_left _ _ h2n_ne
  exact hlog.congr_deriv h_eq

theorem hasDerivAt_skReplicaPoly (n : ℕ) (β q : ℝ) :
    HasDerivAt (fun x => (n : ℝ) * β ^ 2 * (1 - x) ^ 2 / 4 -
      (n : ℝ) ^ 2 * β ^ 2 * x ^ 2 / 4)
      (-((n : ℝ) * β ^ 2 / 2) - (n : ℝ) * ((n : ℝ) - 1) * β ^ 2 / 2 * q) q := by
  have h1 : (fun x => (n : ℝ) * β ^ 2 * (1 - x) ^ 2 / 4 -
      (n : ℝ) ^ 2 * β ^ 2 * x ^ 2 / 4) =
    (fun x => ((n : ℝ) * β ^ 2 / 4) +
      (-((n : ℝ) * β ^ 2 / 2)) * x +
      ((n : ℝ) * (1 - (n : ℝ)) * β ^ 2 / 4) * x ^ 2) := by
    ext x; ring
  rw [h1]
  have hd1 := ((hasDerivAt_id q).const_mul (-((n : ℝ) * β ^ 2 / 2))).const_add
    ((n : ℝ) * β ^ 2 / 4)
  have hd2 : HasDerivAt (fun x => ((n : ℝ) * (1 - (n : ℝ)) * β ^ 2 / 4) * x ^ 2)
      (((n : ℝ) * (1 - (n : ℝ)) * β ^ 2 / 4) * (2 * q)) q := by
    simpa using ((hasDerivAt_id q).pow 2).const_mul ((n : ℝ) * (1 - (n : ℝ)) * β ^ 2 / 4)
  have hd := hd1.add hd2
  have hval : (-((n : ℝ) * β ^ 2 / 2) * 1 + ((n : ℝ) * (1 - (n : ℝ)) * β ^ 2 / 4) * (2 * q)) =
      (-((n : ℝ) * β ^ 2 / 2) - (n : ℝ) * ((n : ℝ) - 1) * β ^ 2 / 2 * q) := by ring
  exact hd.congr_deriv hval

/-- Replica free-energy function $F_n(q)$ expressed in terms of the finite configuration
sum `skReplicaSum`. -/
noncomputable def skReplicaF (n : ℕ) (β h q : ℝ) : ℝ :=
  (n : ℝ) * β ^ 2 * (1 - q) ^ 2 / 4 - (n : ℝ) ^ 2 * β ^ 2 * q ^ 2 / 4 +
    Real.log (skReplicaSum n β h q) - (n : ℝ) * Real.log 2

theorem skReplicaF_def (n : ℕ) (β h q : ℝ) :
    skReplicaF n β h q =
      (n : ℝ) * β ^ 2 * (1 - q) ^ 2 / 4 - (n : ℝ) ^ 2 * β ^ 2 * q ^ 2 / 4 +
        Real.log (skReplicaSum n β h q) - (n : ℝ) * Real.log 2 := rfl

theorem skReplicaF_eq_phi (n : ℕ) (β h q : ℝ) (hq : 0 ≤ q) :
    skReplicaF n β h q =
      (n : ℝ) * β ^ 2 * (1 - q) ^ 2 / 4 - (n : ℝ) ^ 2 * β ^ 2 * q ^ 2 / 4 +
        Real.log (∫ z : ℝ, cosh (β * z * Real.sqrt q + h) ^ n ∂(gaussianReal 0 1)) := by
  have hS := skReplicaSum_eq_integral n β h q hq
  have h2n_pos : (0 : ℝ) < (2 : ℝ) ^ n := pow_pos two_pos n
  have hint_pos := integral_cosh_pow_sk_pos n β h q
  dsimp [skReplicaF]
  rw [hS, Real.log_mul h2n_pos.ne' hint_pos.ne', Real.log_pow]
  ring

theorem hasDerivAt_skReplicaF (n : ℕ) (β h q : ℝ) (hq : 0 ≤ q) :
    HasDerivAt (skReplicaF n β h)
      ((n : ℝ) * ((n : ℝ) - 1) * β ^ 2 / 2 *
        (((∫ z : ℝ, cosh (β * z * Real.sqrt q + h) ^ n *
          tanh (β * z * Real.sqrt q + h) ^ 2 ∂(gaussianReal 0 1)) /
        (∫ z : ℝ, cosh (β * z * Real.sqrt q + h) ^ n ∂(gaussianReal 0 1))) - q)) q := by
  have hp := hasDerivAt_skReplicaPoly n β q
  have hl := hasDerivAt_log_skReplicaSum_of_nonneg n β h q hq
  have htot := (hp.add hl).sub_const ((n : ℝ) * Real.log 2)
  have hval : -((n : ℝ) * β ^ 2 / 2) - (n : ℝ) * ((n : ℝ) - 1) * β ^ 2 / 2 * q +
      ((n : ℝ) * β ^ 2 / 2 +
        (n : ℝ) * ((n : ℝ) - 1) * β ^ 2 / 2 *
          ((∫ z : ℝ, cosh (β * z * Real.sqrt q + h) ^ n *
            tanh (β * z * Real.sqrt q + h) ^ 2 ∂(gaussianReal 0 1)) /
          (∫ z : ℝ, cosh (β * z * Real.sqrt q + h) ^ n ∂(gaussianReal 0 1)))) =
      (n : ℝ) * ((n : ℝ) - 1) * β ^ 2 / 2 *
        (((∫ z : ℝ, cosh (β * z * Real.sqrt q + h) ^ n *
          tanh (β * z * Real.sqrt q + h) ^ 2 ∂(gaussianReal 0 1)) /
        (∫ z : ℝ, cosh (β * z * Real.sqrt q + h) ^ n ∂(gaussianReal 0 1))) - q) := by ring
  have htot' := htot.congr_deriv hval
  exact htot'

lemma exists_gt_of_hasDerivAt_zero_pos {f : ℝ → ℝ} {c : ℝ} (hd : HasDerivAt f c 0) (hc : 0 < c) :
    ∃ x : ℝ, 0 < x ∧ f 0 < f x := by
  have ht := (hd.tendsto_slope_zero.mono_left (nhdsGT_le_nhdsNE 0)).eventually (Ioi_mem_nhds hc)
  have h_both := ht.and self_mem_nhdsWithin
  rcases h_both.exists with ⟨x, hx_slope, hx_pos⟩
  refine ⟨x, hx_pos, ?_⟩
  simp only [zero_add, smul_eq_mul] at hx_slope
  exact sub_pos.1 ((mul_pos_iff_of_pos_left (inv_pos.2 hx_pos)).1 hx_slope)

end SpinGlasses
