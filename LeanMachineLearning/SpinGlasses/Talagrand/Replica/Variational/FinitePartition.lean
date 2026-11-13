/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.Replica.Moments.Hyperbolic
public import LeanMachineLearning.ForMathlib.Algebra.BigOperators.HypercubeProduct

/-!
# Finite spin sum behind the replica variational problem

Talagrand, *Spin Glasses* Vol. I, Section 1.13, Eq. (1.408): the finite sum `skReplicaSum` over
spin configurations of `n` replicas, its equality with `2^n 𝔼 ch^n(β z √q + h)` for `q ≥ 0`, and the
spin-sum identities used to differentiate it.
-/

@[expose] public section

open Finset Real MeasureTheory ProbabilityTheory Filter Topology Set
open scoped BigOperators

namespace SpinGlasses

/-- Finite replica partition sum $\sum_{\varepsilon} \exp(h \sum_l \varepsilon_l +
\frac{\beta^2 q}{2} (\sum_l \varepsilon_l)^2)$. -/
noncomputable def skReplicaSum (n : ℕ) (β h q : ℝ) : ℝ :=
  ∑ ε : Fin n → ℤˣ, Real.exp (h * ∑ l, ((ε l : ℤ) : ℝ) +
    β ^ 2 * (∑ l, ((ε l : ℤ) : ℝ)) ^ 2 * q / 2)

theorem skReplicaSum_def (n : ℕ) (β h q : ℝ) :
    skReplicaSum n β h q =
      ∑ ε : Fin n → ℤˣ, Real.exp (h * ∑ l, ((ε l : ℤ) : ℝ) +
        β ^ 2 * (∑ l, ((ε l : ℤ) : ℝ)) ^ 2 * q / 2) := rfl

theorem skReplicaSum_pos (n : ℕ) (β h q : ℝ) : 0 < skReplicaSum n β h q := by
  rw [skReplicaSum_def]
  exact Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty

theorem skReplicaSum_eq_integral (n : ℕ) (β h q : ℝ) (hq : 0 ≤ q) :
    skReplicaSum n β h q = (2 : ℝ) ^ n *
      ∫ z : ℝ, cosh (β * z * Real.sqrt q + h) ^ n ∂(gaussianReal 0 1) := by
  have hz (ε : Fin n → ℤˣ) (z : ℝ) :
      Real.exp ((β * z * Real.sqrt q + h) * ∑ l, ((ε l : ℤ) : ℝ)) =
        Real.exp (h * ∑ l, ((ε l : ℤ) : ℝ)) *
          Real.exp ((β * Real.sqrt q * ∑ l, ((ε l : ℤ) : ℝ)) * z) := by
    rw [← Real.exp_add]; congr 1; ring
  have hsq : (β * Real.sqrt q) ^ 2 = β ^ 2 * q := by
    rw [mul_pow, Real.sq_sqrt hq]
  have hterm (ε : Fin n → ℤˣ) :
      Real.exp (h * ∑ l, ((ε l : ℤ) : ℝ) +
        β ^ 2 * (∑ l, ((ε l : ℤ) : ℝ)) ^ 2 * q / 2) =
      ∫ z : ℝ, Real.exp ((β * z * Real.sqrt q + h) * ∑ l, ((ε l : ℤ) : ℝ))
        ∂(gaussianReal 0 1) := by
    simp_rw [hz ε]
    rw [integral_const_mul, integral_exp_mul_gaussianReal_zero_one, mul_pow, hsq,
      ← Real.exp_add]
    congr 1
    ring
  rw [skReplicaSum_def]
  simp_rw [hterm]
  rw [← integral_finsetSum]
  · have heq (z : ℝ) : (∑ ε : Fin n → ℤˣ,
        Real.exp ((β * z * Real.sqrt q + h) * ∑ l, ((ε l : ℤ) : ℝ))) =
          (2 : ℝ) ^ n * cosh (β * z * Real.sqrt q + h) ^ n := by
      have := sum_exp_h_mul_spin (N := n) (β * z * Real.sqrt q + h)
      rw [mul_pow] at this
      exact this
    simp_rw [heq]
    rw [integral_const_mul]
  · intro ε _
    simp_rw [hz ε]
    exact (integrable_exp_mul_gaussianReal _).const_mul _

theorem sum_spin_pair_exp_eq (n : ℕ) (Y : ℝ) (a b : Fin n) (hab : a ≠ b) :
    ∑ ε : Fin n → ℤˣ, ((ε a : ℤ) : ℝ) * ((ε b : ℤ) : ℝ) *
        Real.exp (Y * ∑ l, ((ε l : ℤ) : ℝ)) =
      (2 * cosh Y) ^ n * tanh Y ^ 2 := by
  let f : Fin n → ℤˣ → ℝ := fun i s =>
    if i = a then ((s : ℤ) : ℝ) * Real.exp (((s : ℤ) : ℝ) * Y)
    else if i = b then ((s : ℤ) : ℝ) * Real.exp (((s : ℤ) : ℝ) * Y)
    else Real.exp (((s : ℤ) : ℝ) * Y)
  have ha : a ∈ Finset.univ := Finset.mem_univ a
  have hb : b ∈ Finset.univ.erase a := Finset.mem_erase.2 ⟨hab.symm, Finset.mem_univ b⟩
  have hprod (ε : Fin n → ℤˣ) : ((ε a : ℤ) : ℝ) * ((ε b : ℤ) : ℝ) *
      Real.exp (Y * ∑ l, ((ε l : ℤ) : ℝ)) = ∏ i, f i (ε i) := by
    have h1 : Real.exp (Y * ∑ l, ((ε l : ℤ) : ℝ)) = ∏ i, Real.exp (((ε i : ℤ) : ℝ) * Y) := by
      rw [← Real.exp_sum]
      congr 1
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => mul_comm _ _
    have hfa : f a (ε a) = ((ε a : ℤ) : ℝ) * Real.exp (((ε a : ℤ) : ℝ) * Y) := by simp [f]
    have hfb : f b (ε b) = ((ε b : ℤ) : ℝ) * Real.exp (((ε b : ℤ) : ℝ) * Y) := by
      simp [f, hab.symm]
    have hrest : ∏ i ∈ (Finset.univ.erase a).erase b, f i (ε i) =
        ∏ i ∈ (Finset.univ.erase a).erase b, Real.exp (((ε i : ℤ) : ℝ) * Y) := by
      refine Finset.prod_congr rfl fun i hi => ?_
      have hia : i ≠ a := (Finset.mem_erase.1 (Finset.mem_of_mem_erase hi)).1
      have hib : i ≠ b := (Finset.mem_erase.1 hi).1
      simp [f, hia, hib]
    rw [← Finset.mul_prod_erase Finset.univ (fun i => f i (ε i)) ha]
    rw [← Finset.mul_prod_erase (Finset.univ.erase a) (fun i => f i (ε i)) hb]
    rw [hfa, hfb, hrest, h1]
    rw [← Finset.mul_prod_erase Finset.univ _ ha]
    rw [← Finset.mul_prod_erase (Finset.univ.erase a) _ hb]
    ring
  simp_rw [hprod]
  rw [hypercube_sum_prod_eq_prod_add f]
  rw [← Finset.mul_prod_erase Finset.univ _ ha]
  rw [← Finset.mul_prod_erase (Finset.univ.erase a) _ hb]
  have hfa : f a 1 + f a (-1) = 2 * Real.sinh Y := by
    simp [f, Real.sinh_eq]; ring
  have hfb : f b 1 + f b (-1) = 2 * Real.sinh Y := by
    simp [f, hab.symm, Real.sinh_eq]; ring
  have hrest : ∏ i ∈ (Finset.univ.erase a).erase b, (f i 1 + f i (-1)) =
      ∏ i ∈ (Finset.univ.erase a).erase b, (2 * Real.cosh Y) := by
    refine Finset.prod_congr rfl fun i hi => ?_
    have hia : i ≠ a := (Finset.mem_erase.1 (Finset.mem_of_mem_erase hi)).1
    have hib : i ≠ b := (Finset.mem_erase.1 hi).1
    simp [f, hia, hib, Real.cosh_eq]
    ring
  rw [hfa, hfb, hrest, Finset.prod_const]
  have hcard : ((Finset.univ.erase a).erase b).card = n - 2 := by
    rw [Finset.card_erase_of_mem hb, Finset.card_erase_of_mem ha,
      Finset.card_univ, Fintype.card_fin]
    omega
  rw [hcard]
  have hn2 : 2 ≤ n := by
    have := Fintype.card_fin n
    by_contra! hlt
    interval_cases n
    · exact hab (Subsingleton.elim a b)
    · exact hab (Subsingleton.elim a b)
  have hpow : (2 * Real.cosh Y) ^ n =
      (2 * Real.cosh Y) ^ 2 * (2 * Real.cosh Y) ^ (n - 2) := by
    rw [← pow_add]
    congr 1
    omega
  rw [hpow]
  have htanh : Real.tanh Y = Real.sinh Y / Real.cosh Y := Real.tanh_eq_sinh_div_cosh Y
  rw [htanh, div_pow]
  have hch : Real.cosh Y ≠ 0 := (Real.cosh_pos Y).ne'
  have hmul : (2 * Real.cosh Y) ^ 2 * (Real.sinh Y ^ 2 / Real.cosh Y ^ 2) =
      4 * Real.sinh Y ^ 2 := by
    calc (2 * Real.cosh Y) ^ 2 * (Real.sinh Y ^ 2 / Real.cosh Y ^ 2)
      _ = (4 * Real.cosh Y ^ 2) * (Real.sinh Y ^ 2 / Real.cosh Y ^ 2) := by ring
      _ = 4 * (Real.cosh Y ^ 2 * (Real.sinh Y ^ 2 / Real.cosh Y ^ 2)) := by ring
      _ = 4 * Real.sinh Y ^ 2 := by
        rw [mul_div_cancel₀ _ (pow_ne_zero 2 hch)]
  calc (2 * Real.sinh Y) * ((2 * Real.sinh Y) * (2 * Real.cosh Y) ^ (n - 2))
    _ = 4 * Real.sinh Y ^ 2 * (2 * Real.cosh Y) ^ (n - 2) := by ring
    _ = (2 * Real.cosh Y) ^ 2 * (Real.sinh Y ^ 2 / Real.cosh Y ^ 2) *
          (2 * Real.cosh Y) ^ (n - 2) := by rw [hmul]
    _ = (2 * Real.cosh Y) ^ 2 * (2 * Real.cosh Y) ^ (n - 2) *
          (Real.sinh Y ^ 2 / Real.cosh Y ^ 2) := by ring

theorem sum_spin_sq_sub_n_exp_eq (n : ℕ) (Y : ℝ) :
    ∑ ε : Fin n → ℤˣ, ((∑ l, ((ε l : ℤ) : ℝ)) ^ 2 - (n : ℝ)) *
        Real.exp (Y * ∑ l, ((ε l : ℤ) : ℝ)) =
      (n : ℝ) * ((n : ℝ) - 1) * (2 * cosh Y) ^ n * tanh Y ^ 2 := by
  have h1 (ε : Fin n → ℤˣ) : (∑ l, ((ε l : ℤ) : ℝ)) ^ 2 - (n : ℝ) =
      ∑ l, ∑ l', if l = l' then (0 : ℝ) else ((ε l : ℤ) : ℝ) * ((ε l' : ℤ) : ℝ) := by
    have hsum : ∑ l, ((ε l : ℤ) : ℝ) ^ 2 = (n : ℝ) := by
      simp [units_cast_sq]
    have := sum_const_coupling (n := n) 1 (fun l => ((ε l : ℤ) : ℝ))
    simp only [one_mul] at this
    rw [← hsum, ← this]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun l' _ => ?_
    by_cases h : l = l' <;> simp [h]
  simp_rw [h1, Finset.sum_mul]
  rw [Finset.sum_comm]
  have hswap : (∑ x : Fin n, ∑ ε : Fin n → ℤˣ, ∑ l' : Fin n,
        (if x = l' then (0 : ℝ) else ((ε x : ℤ) : ℝ) * ((ε l' : ℤ) : ℝ)) *
          Real.exp (Y * ∑ l, ((ε l : ℤ) : ℝ))) =
      ∑ x : Fin n, ∑ l' : Fin n, ∑ ε : Fin n → ℤˣ,
        (if x = l' then (0 : ℝ) else ((ε x : ℤ) : ℝ) * ((ε l' : ℤ) : ℝ)) *
          Real.exp (Y * ∑ l, ((ε l : ℤ) : ℝ)) := by
    refine Finset.sum_congr rfl fun x _ => Finset.sum_comm
  rw [hswap]
  have hterm (l l' : Fin n) : (∑ ε : Fin n → ℤˣ,
        (if l = l' then (0 : ℝ) else ((ε l : ℤ) : ℝ) * ((ε l' : ℤ) : ℝ)) *
          Real.exp (Y * ∑ k, ((ε k : ℤ) : ℝ))) =
      (if l = l' then (0 : ℝ) else 1) *
        ((2 * cosh Y) ^ n * tanh Y ^ 2) := by
    by_cases hll : l = l'
    · subst hll; simp
    · simp only [hll, ite_false, one_mul]
      exact sum_spin_pair_exp_eq n Y l l' hll
  simp_rw [hterm, ← Finset.sum_mul]
  have hcard : ∑ l : Fin n, ∑ l' : Fin n, (if l = l' then (0 : ℝ) else 1) =
      (n : ℝ) * ((n : ℝ) - 1) := by
    have := sum_sq_const_coupling (n := n) 1
    simpa using this
  rw [hcard]
  ring

theorem sum_spin_sq_exp_integral (n : ℕ) (β h q : ℝ) (hq : 0 ≤ q) :
    ∑ ε : Fin n → ℤˣ, ((∑ l, ((ε l : ℤ) : ℝ)) ^ 2 - (n : ℝ)) *
        Real.exp (h * ∑ l, ((ε l : ℤ) : ℝ) +
          β ^ 2 * (∑ l, ((ε l : ℤ) : ℝ)) ^ 2 * q / 2) =
      (n : ℝ) * ((n : ℝ) - 1) * (2 : ℝ) ^ n *
        ∫ z : ℝ, cosh (β * z * Real.sqrt q + h) ^ n *
          tanh (β * z * Real.sqrt q + h) ^ 2 ∂(gaussianReal 0 1) := by
  have hz (ε : Fin n → ℤˣ) (z : ℝ) :
      Real.exp ((β * z * Real.sqrt q + h) * ∑ l, ((ε l : ℤ) : ℝ)) =
        Real.exp (h * ∑ l, ((ε l : ℤ) : ℝ)) *
          Real.exp ((β * Real.sqrt q * ∑ l, ((ε l : ℤ) : ℝ)) * z) := by
    rw [← Real.exp_add]; congr 1; ring
  have hsq : (β * Real.sqrt q) ^ 2 = β ^ 2 * q := by
    rw [mul_pow, Real.sq_sqrt hq]
  have hterm (ε : Fin n → ℤˣ) :
      Real.exp (h * ∑ l, ((ε l : ℤ) : ℝ) +
        β ^ 2 * (∑ l, ((ε l : ℤ) : ℝ)) ^ 2 * q / 2) =
      ∫ z : ℝ, Real.exp ((β * z * Real.sqrt q + h) * ∑ l, ((ε l : ℤ) : ℝ))
        ∂(gaussianReal 0 1) := by
    simp_rw [hz ε]
    rw [integral_const_mul, integral_exp_mul_gaussianReal_zero_one, mul_pow, hsq,
      ← Real.exp_add]
    congr 1
    ring
  simp_rw [hterm, ← integral_const_mul]
  rw [← integral_finsetSum]
  · have heq (z : ℝ) : (∑ ε : Fin n → ℤˣ,
        ((∑ l, ((ε l : ℤ) : ℝ)) ^ 2 - (n : ℝ)) *
          Real.exp ((β * z * Real.sqrt q + h) * ∑ l, ((ε l : ℤ) : ℝ))) =
        (n : ℝ) * ((n : ℝ) - 1) * (2 : ℝ) ^ n *
          (cosh (β * z * Real.sqrt q + h) ^ n *
            tanh (β * z * Real.sqrt q + h) ^ 2) := by
      have := sum_spin_sq_sub_n_exp_eq n (Y := β * z * Real.sqrt q + h)
      rw [this]
      rw [mul_pow]
      ring
    simp_rw [heq]
  · intro ε _
    simp_rw [hz ε]
    exact ((integrable_exp_mul_gaussianReal _).const_mul _).const_mul _

end SpinGlasses
