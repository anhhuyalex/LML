/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.Hanen.SKHanenTaylor
public import LeanMachineLearning.ForMathlib.Algebra.BigOperators.InvolutiveProduct

/-!
# Spin-difference estimates for products of full overlaps

Talagrand Corollary 1.11.7 for odd or even numbers of spin differences. Expanding the
last-spin corrections reduces the full-overlap estimate to the truncated-overlap estimate
with an additional spin monomial; repeated spin factors cancel by the generic involution API.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Real Matrix
namespace SpinGlasses

/-- Talagrand Corollary 1.11.7 for full overlaps, either parity of the number of spin
differences, and a centering within `L/(N+1)` of the fixed point. -/
theorem sk_eta_full_overlap_shift_bound (β₀ : ℝ) (hβ₀ : 4 * β₀ ^ 2 < 1)
    (n s m : ℕ) (L : ℝ) (hL : 0 ≤ L) :
    ∃ K : ℝ, 0 < K ∧ ∀ (β h q q' : ℝ),
      (∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 2 ∂gaussianReal 0 1 = q) →
      β ^ 2 ≤ β₀ ^ 2 → ∀ (N : ℕ) (pairMap : Fin s → Fin n × Fin n)
      (_ : ∀ u v : Fin s, u ≠ v →
        (pairMap u).1 ≠ (pairMap v).1 ∧ (pairMap u).1 ≠ (pairMap v).2 ∧
        (pairMap u).2 ≠ (pairMap v).1 ∧ (pairMap u).2 ≠ (pairMap v).2)
      (x y : Fin m → Fin n) (_ : ∀ j, x j ≠ y j)
      (_ : |q - q'| ≤ L / ((N : ℝ) + 1)),
      |∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin n → Fin (N + 1) → ℤˣ,
          (∏ w : Fin s, (((σ (pairMap w).1 (Fin.last N) : ℤˣ) : ℝ) -
            ((σ (pairMap w).2 (Fin.last N) : ℤˣ) : ℝ))) *
          ∏ j : Fin m, (((N + 1 : ℝ)⁻¹ *
            (fun i : Fin (N + 1) => (σ (x j) i : ℝ)) ⬝ᵥ
              (fun i : Fin (N + 1) => (σ (y j) i : ℝ))) - q')
          ∂(Measure.pi fun _ : Fin n => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
            (Real.sqrt (N + 1))⁻¹ * β *
              (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
              h * ∑ i : Fin (N + 1), (a i : ℝ))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)| ≤
      K / ((N : ℝ) + 1) ^ (((((s + 1) / 2 + m : ℕ) : ℝ)) / 2) := by
  let C : Finset (Fin m) → Finset (Fin m) := fun I => Finset.univ \ I
  choose K hK hbound using fun I : Finset (Fin m) =>
    sk_eta_trunc_overlap_spin_bound β₀ hβ₀ n s (2 * I.card) (C I).card L hL
  refine ⟨(∑ I : Finset (Fin m), K I) + 1, ?_, ?_⟩
  · have hsum : 0 ≤ ∑ I : Finset (Fin m), K I :=
      Finset.sum_nonneg fun I _ => (hK I).le
    linarith
  intro β h q q' hfix hβ N pairMap hdisj x y hxy hshift
  let t : ℝ := (N : ℝ) + 1
  have ht : 0 < t := by dsimp [t]; positivity
  have ht1 : 1 ≤ t := le_add_of_nonneg_left (Nat.cast_nonneg N)
  let ν : ((Fin n → Fin (N + 1) → ℤˣ) → ℝ) → ℝ := fun F =>
    ∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin n → Fin (N + 1) → ℤˣ, F σ
      ∂(Measure.pi fun _ : Fin n => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
        (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
          h * ∑ i : Fin (N + 1), (a i : ℝ))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)
  let η : (Fin n → Fin (N + 1) → ℤˣ) → ℝ := fun σ =>
    ∏ w : Fin s, ((σ (pairMap w).1 (Fin.last N) : ℝ) -
      (σ (pairMap w).2 (Fin.last N) : ℝ))
  let D : Fin m → (Fin n → Fin (N + 1) → ℤˣ) → ℝ := fun j σ =>
    (N + 1 : ℝ)⁻¹ * ((fun i : Fin N => (σ (x j) i.castSucc : ℝ)) ⬝ᵥ
      fun i : Fin N => (σ (y j) i.castSucc : ℝ)) - q'
  let B : Fin m → (Fin n → Fin (N + 1) → ℤˣ) → ℝ := fun j σ =>
    (σ (x j) (Fin.last N) : ℝ) * (σ (y j) (Fin.last N) : ℝ)
  let F : Finset (Fin m) → (Fin n → Fin (N + 1) → ℤˣ) → ℝ := fun I σ =>
    η σ * (∏ j ∈ I, B j σ) * ∏ j ∈ C I, D j σ
  have hterm (I : Finset (Fin m)) :
      t⁻¹ ^ I.card * |ν (F I)| ≤ K I / t ^ (((((s + 1) / 2 + m : ℕ) : ℝ)) / 2) := by
    obtain ⟨J, hJ, hprod⟩ := Finset.exists_pair_prod_eq_prod_of_mul_self_eq_one
      (G := ℝ) I (fun j => (x j, y j))
    let e : Fin (C I).card ≃ {j // j ∈ C I} := (C I).equivFin.symm
    have hp (σ : Fin n → Fin (N + 1) → ℤˣ) :
        (∏ j : Fin (C I).card, D (e j).val σ) = ∏ j ∈ C I, D j σ := by
      rw [← Finset.prod_coe_sort (C I)]
      exact Fintype.prod_equiv e _ _ (fun _ => rfl)
    have hsp (σ : Fin n → Fin (N + 1) → ℤˣ) :
        (∏ j ∈ I, B j σ) = ∏ j ∈ J, (σ j (Fin.last N) : ℝ) := by
      apply hprod (fun j => (σ j (Fin.last N) : ℝ))
      intro j
      simpa only [pow_two] using units_cast_sq (σ j (Fin.last N))
    have hc : ((Finset.univ : Finset (Fin s)).biUnion
        (fun v => {(pairMap v).1, (pairMap v).2}) ∩ J).card ≤ 2 * I.card :=
      (Finset.card_le_card Finset.inter_subset_right).trans hJ
    have key := hbound I β h q q' hfix hβ N pairMap hdisj J hc
      (fun j => x (e j).val) (fun j => y (e j).val) (fun j => hxy (e j).val) hshift
    have hk : |ν (F I)| ≤ K I /
        t ^ (((((s - 2 * I.card + 1) / 2 + (C I).card : ℕ) : ℝ)) / 2) := by
      convert key using 1
      congr 1
      apply congrArg ν
      funext σ
      dsimp only [F, η]
      rw [hsp, ← hp]
    have hcardC : (C I).card = m - I.card := by simp [C, Finset.card_sdiff]
    have hle : ((s + 1) / 2 + m : ℕ) ≤
        2 * I.card + ((s - 2 * I.card + 1) / 2 + (C I).card) := by
      have hI : I.card ≤ m := by simpa using Finset.card_le_card (Finset.subset_univ I)
      rw [hcardC]
      omega
    calc
      _ ≤ t⁻¹ ^ I.card * (K I /
          t ^ (((((s - 2 * I.card + 1) / 2 + (C I).card : ℕ) : ℝ)) / 2)) :=
        mul_le_mul_of_nonneg_left hk (by positivity)
      _ = K I / t ^ (((2 * I.card + ((s - 2 * I.card + 1) / 2 + (C I).card) : ℕ) : ℝ) / 2) := by
        rw [inv_pow, ← one_div, div_mul_div_comm, one_mul,
          ← Real.rpow_natCast, ← Real.rpow_add ht]
        congr 2
        push_cast
        ring
      _ ≤ _ := by
        apply div_le_div_of_nonneg_left (hK I).le (by positivity)
        apply Real.rpow_le_rpow_of_exponent_le ht1
        exact_mod_cast (div_le_div_of_nonneg_right (show
          (((s + 1) / 2 + m : ℕ) : ℝ) ≤
            ((2 * I.card + ((s - 2 * I.card + 1) / 2 + (C I).card) : ℕ) : ℝ) by
              exact_mod_cast hle) (by norm_num : (0 : ℝ) ≤ 2))
  have hexpand : (fun σ : Fin n → Fin (N + 1) → ℤˣ => η σ *
      ∏ j : Fin m, ((N + 1 : ℝ)⁻¹ *
        ((fun i : Fin (N + 1) => (σ (x j) i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ (y j) i : ℝ)) - q')) =
      fun σ => ∑ I : Finset (Fin m), t⁻¹ ^ I.card * F I σ := by
    funext σ
    have hd (j : Fin m) : (N + 1 : ℝ)⁻¹ *
        ((fun i : Fin (N + 1) => (σ (x j) i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ (y j) i : ℝ)) - q' = t⁻¹ * B j σ + D j σ := by
      dsimp [t, B, D]
      rw [sk_overlap_succ_eq_cavity]
      ring
    simp_rw [hd]
    rw [Fintype.prod_add, Finset.mul_sum]
    refine Finset.sum_congr rfl fun I _ => ?_
    dsimp only [F, C]
    rw [Finset.prod_mul_distrib]
    simp only [Finset.prod_const, Finset.compl_eq_univ_sdiff]
    ring
  change |ν _| ≤ _
  rw [hexpand, sk_replica_avg_finset_sum N n β h ν (fun _ => rfl)]
  calc
    _ ≤ ∑ I : Finset (Fin m), |t⁻¹ ^ I.card * ν (F I)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ I : Finset (Fin m), t⁻¹ ^ I.card * |ν (F I)| := by
      apply Finset.sum_congr rfl
      intro I _
      rw [abs_mul, abs_of_nonneg (by positivity)]
    _ ≤ ∑ I : Finset (Fin m), K I / t ^ (((((s + 1) / 2 + m : ℕ) : ℝ)) / 2) :=
      Finset.sum_le_sum fun I _ => hterm I
    _ ≤ _ := by
      rw [← Finset.sum_div]
      exact div_le_div_of_nonneg_right (by linarith) (by positivity)

end SpinGlasses
