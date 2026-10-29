/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.SKOverlapCLTCovarianceForm
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Finset.Sigma

/-!
# The overlap moment theorem with multiplicities

Talagrand (1.290) groups equal pair, single and global factors into powers. We obtain
this presentation by enumerating each factor with its multiplicity and applying the
already proved mixed-moment estimate. Pair exponents vanish outside the ordered pairs.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Real

namespace SpinGlasses

/-- **Theorem 1.10.1 (1.290), multi-index form.** The inverse-size factor is included
in each of the variances `A2`, `B2`, `C2`. Pair multiplicities are zero off `x < y`. -/
theorem sk_T_multiindex_gaussian_moment_uniform (β₀ : ℝ) (hβ₀ : 4 * β₀ ^ 2 < 1)
    {R : Type*} [Fintype R] [LinearOrder R] [Nonempty R]
    (kP : R × R → ℕ) (kS : R → ℕ) (kG : ℕ)
    (hord : ∀ p, 0 < kP p → p.1 < p.2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (β h q : ℝ),
      (∫ t : ℝ, Real.tanh (β * Real.sqrt q * t + h) ^ 2 ∂gaussianReal 0 1 = q) →
      β ^ 2 ≤ β₀ ^ 2 → ∀ N : ℕ,
    let E : (FinPairs (N + 1) → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g σ =>
      (Real.sqrt (N + 1))⁻¹ * β *
        (∑ p : FinPairs (N + 1), g p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) +
      h * ∑ i : Fin (N + 1), (σ i : ℝ)
    let bmean : (FinPairs (N + 1) → ℝ) → Fin (N + 1) → ℝ := fun g i =>
      ∫ σ : Fin (N + 1) → ℤˣ, (σ i : ℝ) ∂(Measure.count.tilted (E g))
    let TP := fun (p : R × R) g (ρ : R → Fin (N + 1) → ℤˣ) =>
      (N + 1 : ℝ)⁻¹ * ∑ i, ((ρ p.1 i : ℝ) - bmean g i) *
        ((ρ p.2 i : ℝ) - bmean g i)
    let TS := fun (r : R) g (ρ : R → Fin (N + 1) → ℤˣ) =>
      (N + 1 : ℝ)⁻¹ * ∑ i, ((ρ r i : ℝ) - bmean g i) * bmean g i
    let TG := fun g => (N + 1 : ℝ)⁻¹ * ∑ i, bmean g i * bmean g i - q
    let νT : ℝ := ∫ g, ∫ ρ : R → Fin (N + 1) → ℤˣ,
      (∏ p, TP p g ρ ^ kP p) * (∏ r, TS r g ρ ^ kS r) * TG g ^ kG
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)
    let qh : ℝ := ∫ t : ℝ, Real.tanh (β * t * Real.sqrt q + h) ^ 4 ∂gaussianReal 0 1
    let α : ℝ := qh - 2 * q + 1
    let D : ℝ := 1 - β ^ 2 * (1 - 4 * q + 3 * qh)
    let A2 : ℝ := α / ((N + 1 : ℝ) * (1 - β ^ 2 * α))
    let B2 : ℝ := (q - qh) / ((N + 1 : ℝ) * (1 - β ^ 2 * α) * D)
    let C2 : ℝ := ((qh - q ^ 2) / (N + 1 : ℝ) + β ^ 2 * (qh - q ^ 2) * A2 +
      2 * β ^ 2 * (2 * q + q ^ 2 - 3 * qh) * B2) / D
    |νT - (∏ p, ∫ x : ℝ, (Real.sqrt A2 * x) ^ kP p ∂gaussianReal 0 1) *
      (∏ r, ∫ x : ℝ, (Real.sqrt B2 * x) ^ kS r ∂gaussianReal 0 1) *
      (∫ x : ℝ, (Real.sqrt C2 * x) ^ kG ∂gaussianReal 0 1)| ≤
        C / ((N : ℝ) + 1) ^ ((((∑ p, kP p) + (∑ r, kS r) + kG + 1 : ℕ) : ℝ) / 2) := by
  obtain ⟨r₀⟩ := ‹Nonempty R›
  let K := (R × R) ⊕ (R ⊕ Unit)
  let m : K → ℕ := Sum.elim kP (Sum.elim kS (fun _ => kG))
  let J := Σ κ : K, Fin (m κ)
  let L : J → Bool := fun j => Sum.elim (fun _ => true)
    (Sum.elim (fun _ => true) (fun _ => false)) j.1
  let S : J → Bool := fun j => Sum.elim (fun _ => true) (fun _ => false) j.1
  let a : J → R := fun j => Sum.elim Prod.fst (Sum.elim id (fun _ => r₀)) j.1
  let b : J → R := fun j => Sum.elim Prod.snd (fun _ => r₀) j.1
  have hnorm : ∀ j, ¬(L j = true ∧ S j = true) → S j = false := by
    rintro ⟨p | r | u, n⟩ <;> simp [L, S]
  have ho : ∀ j, L j = true → S j = true → a j < b j := by
    rintro ⟨p | r | u, n⟩
    · intro _ _
      exact hord p (Nat.zero_lt_of_lt n.isLt)
    · simp [S]
    · simp [S]
  have hcount (P : K → Prop) [DecidablePred P] :
      ((univ : Finset J).filter fun j => P j.1).card =
        ∑ κ, if P κ then m κ else 0 := by
    rw [← Finset.univ_sigma_univ, Finset.filter_sigma, Finset.card_sigma]
    apply Finset.sum_congr rfl
    intro κ _
    by_cases hκ : P κ <;> simp [hκ]
  have hcP (p : R × R) :
      ((univ : Finset J).filter fun j =>
        (L j = true ∧ S j = true) ∧ (a j, b j) = p).card = kP p := by
    have hf : ((univ : Finset J).filter fun j =>
        (L j = true ∧ S j = true) ∧ (a j, b j) = p) =
        univ.filter (fun j => j.1 = Sum.inl p) := by
      apply Finset.filter_congr
      rintro ⟨p' | r | u, n⟩ _ <;> simp [L, S, a, b]
    rw [hf, hcount (fun κ => κ = Sum.inl p)]
    simp [K, m]
  have hcS (r : R) :
      ((univ : Finset J).filter fun j =>
        (L j = true ∧ S j = false) ∧ a j = r).card = kS r := by
    have hf : ((univ : Finset J).filter fun j =>
        (L j = true ∧ S j = false) ∧ a j = r) =
        univ.filter (fun j => j.1 = Sum.inr (Sum.inl r)) := by
      apply Finset.filter_congr
      rintro ⟨p | r' | u, n⟩ _ <;> simp [L, S, a]
    rw [hf, hcount (fun κ => κ = Sum.inr (Sum.inl r))]
    simp [K, m]
  have hcG : ((univ : Finset J).filter fun j => L j = false ∧ S j = false).card = kG := by
    have hf : ((univ : Finset J).filter fun j => L j = false ∧ S j = false) =
        univ.filter (fun j => j.1 = Sum.inr (Sum.inr ())) := by
      apply Finset.filter_congr
      rintro ⟨p | r | u, n⟩ _ <;> simp [L, S]
    rw [hf, hcount (fun κ => κ = Sum.inr (Sum.inr ()))]
    simp [K, m]
  have hcard : (univ : Finset J).card = (∑ p, kP p) + (∑ r, kS r) + kG := by
    simp [J, K, m, Fintype.card_sigma, Fintype.sum_sum_type, add_assoc]
  obtain ⟨C, hC0, hC⟩ := sk_T_mixed_gaussian_moment_covariance_uniform
    β₀ hβ₀ L S hnorm a b ho univ
  refine ⟨C, hC0, fun β h q hfix hb N => ?_⟩
  intro E bmean TP TS TG νT qh α D A2 B2 C2
  have h := hC β h q hfix hb N
  simp_rw [hcP, hcS, hcG] at h
  rw [hcard] at h
  have hprod (g : FinPairs (N + 1) → ℝ) (ρ : R → Fin (N + 1) → ℤˣ) :
      (∏ j : J, (((N + 1 : ℝ)⁻¹ * ∑ i,
        (if L j then (ρ (a j) i : ℝ) - bmean g i else bmean g i) *
        (if S j then (ρ (b j) i : ℝ) - bmean g i else bmean g i)) -
          (if L j || S j then 0 else q))) =
        (∏ p, TP p g ρ ^ kP p) * (∏ r, TS r g ρ ^ kS r) * TG g ^ kG := by
    let F : K → ℝ := Sum.elim (fun p => TP p g ρ)
      (Sum.elim (fun r => TS r g ρ) (fun _ => TG g))
    have hpow : (∏ j : J, F j.1) = ∏ κ, F κ ^ m κ := by
      rw [Fintype.prod_sigma]
      simp
    have hobs (j : J) :
        (((N + 1 : ℝ)⁻¹ * ∑ i,
          (if L j then (ρ (a j) i : ℝ) - bmean g i else bmean g i) *
          (if S j then (ρ (b j) i : ℝ) - bmean g i else bmean g i)) -
            (if L j || S j then 0 else q)) = F j.1 := by
      rcases j with ⟨p | r | u, n⟩ <;> simp [F, L, S, a, b, TP, TS, TG]
    simp_rw [hobs]
    rw [hpow, Fintype.prod_sum_type, Fintype.prod_sum_type]
    simp [F, m, mul_assoc]
  have hν : (∫ g, ∫ ρ : R → Fin (N + 1) → ℤˣ,
      ∏ j : J, (((N + 1 : ℝ)⁻¹ * ∑ i,
        (if L j then (ρ (a j) i : ℝ) - bmean g i else bmean g i) *
        (if S j then (ρ (b j) i : ℝ) - bmean g i else bmean g i)) -
          (if L j || S j then 0 else q))
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) = νT := by
    simp_rw [hprod]
    rfl
  rw [hν] at h
  exact h

end SpinGlasses
