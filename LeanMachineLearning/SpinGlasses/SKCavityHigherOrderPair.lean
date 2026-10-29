/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.SKCavityHigherOrder
public import LeanMachineLearning.SpinGlasses.SKCovarianceRows
public import LeanMachineLearning.SpinGlasses.SKTBasisAlgebra

/-!
# The higher-order pair expansion (Talagrand's Lemma 1.10.2)

The second-order cavity expansion evaluates the derivative by Lemma 1.8.2. Each old-spin
average in its signed replica sum is then replaced by the full average, with one additional
centered overlap factor. The constants precede the system size.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Real Matrix

namespace SpinGlasses

/-- **Lemma 1.10.2, Eq. (1.300).** For a product of `k` truncated centered overlaps,
the pair expansion has error `C / (N+1)^((k+2)/2)`. The right-hand side uses the full
SK measure with two additional replicas, not the old-spin measure. -/
theorem sk_cavity_pair_prod_expansion_uniform (β₀ : ℝ) (hβ₀ : 4 * β₀ ^ 2 < 1)
    (n k : ℕ) {x y : Fin n} (hxy : x ≠ y) :
    ∃ C : ℝ, 0 < C ∧ ∀ (β h q qhat : ℝ),
      (∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 2 ∂gaussianReal 0 1 = q) →
      (∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 4 ∂gaussianReal 0 1 = qhat) →
      β ^ 2 ≤ β₀ ^ 2 → ∀ (N : ℕ) (a b : Fin k → Fin n), (∀ j, a j ≠ b j) →
    let F : (Fin n → Fin N → ℤˣ) → ℝ := fun ρ => ∏ j : Fin k,
      ((N + 1 : ℝ)⁻¹ * ((fun i : Fin N => (ρ (a j) i : ℝ)) ⬝ᵥ
        fun i : Fin N => (ρ (b j) i : ℝ)) - q)
    let E : (FinPairs (N + 1) → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g σ =>
      (Real.sqrt (N + 1))⁻¹ * β *
        (∑ p : FinPairs (N + 1), g p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) +
        h * ∑ i : Fin (N + 1), (σ i : ℝ)
    let ν : ((Fin n → Fin (N + 1) → ℤˣ) → ℝ) → ℝ := fun f =>
      ∫ g, ∫ σ, f σ ∂(Measure.pi fun _ : Fin n => Measure.count.tilted (E g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)
    let ν₂ : ((Option (Option (Fin n)) → Fin (N + 1) → ℤˣ) → ℝ) → ℝ := fun f =>
      ∫ g, ∫ σ, f σ
        ∂(Measure.pi fun _ : Option (Option (Fin n)) => Measure.count.tilted (E g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)
    |ν (fun σ => F (fun r i => σ r i.castSucc) *
        ((σ x (Fin.last N) : ℝ) * (σ y (Fin.last N) : ℝ) - q)) -
      ∑ j : SKCavityReplicaPair n, skCavityReplicaPairWeight n j *
        (skCavityBCoef β q qhat (skCavityReplicaPairCoincidences x y j) *
          ν₂ (fun σ => F (fun r i => σ (some (some r)) i.castSucc) *
            ((N + 1 : ℝ)⁻¹ *
              ((fun i : Fin N => (σ (skCavityReplicaPairMap j).1 i.castSucc : ℝ)) ⬝ᵥ
                fun i : Fin N => (σ (skCavityReplicaPairMap j).2 i.castSucc : ℝ)) - q)))| ≤
      C / ((N : ℝ) + 1) ^ (((k + 2 : ℕ) : ℝ) / 2) := by
  obtain ⟨C₀, hC₀0, hC₀⟩ := sk_cavity_prod_expansion_uniform β₀ hβ₀ n k 2
  obtain ⟨C₁, hC₁0, hC₁⟩ :=
    sk_cavity_prod_old_spin_compare_uniform β₀ hβ₀ (n + 2) (k + 1)
  let D : ℝ := β₀ ^ 2 * ∑ j : SKCavityReplicaPair n, |skCavityReplicaPairWeight n j|
  have hD : 0 ≤ D := by positivity
  refine ⟨C₀ + D * C₁, by positivity, ?_⟩
  intro β h q qhat hfix hqhat hb N a b hab F E ν ν₂
  let c : SKCavityReplicaPair n → ℝ := fun j => skCavityReplicaPairWeight n j *
    skCavityBCoef β q qhat (skCavityReplicaPairCoincidences x y j)
  have hc : (∑ j, |c j|) ≤ D := by
    have hq := fixedPoint_mem_Icc hfix
    have hh : qhat ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨by rw [← hqhat]; exact integral_nonneg fun _ => by positivity,
        (qhat_le_of_fixedPoint β q h qhat hfix hqhat).trans hq.2⟩
    calc
      _ ≤ ∑ j : SKCavityReplicaPair n, |skCavityReplicaPairWeight n j| * β₀ ^ 2 := by
        apply Finset.sum_le_sum
        intro j _
        dsimp only [c, skCavityBCoef]
        rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg β)]
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        exact (mul_le_mul_of_nonneg_left
          (abs_skCavityBUnscaled_le hq hh _) (sq_nonneg β)).trans
          (by simpa only [mul_one] using hb)
      _ = D := by rw [← Finset.sum_mul]; exact mul_comm _ _
  let E₀ : (FinPairs N → ℝ) → (Fin N → ℤˣ) → ℝ := fun g σ =>
    (Real.sqrt (N + 1))⁻¹ * β *
      (∑ p : FinPairs N, g p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) +
      h * ∑ i : Fin N, (σ i : ℝ)
  let O : ((Option (Option (Fin n)) → Fin N → ℤˣ) → ℝ) → ℝ := fun f =>
    ∫ g, ∫ σ, f σ
      ∂(Measure.pi fun _ : Option (Option (Fin n)) => Measure.count.tilted (E₀ g))
      ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)
  let G : SKCavityReplicaPair n → (Option (Option (Fin n)) → Fin N → ℤˣ) → ℝ :=
    fun j ρ => F (fun r => ρ (some (some r))) * ((N + 1 : ℝ)⁻¹ *
      ((fun i : Fin N => (ρ (skCavityReplicaPairMap j).1 i : ℝ)) ⬝ᵥ
        fun i : Fin N => (ρ (skCavityReplicaPairMap j).2 i : ℝ)) - q)
  let V : SKCavityReplicaPair n → ℝ := fun j => ν₂ (fun σ => G j (fun r i => σ r i.castSucc))
  let W : (Fin n → Fin (N + 1) → ℤˣ) → ℝ := fun σ =>
    (σ x (Fin.last N) : ℝ) * (σ y (Fin.last N) : ℝ) - q
  have ht := (hC₀ β h q hfix hb N a b hab W (fun σ =>
    abs_units_cast_mul_sub_le_two _ _ (fixedPoint_mem_Icc hfix))).2
  have hobs (σ : Fin n → Fin (N + 1) → ℤˣ) :
      W σ * (∏ j : Fin k, ((N + 1 : ℝ)⁻¹ *
        ((fun i : Fin N => (σ (a j) i.castSucc : ℝ)) ⬝ᵥ
          fun i : Fin N => (σ (b j) i.castSucc : ℝ)) - q)) =
      F (fun r i => σ r i.castSucc) * W σ := mul_comm _ _
  simp only [hobs] at ht
  simp only [W] at ht
  have hfixz : ∫ z : ℝ, Real.tanh (β * z * Real.sqrt q + h) ^ 2 ∂gaussianReal 0 1 = q := by
    rw [integral_tanh_pow_mul_z_sqrt_eq, hfix]
  have hz := sk_cavity_decoupled_pair_zero N β q h hfixz hxy F
  have hl := sk_cavity_deriv_zero_pair N n β q h hfix qhat hqhat hxy F
  simp only [] at ht hz hl
  rw [hz, hl, sub_zero] at ht
  have ht' : |ν (fun σ => F (fun r i => σ r i.castSucc) * W σ) -
      ∑ j, c j * O (G j)| ≤ C₀ / ((N : ℝ) + 1) ^ (((k + 2 : ℕ) : ℝ) / 2) := by
    simpa only [ν, E, W, c, O, G, E₀, mul_assoc] using ht
  have hv (j : SKCavityReplicaPair n) : |V j - O (G j)| ≤
      C₁ / ((N : ℝ) + 1) ^ (((k + 2 : ℕ) : ℝ) / 2) := by
    let e : Option (Option (Fin n)) ≃ Fin (n + 2) :=
      (Equiv.optionCongr (finSuccEquiv n).symm).trans (finSuccEquiv (n + 1)).symm
    let aa : Fin (k + 1) → Fin (n + 2) :=
      Fin.snoc (fun v => e (some (some (a v)))) (e (skCavityReplicaPairMap j).1)
    let bb : Fin (k + 1) → Fin (n + 2) :=
      Fin.snoc (fun v => e (some (some (b v)))) (e (skCavityReplicaPairMap j).2)
    have hab' (v : Fin (k + 1)) : aa v ≠ bb v := by
      refine Fin.lastCases ?_ (fun i => ?_) v
      · simp only [aa, bb, Fin.snoc_last]
        exact e.injective.ne (skCavityReplicaPair_ne j)
      · simp only [aa, bb, Fin.snoc_castSucc]
        exact e.injective.ne (by simpa only [ne_eq, Option.some.injEq] using hab i)
    have hh := hC₁ β h q hfix hb N aa bb hab'
    have hf (g : FinPairs (N + 1) → ℝ) := integral_pi_count_tilted_reindex e (E g)
      (fun σ => G j (fun r i => σ r i.castSucc))
    have ho (g : FinPairs N → ℝ) := integral_pi_count_tilted_reindex e (E₀ g) (G j)
    change |(∫ g, ∫ σ, G j (fun r i => σ r i.castSucc)
        ∂(Measure.pi fun _ : Option (Option (Fin n)) => Measure.count.tilted (E g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) - O (G j)| ≤ _
    simp_rw [hf]
    dsimp only [O]
    simp_rw [ho]
    simpa only [Fin.prod_univ_castSucc, aa, bb, Fin.snoc_castSucc, Fin.snoc_last,
      G, F, E, E₀, Nat.add_assoc] using hh
  have hs := Weights.abs_weighted_sum_le c (fun j => O (G j) - V j)
    (fun j => by rw [abs_sub_comm]; exact hv j)
  have he : (∑ j, c j * O (G j)) - ∑ j, c j * V j =
      ∑ j, c j * (O (G j) - V j) := by simp only [mul_sub, Finset.sum_sub_distrib]
  change |ν (fun σ => F (fun r i => σ r i.castSucc) * W σ) -
    ∑ j, skCavityReplicaPairWeight n j *
      (skCavityBCoef β q qhat (skCavityReplicaPairCoincidences x y j) * V j)| ≤ _
  simp only [← mul_assoc]
  change |ν (fun σ => F (fun r i => σ r i.castSucc) * W σ) - ∑ j, c j * V j| ≤ _
  calc
    _ ≤ |ν (fun σ => F (fun r i => σ r i.castSucc) * W σ) - ∑ j, c j * O (G j)| +
        |(∑ j, c j * O (G j)) - ∑ j, c j * V j| := abs_sub_le _ _ _
    _ ≤ C₀ / ((N : ℝ) + 1) ^ (((k + 2 : ℕ) : ℝ) / 2) +
        (∑ j, |c j|) * (C₁ / ((N : ℝ) + 1) ^ (((k + 2 : ℕ) : ℝ) / 2)) :=
      add_le_add ht' (by rw [he]; exact hs)
    _ ≤ C₀ / ((N : ℝ) + 1) ^ (((k + 2 : ℕ) : ℝ) / 2) +
        D * (C₁ / ((N : ℝ) + 1) ^ (((k + 2 : ℕ) : ℝ) / 2)) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_right hc
        (by positivity : 0 ≤ C₁ / ((N : ℝ) + 1) ^ (((k + 2 : ℕ) : ℝ) / 2)))
    _ = _ := by ring

/-- **Lemma 1.10.2 with fixed model parameters.** This is the corresponding
specialization of the uniform monomial expansion. -/
theorem sk_cavity_pair_prod_expansion (β h q : ℝ) (hβ : 4 * β ^ 2 < 1)
    (hfix : ∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 2 ∂gaussianReal 0 1 = q)
    (qhat : ℝ)
    (hqhat : ∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 4 ∂gaussianReal 0 1 = qhat)
    (n k : ℕ) {x y : Fin n} (hxy : x ≠ y) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (a b : Fin k → Fin n), (∀ j, a j ≠ b j) →
    let F : (Fin n → Fin N → ℤˣ) → ℝ := fun ρ => ∏ j : Fin k,
      ((N + 1 : ℝ)⁻¹ * ((fun i : Fin N => (ρ (a j) i : ℝ)) ⬝ᵥ
        fun i : Fin N => (ρ (b j) i : ℝ)) - q)
    let E : (FinPairs (N + 1) → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g σ =>
      (Real.sqrt (N + 1))⁻¹ * β *
        (∑ p : FinPairs (N + 1), g p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) +
        h * ∑ i : Fin (N + 1), (σ i : ℝ)
    let ν : ((Fin n → Fin (N + 1) → ℤˣ) → ℝ) → ℝ := fun f =>
      ∫ g, ∫ σ, f σ ∂(Measure.pi fun _ : Fin n => Measure.count.tilted (E g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)
    let ν₂ : ((Option (Option (Fin n)) → Fin (N + 1) → ℤˣ) → ℝ) → ℝ := fun f =>
      ∫ g, ∫ σ, f σ
        ∂(Measure.pi fun _ : Option (Option (Fin n)) => Measure.count.tilted (E g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)
    |ν (fun σ => F (fun r i => σ r i.castSucc) *
        ((σ x (Fin.last N) : ℝ) * (σ y (Fin.last N) : ℝ) - q)) -
      ∑ j : SKCavityReplicaPair n, skCavityReplicaPairWeight n j *
        (skCavityBCoef β q qhat (skCavityReplicaPairCoincidences x y j) *
          ν₂ (fun σ => F (fun r i => σ (some (some r)) i.castSucc) *
            ((N + 1 : ℝ)⁻¹ *
              ((fun i : Fin N => (σ (skCavityReplicaPairMap j).1 i.castSucc : ℝ)) ⬝ᵥ
                fun i : Fin N => (σ (skCavityReplicaPairMap j).2 i.castSucc : ℝ)) - q)))| ≤
      C / ((N : ℝ) + 1) ^ (((k + 2 : ℕ) : ℝ) / 2) := by
  obtain ⟨C, hC0, hC⟩ := sk_cavity_pair_prod_expansion_uniform β hβ n k hxy
  exact ⟨C, hC0, hC β h q qhat hfix hqhat le_rfl⟩

end SpinGlasses
