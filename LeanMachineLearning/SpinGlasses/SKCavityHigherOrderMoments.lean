/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.SKCavityHigherOrder
public import LeanMachineLearning.ForMathlib.LinearAlgebra.FiniteProductBound

/-!
# Moment and Taylor bounds for the full higher-order product class

Talagrand's functions of order `k` allow linear combinations in each overlap factor and
an arbitrary bounded factor. The coefficient families are fixed before the number of sites.
The moment bound is finite multilinearity of a positive linear functional; the Taylor
estimate reuses the observable-general analytic bound, without repeating its proof.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Real Matrix

namespace SpinGlasses

/-- **Eq. (1.297) for products of linear combinations, squared form.** The bounded factor
may depend on every spin. The coefficient loss is its total absolute mass squared. -/
theorem sk_cavity_lincomb_sq_le (β₀ : ℝ) (hβ₀ : 4 * β₀ ^ 2 < 1) (k : ℕ) (M : ℝ)
    {ι : Fin k → Type*} [∀ j, Fintype (ι j)] (c : ∀ j, ι j → ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (β h q : ℝ),
      (∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 2 ∂gaussianReal 0 1 = q) →
      β ^ 2 ≤ β₀ ^ 2 → ∀ (N n : ℕ) (a b : ∀ j, ι j → Fin n),
      (∀ j i, a j i ≠ b j i) → ∀ W : (Fin n → Fin (N + 1) → ℤˣ) → ℝ,
      (∀ σ, |W σ| ≤ M) →
      ∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin n → Fin (N + 1) → ℤˣ,
          (W σ * ∏ j : Fin k, ∑ i : ι j, c j i * ((N + 1 : ℝ)⁻¹ *
            ((fun v : Fin N => (σ (a j i) v.castSucc : ℝ)) ⬝ᵥ
              fun v : Fin N => (σ (b j i) v.castSucc : ℝ)) - q)) ^ 2
          ∂(Measure.pi fun _ : Fin n => Measure.count.tilted fun s : Fin (N + 1) → ℤˣ =>
            (Real.sqrt (N + 1))⁻¹ * β *
              (∑ p : FinPairs (N + 1), g p * (s p.val.1 : ℝ) * (s p.val.2 : ℝ)) +
              h * ∑ v : Fin (N + 1), (s v : ℝ))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) ≤
        K / ((N : ℝ) + 1) ^ k := by
  obtain ⟨K, hK0, hK⟩ := sk_cavity_prod_sq_le β₀ hβ₀ k M
  refine ⟨(∏ j, ∑ i, |c j i|) ^ 2 * K + 1, by positivity, ?_⟩
  intro β h q hfix hb N n a b hab W hW
  let ν : ((Fin n → Fin (N + 1) → ℤˣ) → ℝ) → ℝ := fun f =>
    ∫ g : FinPairs (N + 1) → ℝ, ∫ σ, f σ
      ∂(Measure.pi fun _ : Fin n => Measure.count.tilted fun s : Fin (N + 1) → ℤˣ =>
        (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs (N + 1), g p * (s p.val.1 : ℝ) * (s p.val.2 : ℝ)) +
          h * ∑ v : Fin (N + 1), (s v : ℝ))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)
  obtain ⟨hadd, hsmul, hmono, -⟩ := sk_replica_avg_calculus N n β h ν (fun _ => rfl)
  let L : ((Fin n → Fin (N + 1) → ℤˣ) → ℝ) →ₗ[ℝ] ℝ :=
    ({ toFun := ν, map_add' := hadd, map_smul' := hsmul } :
      ((Fin n → Fin (N + 1) → ℤˣ) → ℝ) →ₗ[ℝ] ℝ) ∘ₗ LinearMap.mulLeft ℝ fun σ => W σ ^ 2
  have hL : ∀ f g, (∀ σ, f σ ≤ g σ) → L f ≤ L g := fun f g hfg =>
    hmono _ _ fun σ => mul_le_mul_of_nonneg_left (hfg σ) (sq_nonneg _)
  let D : ∀ j, ι j → (Fin n → Fin (N + 1) → ℤˣ) → ℝ := fun j i σ =>
    (N + 1 : ℝ)⁻¹ * ((fun v : Fin N => (σ (a j i) v.castSucc : ℝ)) ⬝ᵥ
      fun v : Fin N => (σ (b j i) v.castSucc : ℝ)) - q
  have hp (t : ∀ j, ι j) : L (fun σ => (∏ j, D j (t j) σ) ^ 2) ≤
      K / ((N : ℝ) + 1) ^ k := by
    change ν (fun σ => W σ ^ 2 * (∏ j, D j (t j) σ) ^ 2) ≤ _
    simpa only [ν, D, mul_pow] using
      hK β h q hfix hb N n (fun j => a j (t j)) (fun j => b j (t j))
        (fun j => hab j (t j)) W hW
  have ht := L.apply_sq_prod_sum_le hL c D hp
  change ν (fun σ => (W σ * ∏ j, ∑ i, c j i * D j i σ) ^ 2) ≤ _
  simp only [mul_pow]
  calc
    _ = L (fun σ => (∏ j, ∑ i, c j i * D j i σ) ^ 2) := rfl
    _ ≤ (∏ j, ∑ i, |c j i|) ^ 2 * (K / ((N : ℝ) + 1) ^ k) := ht
    _ = ((∏ j, ∑ i, |c j i|) ^ 2 * K) / ((N : ℝ) + 1) ^ k := by ring
    _ ≤ _ := div_le_div_of_nonneg_right (by linarith) (by positivity)

/-- **Eqs. (1.298)--(1.299) for the full finite-linear-combination product class.** The bounded
factor may depend on every spin, including the last. The same positive constant works for
both errors and is chosen before the system size, replica pairs and bounded factor.
The derivative is the actual decoupled cavity derivative with its signed replica sum. -/
theorem sk_cavity_lincomb_expansion (β h q : ℝ) (hβ : 4 * β ^ 2 < 1)
    (hfix : ∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 2 ∂gaussianReal 0 1 = q)
    (n k : ℕ) (M : ℝ)
    {ι : Fin k → Type*} [∀ j, Fintype (ι j)] (c : ∀ j, ι j → ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (a b : ∀ j, ι j → Fin n),
      (∀ j i, a j i ≠ b j i) →
    ∀ W : (Fin n → Fin (N + 1) → ℤˣ) → ℝ, (∀ σ, |W σ| ≤ M) →
    let B : (FinPairs N → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g' a =>
      (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs N,
            g' p * (a p.val.1.castSucc : ℝ) * (a p.val.2.castSucc : ℝ)) +
        h * ∑ i : Fin (N + 1), (a i : ℝ)
    let E : ℝ → (FinPairs N → ℝ) → ((Fin N → ℝ) × ℝ) →
        (Fin (N + 1) → ℤˣ) → ℝ := fun s g' ω a =>
      Real.cos s * ((Real.sqrt (N + 1))⁻¹ * β *
        (a (Fin.last N) : ℝ) * ∑ i : Fin N, ω.1 i * (a i.castSucc : ℝ)) +
      Real.sin s * (β * (a (Fin.last N) : ℝ) * ω.2 * Real.sqrt q) + B g' a
    let Esk : (FinPairs (N + 1) → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g a =>
      (Real.sqrt (N + 1))⁻¹ * β *
        (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
      h * ∑ i : Fin (N + 1), (a i : ℝ)
    let J : (Fin (N + 1) → ℤˣ) → (Fin (N + 1) → ℤˣ) → ℝ := fun a b =>
      β ^ 2 * (a (Fin.last N) : ℝ) * (b (Fin.last N) : ℝ) *
        ((N + 1 : ℝ)⁻¹ *
          ((fun i : Fin N => (a i.castSucc : ℝ)) ⬝ᵥ fun i : Fin N => (b i.castSucc : ℝ)) - q)
    let f : (Fin n → Fin (N + 1) → ℤˣ) → ℝ := fun σ =>
      W σ * ∏ j : Fin k, ∑ i : ι j, c j i * ((N + 1 : ℝ)⁻¹ *
        ((fun v : Fin N => (σ (a j i) v.castSucc : ℝ)) ⬝ᵥ
          fun v : Fin N => (σ (b j i) v.castSucc : ℝ)) - q)
    |(∫ g, ∫ σ : Fin n → Fin (N + 1) → ℤˣ, f σ
        ∂(Measure.pi fun _ : Fin n => Measure.count.tilted (Esk g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) -
      (∫ g', ∫ ω : (Fin N → ℝ) × ℝ, ∫ σ : Fin n → Fin (N + 1) → ℤˣ, f σ
        ∂(Measure.pi fun _ : Fin n => Measure.count.tilted (E (π / 2) g' ω))
        ∂((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))
        ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1))| ≤
      C / ((N : ℝ) + 1) ^ (((k + 1 : ℕ) : ℝ) / 2) ∧
    |(∫ g, ∫ σ : Fin n → Fin (N + 1) → ℤˣ, f σ
        ∂(Measure.pi fun _ : Fin n => Measure.count.tilted (Esk g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) -
      (∫ g', ∫ ω : (Fin N → ℝ) × ℝ, ∫ σ : Fin n → Fin (N + 1) → ℤˣ, f σ
        ∂(Measure.pi fun _ : Fin n => Measure.count.tilted (E (π / 2) g' ω))
        ∂((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))
        ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)) -
      (∫ g', ∫ ω : (Fin N → ℝ) × ℝ,
        ∫ τ : Option (Option (Fin n)) → Fin (N + 1) → ℤˣ,
          f (fun r => τ (some (some r))) *
            ((∑ p : Fin n × Fin n with p.1 < p.2,
                J (τ (some (some p.1))) (τ (some (some p.2)))) -
              (n : ℝ) * ∑ r : Fin n, J (τ (some (some r))) (τ (some none)) +
              (n : ℝ) * ((n : ℝ) + 1) / 2 * J (τ (some none)) (τ none))
        ∂(Measure.pi fun _ : Option (Option (Fin n)) => Measure.count.tilted
          (E (π / 2) g' ω))
        ∂((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))
        ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1))| ≤
      C / ((N : ℝ) + 1) ^ (((k + 2 : ℕ) : ℝ) / 2) := by
  obtain ⟨H, hH0, hH⟩ := sk_cavity_lincomb_sq_le β hβ k M c
  obtain ⟨C, hC0, hC⟩ := sk_cavity_expansion_of_sq_le β h q hβ hfix n k H hH0.le
  refine ⟨C, hC0, ?_⟩
  intro N a b hab W hW B E Esk J f
  exact hC N f (hH β h q hfix le_rfl N n a b hab W hW)

end SpinGlasses
