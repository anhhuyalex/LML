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
    { toFun := fun f => ν (fun σ => W σ ^ 2 * f σ)
      map_add' := by
        intro f g
        simp only [Pi.add_apply, mul_add]
        exact hadd _ _
      map_smul' := by
        intro r f
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        simpa only [mul_left_comm (W _ ^ 2) r] using
          hsmul r (fun σ => W σ ^ 2 * f σ) }
  have hL : ∀ f g, (∀ σ, f σ ≤ g σ) → L f ≤ L g := fun f g hfg =>
    hmono _ _ fun σ => mul_le_mul_of_nonneg_left (hfg σ) (sq_nonneg _)
  let D : ∀ j, ι j → (Fin n → Fin (N + 1) → ℤˣ) → ℝ := fun j i σ =>
    (N + 1 : ℝ)⁻¹ * ((fun v : Fin N => (σ (a j i) v.castSucc : ℝ)) ⬝ᵥ
      fun v : Fin N => (σ (b j i) v.castSucc : ℝ)) - q
  have hp (t : ∀ j, ι j) : L (fun σ => (∏ j, D j (t j) σ) ^ 2) ≤
      K / ((N : ℝ) + 1) ^ k := by
    simpa only [L, LinearMap.coe_mk, AddHom.coe_mk, ν, D, mul_pow] using
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

end SpinGlasses
