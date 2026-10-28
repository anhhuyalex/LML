/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.SKCavityHigherOrderPair
public import LeanMachineLearning.ForMathlib.LinearAlgebra.FiniteProductBound

/-!
# Products of linear combinations in the cavity expansion

The extension of Lemma 1.10.2 following Eq. (1.300) is finite multilinearity. The coefficients
are fixed before the system size; the replica labels may vary with it. Each factor may use a
different finite summand type. Empty sums, empty products and signed coefficients are allowed.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Real Matrix

namespace SpinGlasses

/-- **Lemma 1.10.2 for products of finite linear combinations.** The coefficient loss is
independent of `N`. Only the monomial pair expansion is probabilistic; the extension uses
`LinearMap.abs_apply_prod_sum_le`. -/
theorem sk_cavity_pair_lincomb_expansion (β h q : ℝ) (hβ : 4 * β ^ 2 < 1)
    (hfix : ∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 2 ∂gaussianReal 0 1 = q)
    (qhat : ℝ)
    (hqhat : ∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 4 ∂gaussianReal 0 1 = qhat)
    (n k : ℕ) {x y : Fin n} (hxy : x ≠ y)
    {ι : Fin k → Type*} [∀ j, Fintype (ι j)] (c : ∀ j, ι j → ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (a b : ∀ j, ι j → Fin n), (∀ j i, a j i ≠ b j i) →
    let F : (Fin n → Fin N → ℤˣ) → ℝ := fun ρ => ∏ j : Fin k, ∑ i : ι j,
      c j i * ((N + 1 : ℝ)⁻¹ * ((fun v : Fin N => (ρ (a j i) v : ℝ)) ⬝ᵥ
        fun v : Fin N => (ρ (b j i) v : ℝ)) - q)
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
  obtain ⟨C, hC0, hC⟩ := sk_cavity_pair_prod_expansion β h q hβ hfix qhat hqhat n k hxy
  have hc : 0 ≤ ∏ j, ∑ i, |c j i| :=
    Finset.prod_nonneg fun j _ => Finset.sum_nonneg fun i _ => abs_nonneg _
  refine ⟨(∏ j, ∑ i, |c j i|) * C + 1, by positivity, ?_⟩
  intro N a b hab F E ν ν₂
  have hE (σ : Fin (N + 1) → ℤˣ) : Measurable (fun g => E g σ) := by
    dsimp [E]
    fun_prop
  have hadd {R : Type} [Fintype R] (f g : (R → Fin (N + 1) → ℤˣ) → ℝ) :
      (∫ w, ∫ σ, (f σ + g σ)
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E w))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) =
      (∫ w, ∫ σ, f σ ∂(Measure.pi fun _ : R => Measure.count.tilted (E w))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) +
      (∫ w, ∫ σ, g σ ∂(Measure.pi fun _ : R => Measure.count.tilted (E w))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) := by
    simp_rw [integral_add Integrable.of_finite Integrable.of_finite]
    exact integral_add
      (integrable_integral_pi_count_tilted_det (g := fun σ w => E w σ)
        (fun σ => (hE σ).aemeasurable) f)
      (integrable_integral_pi_count_tilted_det (g := fun σ w => E w σ)
        (fun σ => (hE σ).aemeasurable) g)
  let w : SKCavityReplicaPair n → ℝ := fun j => skCavityReplicaPairWeight n j *
    skCavityBCoef β q qhat (skCavityReplicaPairCoincidences x y j)
  let L : ((Fin n → Fin N → ℤˣ) → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun f => ν (fun σ => f (fun r i => σ r i.castSucc) *
          ((σ x (Fin.last N) : ℝ) * (σ y (Fin.last N) : ℝ) - q)) -
        ∑ j, w j * ν₂ (fun σ => f (fun r i => σ (some (some r)) i.castSucc) *
          ((N + 1 : ℝ)⁻¹ *
            ((fun i : Fin N => (σ (skCavityReplicaPairMap j).1 i.castSucc : ℝ)) ⬝ᵥ
              fun i : Fin N => (σ (skCavityReplicaPairMap j).2 i.castSucc : ℝ)) - q))
      map_add' := by
        intro f g
        dsimp only [ν, ν₂, Pi.add_apply]
        simp only [add_mul]
        simp only [hadd, mul_add, Finset.sum_add_distrib]
        ring
      map_smul' := by
        intro t f
        dsimp only [ν, ν₂, Pi.smul_apply]
        simp only [smul_eq_mul, RingHom.id_apply, mul_assoc, integral_const_mul]
        simp only [mul_sub, Finset.mul_sum]
        congr 1
        exact Finset.sum_congr rfl fun j _ => by ring }
  have hp (t : ∀ j, ι j) :
      |L (fun ρ => ∏ j : Fin k, ((N + 1 : ℝ)⁻¹ *
        ((fun i : Fin N => (ρ (a j (t j)) i : ℝ)) ⬝ᵥ
          fun i : Fin N => (ρ (b j (t j)) i : ℝ)) - q))| ≤
        C / ((N : ℝ) + 1) ^ (((k + 2 : ℕ) : ℝ) / 2) := by
    simpa only [L, LinearMap.coe_mk, AddHom.coe_mk, ν, ν₂, E, w, mul_assoc] using
      hC N (fun j => a j (t j))
      (fun j => b j (t j)) (fun j => hab j (t j))
  have ht := L.abs_apply_prod_sum_le c (fun j i ρ =>
    (N + 1 : ℝ)⁻¹ * ((fun v : Fin N => (ρ (a j i) v : ℝ)) ⬝ᵥ
      fun v : Fin N => (ρ (b j i) v : ℝ)) - q) hp
  simp only [← mul_assoc]
  change |L F| ≤ _
  calc
    _ ≤ (∏ j, ∑ i, |c j i|) * (C / ((N : ℝ) + 1) ^ (((k + 2 : ℕ) : ℝ) / 2)) := ht
    _ = ((∏ j, ∑ i, |c j i|) * C) /
        ((N : ℝ) + 1) ^ (((k + 2 : ℕ) : ℝ) / 2) := by ring
    _ ≤ _ := div_le_div_of_nonneg_right (by linarith) (by positivity)

end SpinGlasses
