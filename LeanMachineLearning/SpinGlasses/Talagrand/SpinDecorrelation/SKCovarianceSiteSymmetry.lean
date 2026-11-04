/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Gibbs.GibbsReplicaMarginal
public import LeanMachineLearning.SpinGlasses.Talagrand.CavityMethod.SKOverlapContraction

/-! # Site symmetry for disorder-averaged Gibbs covariance moments -/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Real Matrix
namespace SpinGlasses

/-- Disorder-averaged powers of a Gibbs covariance are invariant under a common
permutation of the two sites, for every nonnegative integer power. -/
theorem sk_covariance_pow_site_perm (N k : ℕ) (β h : ℝ) (pm : Equiv.Perm (Fin (N + 1)))
    (i j : Fin (N + 1)) :
    let E : (FinPairs (N + 1) → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g σ =>
      (Real.sqrt (N + 1))⁻¹ * β *
        (∑ p : FinPairs (N + 1), g p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) +
        h * ∑ i, (σ i : ℝ)
    ∫ g : FinPairs (N + 1) → ℝ,
      ((∫ σ : Fin (N + 1) → ℤˣ, (σ (pm i) : ℝ) * (σ (pm j) : ℝ)
          ∂(Measure.count.tilted (E g))) -
        (∫ σ : Fin (N + 1) → ℤˣ, (σ (pm i) : ℝ) ∂(Measure.count.tilted (E g))) *
          (∫ σ : Fin (N + 1) → ℤˣ, (σ (pm j) : ℝ) ∂(Measure.count.tilted (E g)))) ^ k
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) =
    ∫ g : FinPairs (N + 1) → ℝ,
      ((∫ σ : Fin (N + 1) → ℤˣ, (σ i : ℝ) * (σ j : ℝ) ∂(Measure.count.tilted (E g))) -
        (∫ σ : Fin (N + 1) → ℤˣ, (σ i : ℝ) ∂(Measure.count.tilted (E g))) *
          (∫ σ : Fin (N + 1) → ℤˣ, (σ j : ℝ) ∂(Measure.count.tilted (E g)))) ^ k
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) := by
  intro E
  simp_rw [cov_pow_eq_two_inv_pow_mul_integral]
  simp_rw [integral_const_mul]
  congr 1
  let Θ : (Fin (2 * k) → Fin (N + 1) → ℤˣ) → ℝ := fun ρ =>
    ∏ w : Fin k,
      ((ρ ⟨2 * w.val, by omega⟩ i : ℝ) - (ρ ⟨2 * w.val + 1, by omega⟩ i : ℝ)) *
      ((ρ ⟨2 * w.val, by omega⟩ j : ℝ) - (ρ ⟨2 * w.val + 1, by omega⟩ j : ℝ))
  exact sk_replica_site_perm N β h pm Θ

end SpinGlasses
