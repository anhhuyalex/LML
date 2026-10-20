/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.SKCavityInterpolation

/-!
# Truncated overlaps for the SK cavity

The overlap of an enlarged system splits exactly into the overlap of its first
`N` coordinates (with the *same* `N+1` normalization) and the contribution of
its last spin. This is Talagrand's equation (1.149).
-/

@[expose] public section

open Finset
open scoped BigOperators

namespace SpinGlasses

/-- The full overlap is the truncated overlap plus the last-spin contribution.
Both overlaps use the full system size `N+1` as their normalization. -/
theorem sk_overlap_succ_eq_cavity (N : ℕ)
    (σ τ : Fin (N + 1) → ℤˣ) :
    ((N + 1 : ℝ)⁻¹ *
      ((fun i : Fin (N + 1) => (σ i : ℝ)) ⬝ᵥ
        fun i : Fin (N + 1) => (τ i : ℝ))) =
      (N + 1 : ℝ)⁻¹ *
        ((fun i : Fin N => (σ i.castSucc : ℝ)) ⬝ᵥ
          fun i : Fin N => (τ i.castSucc : ℝ)) +
      (N + 1 : ℝ)⁻¹ * (σ (Fin.last N) : ℝ) * (τ (Fin.last N) : ℝ) := by
  simp only [dotProduct, Fin.sum_univ_castSucc]
  ring

/-- The truncated self-overlap is `N/(N+1)`, not one. In the replica
interpolation this common diagonal value cancels between the first `n`
replicas and the extra replica. -/
theorem sk_cavity_self_overlap (N : ℕ) (σ : Fin (N + 1) → ℤˣ) :
    (N + 1 : ℝ)⁻¹ *
      ((fun i : Fin N => (σ i.castSucc : ℝ)) ⬝ᵥ
        fun i : Fin N => (σ i.castSucc : ℝ)) =
      (N : ℝ) / (N + 1 : ℝ) := by
  simp only [dotProduct, ← sq]
  simp_rw [show ∀ i : Fin N, (σ i.castSucc : ℝ) ^ 2 = 1 from
    fun i => by simpa using units_cast_sq (σ i.castSucc)]
  simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul, mul_one]
  ring

end SpinGlasses
