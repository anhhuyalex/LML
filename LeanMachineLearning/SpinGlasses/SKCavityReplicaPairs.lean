/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Data.Fintype.BigOperators
public import LeanMachineLearning.ForMathlib.Algebra.BigOperators.OffDiag
public import LeanMachineLearning.SpinGlasses.SKFirstMoment

/-!
# The Canonical Three-Family Replica Pairs of the Cavity Path

This module defines the canonical signed index family representing the three groups of
replica pairs in the cavity path derivative (Talagrand Eq. 1.152):
1. Old-old pairs `(ℓ, ℓ')` with `1 ≤ ℓ < ℓ' ≤ n`, weight `1`;
2. Old-extra pairs `(ℓ, n+1)` with `1 ≤ ℓ ≤ n`, weight `-n`;
3. Extra-extra pair `(n+1, n+2)`, weight `n(n+1)/2`.

Centralizing this family eliminates duplicated index encodings across `SKCavityCovariance`,
`SKRectangularDerivative`, and the covariance equations.
-/

@[expose] public section

open scoped BigOperators

namespace SpinGlasses

/-- The three replica families of Eq. (1.152) indexed as a sum type. -/
abbrev SKCavityReplicaPair (n : ℕ) := FinPairs n ⊕ (Fin n ⊕ Unit)

/-- Canonical embedding of a family index into a pair of distinct lifted replicas
in `Option (Option (Fin n))`. -/
def skCavityReplicaPairMap {n : ℕ} (j : SKCavityReplicaPair n) :
    Option (Option (Fin n)) × Option (Option (Fin n)) :=
  match j with
  | Sum.inl s => (some (some s.val.1), some (some s.val.2))
  | Sum.inr (Sum.inl s) => (some (some s), some none)
  | Sum.inr (Sum.inr _) => (some none, none)

/-- The signed weights of the three replica families in Eq. (1.152). -/
noncomputable def skCavityReplicaPairWeight (n : ℕ) (j : SKCavityReplicaPair n) : ℝ :=
  match j with
  | Sum.inl _ => 1
  | Sum.inr (Sum.inl _) => -(n : ℝ)
  | Sum.inr (Sum.inr _) => (n : ℝ) * ((n : ℝ) + 1) / 2

/-- The two replicas in every family pair are distinct. -/
theorem skCavityReplicaPair_ne {n : ℕ} (j : SKCavityReplicaPair n) :
    (skCavityReplicaPairMap j).1 ≠ (skCavityReplicaPairMap j).2 := by
  rcases j with s | s | s
  · have h := s.property
    simp only [skCavityReplicaPairMap, ne_eq, Option.some.injEq]
    exact h.ne
  · simp [skCavityReplicaPairMap]
  · simp [skCavityReplicaPairMap]

/-- **Canonical sum-reindexing theorem:** The signed three-family sum of any bivariate
kernel `D` over lifted replicas equals the sum over `SKCavityReplicaPair n`. -/
theorem sk_cavity_signed_pair_sum {n : ℕ} {α : Type*} (D : α → α → ℝ)
    (τ : Option (Option (Fin n)) → α) :
    (∑ p : Fin n × Fin n with p.1 < p.2, D (τ (some (some p.1))) (τ (some (some p.2)))) -
      (n : ℝ) * ∑ r : Fin n, D (τ (some (some r))) (τ (some none)) +
      (n : ℝ) * ((n : ℝ) + 1) / 2 * D (τ (some none)) (τ none) =
    ∑ j : SKCavityReplicaPair n,
      skCavityReplicaPairWeight n j *
        D (τ (skCavityReplicaPairMap j).1) (τ (skCavityReplicaPairMap j).2) := by
  simp only [skCavityReplicaPairWeight, skCavityReplicaPairMap, Fintype.sum_sum_type,
    Finset.univ_unique, Finset.sum_singleton, ← Finset.mul_sum]
  rw [sum_filter_lt_eq_sum_subtype fun s : Fin n × Fin n =>
    D (τ (some (some s.1))) (τ (some (some s.2)))]
  ring

/-- The signed three-family sum scaled by a common factor `c`. -/
theorem sk_cavity_signed_pair_mul_sum {n : ℕ} {α : Type*} (D : α → α → ℝ)
    (τ : Option (Option (Fin n)) → α) (c : ℝ) :
    c * ((∑ p : Fin n × Fin n with p.1 < p.2,
            D (τ (some (some p.1))) (τ (some (some p.2)))) -
          (n : ℝ) * ∑ r : Fin n, D (τ (some (some r))) (τ (some none)) +
          (n : ℝ) * ((n : ℝ) + 1) / 2 * D (τ (some none)) (τ none)) =
      ∑ j : SKCavityReplicaPair n,
        skCavityReplicaPairWeight n j *
          (c * D (τ (skCavityReplicaPairMap j).1) (τ (skCavityReplicaPairMap j).2)) := by
  rw [sk_cavity_signed_pair_sum D τ, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

end SpinGlasses
