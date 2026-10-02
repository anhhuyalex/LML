/-
Copyright (c) 2025 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.NTK.Basic
public import LeanMachineLearning.Optimization.NTK.Foundations.MatrixUtil
public import LeanMachineLearning.Optimization.NTK.Deep.Architecture
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.LinearAlgebra.Matrix.Hadamard
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Exact Layerwise NTK Decomposition and Positive Semidefiniteness (Proposition 2.25)

This file formalizes the finite-width multilayer Neural Tangent Kernel (NTK) Gram matrix
`deepEmpiricalNTK` and proves Proposition 2.25: the exact layerwise Hadamard decomposition
across parameter blocks, its symmetry, positive semidefiniteness, and Loewner order dominance
over the top-layer forward feature covariance (the finite-width NNGP kernel).

## Mathematical Overview

For an MLP of architectural depth `d`, input dimension `n₀`, hidden width `n`, evaluation inputs
`X : Fin m → Fin n₀ → ℝ`, activation `φ`, weak derivative `φ'`, and parameters `θ : DeepMLPParams`:

1. **Empirical NTK Matrix** (`deepEmpiricalNTK`):
   $$\mathbf{\Theta}^{\mathrm{emp}, (d)} :=
     \sum_{\ell=0}^d \mathbf{G}_{\ell+1}^{(n)} \odot \boldsymbol{\Phi}_\ell^{(n)}$$
   where:
   - `Φ_ℓ^{(n)} ∈ ℝ^{m × m}` is the empirical forward feature covariance at layer `ℓ`
     (`deepActivationGram`).
   - `G_{ℓ+1}^{(n)} ∈ ℝ^{m × m}` is the empirical backward error sensitivity covariance
     (`deepSensitivityGram`).

2. **Properties**:
   - **Exact Decomposition** (`deepEmpiricalNTK_eq_sum_hadamard`): Holds definitionally.
   - **Symmetry** (`deepEmpiricalNTK_transpose`):
     `((Θ^{emp, (d)})ᵀ = Θ^{emp, (d)})`.
   - **Positive Semidefiniteness** (`deepEmpiricalNTK_posSemidef`):
     `Θ^{emp, (d)}` is positive semidefinite via the Schur product theorem
     (`Matrix.PosSemidef.hadamard`) applied to each layer summand `G_{ℓ+1}^{(n)} ⊙ Φ_ℓ^{(n)}`.
   - **Loewner Order Dominance** (`deepEmpiricalNTK_ge_nngp`):
     `Φ_d^{(n)} ≤ Θ^{emp, (d)}`, where the difference
     `Θ^{emp, (d)} - Φ_d^{(n)} = ∑_{ℓ=0}^{d-1} G_{ℓ+1}^{(n)} ⊙ Φ_ℓ^{(n)} ≥ 0`.

## Disambiguation and Design Decisions

- **Single Definition Architecture**: Aligned with the repository plan, this module introduces
  exactly one definition (`deepEmpiricalNTK`), eliminating intermediate wrappers.
- **Loewner Order**: Expressed via Mathlib's canonical order on matrices
  (`Matrix.le_iff : A ≤ B ↔ (B - A).PosSemidef` from `Mathlib.Analysis.Matrix.Order`).
-/

@[expose]
public section

open scoped Matrix Real BigOperators MatrixOrder

namespace NTK

/-- Finite-width empirical Neural Tangent Kernel (NTK) Gram matrix `Θ^{emp, (d)} ∈ ℝ^{m × m}`
defined via the exact layerwise Hadamard decomposition (Proposition 2.25):
`Θ^{emp, (d)} = ∑_{ℓ=0}^d G_{ℓ+1}^{(n)} ⊙ Φ_ℓ^{(n)}`. -/
noncomputable def deepEmpiricalNTK (d n0 n m : ℕ) (φ φ' : ℝ → ℝ) (X : Fin m → Fin n0 → ℝ)
    (θ : DeepMLPParams d n0 n) : Matrix (Fin m) (Fin m) ℝ :=
  ∑ ℓ : Fin (d + 1),
    deepSensitivityGram d n0 n m φ φ' X θ ℓ ⊙ deepActivationGram d n0 n m φ X θ ℓ

/-- Exact layerwise Hadamard decomposition of the empirical NTK (Proposition 2.25). -/
theorem deepEmpiricalNTK_eq_sum_hadamard (d n0 n m : ℕ) (φ φ' : ℝ → ℝ)
    (X : Fin m → Fin n0 → ℝ) (θ : DeepMLPParams d n0 n) :
    deepEmpiricalNTK d n0 n m φ φ' X θ =
      ∑ ℓ : Fin (d + 1),
        deepSensitivityGram d n0 n m φ φ' X θ ℓ ⊙
        deepActivationGram d n0 n m φ X θ ℓ :=
  rfl

/-- The finite-width empirical NTK matrix is symmetric. -/
theorem deepEmpiricalNTK_transpose (d n0 n m : ℕ) (φ φ' : ℝ → ℝ)
    (X : Fin m → Fin n0 → ℝ) (θ : DeepMLPParams d n0 n) :
    (deepEmpiricalNTK d n0 n m φ φ' X θ)ᵀ = deepEmpiricalNTK d n0 n m φ φ' X θ := by
  simp only [deepEmpiricalNTK, Matrix.transpose_sum, Matrix.transpose_hadamard,
    deepSensitivityGram_transpose, deepActivationGram_transpose]

/-- The finite-width empirical NTK matrix is positive semidefinite. -/
theorem deepEmpiricalNTK_posSemidef (d n0 n m : ℕ) (φ φ' : ℝ → ℝ)
    (X : Fin m → Fin n0 → ℝ) (θ : DeepMLPParams d n0 n) :
    (deepEmpiricalNTK d n0 n m φ φ' X θ).PosSemidef := by
  rw [deepEmpiricalNTK]
  apply Matrix.posSemidef_sum
  intro ℓ _
  exact (deepSensitivityGram_posSemidef d n0 n m φ φ' X θ ℓ).hadamard
    (deepActivationGram_posSemidef d n0 n m φ X θ ℓ)

/-- Loewner order dominance of the empirical NTK over the top-layer forward feature
covariance (NNGP kernel): `Φ_d^{(n)} ≤ Θ^{emp, (d)}`.
The difference `Θ^{emp, (d)} - Φ_d^{(n)} = ∑_{ℓ < d} G_{ℓ+1}^{(n)} ⊙ Φ_ℓ^{(n)}` is positive
semidefinite. -/
theorem deepEmpiricalNTK_ge_nngp (d n0 n m : ℕ) (φ φ' : ℝ → ℝ) (X : Fin m → Fin n0 → ℝ)
    (θ : DeepMLPParams d n0 n) :
    deepActivationGram d n0 n m φ X θ ⟨d, by omega⟩ ≤ deepEmpiricalNTK d n0 n m φ φ' X θ := by
  rw [Matrix.le_iff]
  have hsplit : deepEmpiricalNTK d n0 n m φ φ' X θ =
      (∑ ℓ : Fin d,
        deepSensitivityGram d n0 n m φ φ' X θ ℓ.castSucc ⊙
        deepActivationGram d n0 n m φ X θ ℓ.castSucc) +
      deepActivationGram d n0 n m φ X θ ⟨d, by omega⟩ := by
    rw [deepEmpiricalNTK, Fin.sum_univ_castSucc]
    have hlast : deepSensitivityGram d n0 n m φ φ' X θ (Fin.last d) ⊙
        deepActivationGram d n0 n m φ X θ (Fin.last d) =
        deepActivationGram d n0 n m φ X θ ⟨d, by omega⟩ := by
      have hterm : deepSensitivityGram d n0 n m φ φ' X θ (Fin.last d) =
          Matrix.of fun _ _ => 1 := by
        apply deepSensitivityGram_terminal
      rw [hterm, allOnes_hadamard]
      rfl
    rw [hlast]
  rw [hsplit, add_sub_cancel_right]
  apply Matrix.posSemidef_sum
  intro ℓ _
  exact (deepSensitivityGram_posSemidef d n0 n m φ φ' X θ ℓ.castSucc).hadamard
    (deepActivationGram_posSemidef d n0 n m φ X θ ℓ.castSucc)

/-- Finite-width two-layer specialization: at architectural depth `d = 1`, the empirical NTK
matrix splits into the readout forward feature Gram matrix plus the input-layer Hadamard
product summand:
`Θ^{emp, (1)} = Φ_1^{(n)} + G_1^{(n)} ⊙ Φ_0^{(n)}`. -/
theorem deepEmpiricalNTK_twoLayer_eq_add_hadamard (n0 n m : ℕ) (φ φ' : ℝ → ℝ)
    (X : Fin m → Fin n0 → ℝ) (θ : DeepMLPParams 1 n0 n) :
    deepEmpiricalNTK 1 n0 n m φ φ' X θ =
      deepActivationGram 1 n0 n m φ X θ 1 +
        deepSensitivityGram 1 n0 n m φ φ' X θ 0 ⊙
          deepActivationGram 1 n0 n m φ X θ 0 := by
  rw [deepEmpiricalNTK, Fin.sum_univ_two]
  have hterm : deepSensitivityGram 1 n0 n m φ φ' X θ 1 = Matrix.of fun _ _ => 1 := by
    apply deepSensitivityGram_terminal
  rw [hterm, allOnes_hadamard]
  rw [add_comm]

end NTK

end
