/-
Copyright (c) 2025 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.NTK.Basic
public import LeanMachineLearning.Optimization.NTK.Foundations.MatrixUtil
public import LeanMachineLearning.Optimization.NTK.Initialization.DeepRecursion

/-!
# Finite-Width Multilayer Architecture, Sensitivities, and Empirical Covariances

This file formalizes the finite-width multilayer perceptron (MLP) architecture,
forward pre-activations, backward sensitivity recurrence, and the empirical forward/backward
Gram matrices that constitute the building blocks of the deep Neural Tangent Kernel (NTK).

## Mathematical Overview

For an MLP of architectural depth `d ≥ 1`, input dimension `n₀`, uniform hidden width `n`,
activation `φ : ℝ → ℝ`, and derivative `φ' : ℝ → ℝ`:

1. **Parameters** (`DeepMLPParams`):
   - Input weight matrix `W₀ ∈ ℝ^{n × n₀}`.
   - Hidden weight matrices `W_ℓ ∈ ℝ^{n × n}` for `ℓ ∈ {0, ..., d - 2}`.
   - Readout weight vector `W_d ∈ ℝ^n`.

2. **Pre-activations** (`deepMLPPreactivation`):
   - `h₀^α = (n₀)⁻¹/² (W₀ x^α)`
   - `h_{ℓ+1}^α = n⁻¹/² W_ℓ φ(h_ℓ^α)`

3. **Scalar Output** (`deepMLPOutput`):
   - `f^α = n⁻¹/² (W_d ⬝ᵥ φ(h_{d-1}^α))`

4. **Backward Sensitivities** (`backwardSensitivity`):
   Normalized sensitivity vector `g_ℓ^α = √n ∇_{h_ℓ^α} f^α ∈ ℝ^n`:
   - Top layer `g_{d-1}^α = W_d ⊙ φ'(h_{d-1}^α)`
   - Lower layers `g_ℓ^α = (1/√n) diag(φ'(h_ℓ^α)) W_ℓᵀ g_{ℓ+1}^α`

5. **Empirical Gram Matrices**:
   - Forward feature Gram matrix `Φ_ℓ^{(n)}` (`empiricalForwardCov`):
     - `Φ₀ = (1/n₀) X Xᵀ`
     - `Φ_{k+1}^{(n), αβ} = (1/n) ⟨φ(h_k^α), φ(h_k^β)⟩`
   - Backward sensitivity Gram matrix `G_{ℓ+1}^{(n)}` (`empiricalBackwardCov`):
     - `G_{k+1}^{(n), αβ} = (1/n) ⟨g_k^α, g_k^β⟩` for `k ∈ {0, ..., d - 1}`
     - `G_{d+1}^{(n)} = 1_{m × m}` (terminal condition)
   - Derivative feature Gram matrix `Φ'_{k+1}^{(n)}` (`empiricalDerivCov`):
     - `Φ'_{k+1}^{(n), αβ} = (1/n) ⟨φ'(h_k^α), φ'(h_k^β)⟩`
-/

@[expose]
public section

open scoped Matrix Real

namespace NTK

/-- Multilayer perceptron parameters for a network of architectural depth `d`,
input dimension `n0`, and uniform hidden width `n`.

- `W0 ∈ ℝ^{n × n0}`: input weight matrix connecting raw inputs to first hidden layer.
- `Wh ℓ ∈ ℝ^{n × n}`: hidden weight matrices connecting layer `ℓ` to `ℓ + 1`,
  indexed by `Fin (d - 1)` (for layers `ℓ ∈ {0, ..., d - 2}`).
- `Wd ∈ ℝ^n`: readout weight vector connecting the final hidden layer to scalar output. -/
structure DeepMLPParams (d n0 n : ℕ) where
  /-- Input-to-first-hidden-layer weight matrix `W0 ∈ ℝ^{n × n0}`. -/
  W0 : Matrix (Fin n) (Fin n0) ℝ
  /-- Hidden-to-hidden layer weight matrices `Wh ℓ ∈ ℝ^{n × n}` for `ℓ ∈ {0, ..., d - 2}`. -/
  Wh : Fin (d - 1) → Matrix (Fin n) (Fin n) ℝ
  /-- Readout layer weights `Wd ∈ ℝ^n`. -/
  Wd : Fin n → ℝ

/-- Convert an infinite weight tensor `W : ℕ → ℕ → ℕ → ℝ` and readout vector `w_out : ℕ → ℝ`
to finite parameters `DeepMLPParams d n0 n`. -/
def DeepMLPParams.ofTensor (d n0 n : ℕ) (W : ℕ → ℕ → ℕ → ℝ) (w_out : ℕ → ℝ) :
    DeepMLPParams d n0 n where
  W0 := Matrix.of fun j k => W 0 j.val k.val
  Wh := fun ⟨ℓ, _⟩ => Matrix.of fun j k => W (ℓ + 1) j.val k.val
  Wd := fun j => w_out j.val

/-- Pre-activations `h_ℓ^α ∈ ℝ^n` at each hidden layer `ℓ ∈ Fin d` for evaluation inputs `X`.
The normalization factors match `NTK.deepPreactivation`:
- Input layer `ℓ = 0`: `(n0 : ℝ)⁻¹.sqrt • (W0 ⬝ᵥ X α)`
- Hidden layers `ℓ + 1`: `(n : ℝ)⁻¹.sqrt • (Wh ℓ * φ(h_ℓ^α))` -/
noncomputable def deepMLPPreactivation (d n0 n m : ℕ) (φ : ℝ → ℝ) (X : Fin m → Fin n0 → ℝ)
    (θ : DeepMLPParams d n0 n) : Fin d → Fin m → Fin n → ℝ
  | ⟨0, _⟩ => fun α j => Real.sqrt ((n0 : ℝ)⁻¹) * (θ.W0 j ⬝ᵥ X α)
  | ⟨ℓ + 1, hℓ⟩ => fun α j =>
      Real.sqrt ((n : ℝ)⁻¹) * ∑ k : Fin n,
        θ.Wh ⟨ℓ, by omega⟩ j k * φ (deepMLPPreactivation d n0 n m φ X θ ⟨ℓ, by omega⟩ α k)

lemma deepMLPPreactivation_zero (d n0 n m : ℕ) (φ : ℝ → ℝ) (X : Fin m → Fin n0 → ℝ)
    (θ : DeepMLPParams d n0 n) (h0 : 0 < d) (α : Fin m) (j : Fin n) :
    deepMLPPreactivation d n0 n m φ X θ ⟨0, h0⟩ α j =
      Real.sqrt ((n0 : ℝ)⁻¹) * (θ.W0 j ⬝ᵥ X α) := by
  rw [deepMLPPreactivation]

lemma deepMLPPreactivation_succ (d n0 n m : ℕ) (φ : ℝ → ℝ) (X : Fin m → Fin n0 → ℝ)
    (θ : DeepMLPParams d n0 n) (ℓ : ℕ) (hℓ : ℓ + 1 < d) (α : Fin m) (j : Fin n) :
    deepMLPPreactivation d n0 n m φ X θ ⟨ℓ + 1, hℓ⟩ α j =
      Real.sqrt ((n : ℝ)⁻¹) * ∑ k : Fin n,
        θ.Wh ⟨ℓ, by omega⟩ j k * φ (deepMLPPreactivation d n0 n m φ X θ ⟨ℓ, by omega⟩ α k) := by
  rw [deepMLPPreactivation]

/-- Bridge connecting `deepMLPPreactivation` to `NTK.deepPreactivation` from
`Initialization/DeepRecursion.lean`. -/
lemma deepMLPPreactivation_ofTensor_eq_deepPreactivation (d n0 n m : ℕ) (φ : ℝ → ℝ)
    (X : Fin m → Fin n0 → ℝ) (W : ℕ → ℕ → ℕ → ℝ) (w_out : ℕ → ℝ) (ℓ : ℕ) (hℓ : ℓ < d) :
    deepMLPPreactivation d n0 n m φ X (DeepMLPParams.ofTensor d n0 n W w_out) ⟨ℓ, hℓ⟩ =
      deepPreactivation n0 m n φ X W ℓ := by
  induction ℓ with
  | zero =>
      ext α j
      rw [deepMLPPreactivation]
      simp [deepPreactivation, DeepMLPParams.ofTensor, dotProduct, Real.sqrt_inv]
  | succ ℓ ih =>
      ext α j
      have hprev : ℓ < d := by omega
      have hih := ih hprev
      rw [deepMLPPreactivation]
      simp only [DeepMLPParams.ofTensor, Matrix.of_apply, deepPreactivation, Real.sqrt_inv]
      congr 1
      apply Finset.sum_congr rfl
      intro k _
      congr 2
      exact congr_fun (congr_fun hih α) k

/-- Scalar network output `f^α = (n : ℝ)⁻¹/² (Wd ⬝ᵥ φ(h_{d-1}^α))` for sample `α`. -/
noncomputable def deepMLPOutput (d n0 n m : ℕ) (φ : ℝ → ℝ) (X : Fin m → Fin n0 → ℝ)
    (θ : DeepMLPParams d n0 n) (hd : 0 < d) : Fin m → ℝ :=
  fun α => Real.sqrt ((n : ℝ)⁻¹) * (θ.Wd ⬝ᵥ fun j =>
    φ (deepMLPPreactivation d n0 n m φ X θ ⟨d - 1, by omega⟩ α j))

/-- Empirical forward Gram matrix `Φ_ℓ^{(n)} ∈ ℝ^{m × m}` for `ℓ ∈ Fin (d + 1)`:
- `ℓ = 0`: base input Gram matrix `(n0 : ℝ)⁻¹ • (X α ⬝ᵥ X β)`
- `ℓ = k + 1`: feature Gram matrix `(n : ℝ)⁻¹ • (φ(h_k^α) ⬝ᵥ φ(h_k^β))` -/
noncomputable def empiricalForwardCov (d n0 n m : ℕ) (φ : ℝ → ℝ) (X : Fin m → Fin n0 → ℝ)
    (θ : DeepMLPParams d n0 n) (ℓ : Fin (d + 1)) : Matrix (Fin m) (Fin m) ℝ :=
  if h0 : ℓ.val = 0 then
    Matrix.of fun α β => (n0 : ℝ)⁻¹ * (X α ⬝ᵥ X β)
  else
    have hpred : ℓ.val - 1 < d := by omega
    Matrix.of fun α β =>
      (n : ℝ)⁻¹ * ((fun j => φ (deepMLPPreactivation d n0 n m φ X θ ⟨ℓ.val - 1, hpred⟩ α j)) ⬝ᵥ
                   (fun j => φ (deepMLPPreactivation d n0 n m φ X θ ⟨ℓ.val - 1, hpred⟩ β j)))

lemma empiricalForwardCov_zero (d n0 n m : ℕ) (φ : ℝ → ℝ) (X : Fin m → Fin n0 → ℝ)
    (θ : DeepMLPParams d n0 n) (h0 : 0 < d + 1) :
    empiricalForwardCov d n0 n m φ X θ ⟨0, h0⟩ =
      Matrix.of fun α β => (n0 : ℝ)⁻¹ * (X α ⬝ᵥ X β) := by
  ext α β
  simp [empiricalForwardCov]

lemma empiricalForwardCov_succ (d n0 n m : ℕ) (φ : ℝ → ℝ) (X : Fin m → Fin n0 → ℝ)
    (θ : DeepMLPParams d n0 n) (k : ℕ) (hk : k < d) :
    empiricalForwardCov d n0 n m φ X θ ⟨k + 1, by omega⟩ =
      Matrix.of fun α β =>
        (n : ℝ)⁻¹ * ((fun j => φ (deepMLPPreactivation d n0 n m φ X θ ⟨k, hk⟩ α j)) ⬝ᵥ
                     (fun j => φ (deepMLPPreactivation d n0 n m φ X θ ⟨k, hk⟩ β j))) := by
  ext α β
  rw [empiricalForwardCov]
  have h0 : ¬ (⟨k + 1, by omega⟩ : Fin (d + 1)).val = 0 := by simp
  simp only [h0, ↓reduceDIte, Matrix.of_apply]
  have heq : (⟨(⟨k + 1, by omega⟩ : Fin (d + 1)).val - 1, by omega⟩ : Fin d) = ⟨k, hk⟩ :=
    Fin.ext (by simp)
  rw [heq]

/-- The empirical forward Gram matrix `Φ_ℓ^{(n)}` is symmetric. -/
theorem empiricalForwardCov_transpose (d n0 n m : ℕ) (φ : ℝ → ℝ) (X : Fin m → Fin n0 → ℝ)
    (θ : DeepMLPParams d n0 n) (ℓ : Fin (d + 1)) :
    (empiricalForwardCov d n0 n m φ X θ ℓ)ᵀ = empiricalForwardCov d n0 n m φ X θ ℓ := by
  simp only [empiricalForwardCov]
  split_ifs
  · exact scaled_gram_transpose (n0 : ℝ)⁻¹ X
  · exact scaled_gram_transpose (n : ℝ)⁻¹ _

/-- The empirical forward Gram matrix `Φ_ℓ^{(n)}` is positive semidefinite. -/
theorem empiricalForwardCov_posSemidef (d n0 n m : ℕ) (φ : ℝ → ℝ) (X : Fin m → Fin n0 → ℝ)
    (θ : DeepMLPParams d n0 n) (ℓ : Fin (d + 1)) :
    (empiricalForwardCov d n0 n m φ X θ ℓ).PosSemidef := by
  simp only [empiricalForwardCov]
  split_ifs
  · exact scaled_gram_posSemidef (n0 : ℝ)⁻¹ (by positivity) X
  · exact scaled_gram_posSemidef (n : ℝ)⁻¹ (by positivity) _

/-- Empirical derivative covariance matrix `Φ'_{k+1}^{(n)} ∈ ℝ^{m × m}` for hidden layer
`k ∈ Fin d`: `Φ'_{k+1}^{(n), αβ} = (n : ℝ)⁻¹ • (φ'(h_k^α) ⬝ᵥ φ'(h_k^β))`. -/
noncomputable def empiricalDerivCov (d n0 n m : ℕ) (φ φ' : ℝ → ℝ) (X : Fin m → Fin n0 → ℝ)
    (θ : DeepMLPParams d n0 n) (k : Fin d) : Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of fun α β =>
    (n : ℝ)⁻¹ * ((fun j => φ' (deepMLPPreactivation d n0 n m φ X θ k α j)) ⬝ᵥ
                 (fun j => φ' (deepMLPPreactivation d n0 n m φ X θ k β j)))

/-- The empirical derivative Gram matrix `Φ'_{k+1}^{(n)}` is symmetric. -/
theorem empiricalDerivCov_transpose (d n0 n m : ℕ) (φ φ' : ℝ → ℝ) (X : Fin m → Fin n0 → ℝ)
    (θ : DeepMLPParams d n0 n) (k : Fin d) :
    (empiricalDerivCov d n0 n m φ φ' X θ k)ᵀ = empiricalDerivCov d n0 n m φ φ' X θ k :=
  scaled_gram_transpose (n : ℝ)⁻¹ _

/-- The empirical derivative Gram matrix `Φ'_{k+1}^{(n)}` is positive semidefinite. -/
theorem empiricalDerivCov_posSemidef (d n0 n m : ℕ) (φ φ' : ℝ → ℝ) (X : Fin m → Fin n0 → ℝ)
    (θ : DeepMLPParams d n0 n) (k : Fin d) :
    (empiricalDerivCov d n0 n m φ φ' X θ k).PosSemidef :=
  scaled_gram_posSemidef (n : ℝ)⁻¹ (by positivity) _

/-- Normalized backward sensitivity vectors `g_ℓ^α = √n ∇_{h_ℓ^α} f^α ∈ ℝ^n` for `ℓ ∈ Fin d`.
Satisfies the backward recurrence:
- Top hidden layer `ℓ = d - 1`: `g_{d-1}^α = Wd ⊙ φ'(h_{d-1}^α)`
- Lower layers `ℓ < d - 1`: `g_ℓ^α = (1/√n) diag(φ'(h_ℓ^α)) Wh(ℓ)ᵀ g_{ℓ+1}^α` -/
noncomputable def backwardSensitivity (d n0 n m : ℕ) (φ φ' : ℝ → ℝ) (X : Fin m → Fin n0 → ℝ)
    (θ : DeepMLPParams d n0 n) : Fin d → Fin m → Fin n → ℝ
  | ⟨ℓ, hℓ⟩ =>
      if htop : ℓ = d - 1 then
        fun α j => θ.Wd j * φ' (deepMLPPreactivation d n0 n m φ X θ ⟨ℓ, hℓ⟩ α j)
      else
        have hsucc : ℓ + 1 < d := by omega
        fun α j =>
          φ' (deepMLPPreactivation d n0 n m φ X θ ⟨ℓ, hℓ⟩ α j) *
            (Real.sqrt ((n : ℝ)⁻¹) * ∑ i : Fin n,
              θ.Wh ⟨ℓ, by omega⟩ i j *
                backwardSensitivity d n0 n m φ φ' X θ ⟨ℓ + 1, hsucc⟩ α i)
termination_by ℓ => d - 1 - ℓ.val
decreasing_by omega

lemma backwardSensitivity_top (d n0 n m : ℕ) (φ φ' : ℝ → ℝ) (X : Fin m → Fin n0 → ℝ)
    (θ : DeepMLPParams d n0 n) (hd : 0 < d) (α : Fin m) (j : Fin n) :
    backwardSensitivity d n0 n m φ φ' X θ ⟨d - 1, by omega⟩ α j =
      θ.Wd j * φ' (deepMLPPreactivation d n0 n m φ X θ ⟨d - 1, by omega⟩ α j) := by
  rw [backwardSensitivity]
  simp

lemma backwardSensitivity_step (d n0 n m : ℕ) (φ φ' : ℝ → ℝ) (X : Fin m → Fin n0 → ℝ)
    (θ : DeepMLPParams d n0 n) (ℓ : Fin d) (hne : ℓ.val < d - 1) (α : Fin m) (j : Fin n) :
    backwardSensitivity d n0 n m φ φ' X θ ℓ α j =
      φ' (deepMLPPreactivation d n0 n m φ X θ ℓ α j) *
        (Real.sqrt ((n : ℝ)⁻¹) * ∑ i : Fin n,
          θ.Wh ⟨ℓ.val, by omega⟩ i j *
            backwardSensitivity d n0 n m φ φ' X θ ⟨ℓ.val + 1, by omega⟩ α i) := by
  rw [backwardSensitivity]
  have htop : ¬ ℓ.val = d - 1 := by omega
  simp [htop]

/-- Empirical backward Gram matrix `G_{ℓ+1}^{(n)} ∈ ℝ^{m × m}` for `ℓ ∈ Fin (d + 1)`:
- `ℓ = 0, ..., d - 1`: hidden sensitivity covariance `(n : ℝ)⁻¹ • (g_ℓ^α ⬝ᵥ g_ℓ^β)`
- `ℓ = d`: terminal condition `G_{d+1}^{(n)} = 1_{m × m}` -/
noncomputable def empiricalBackwardCov (d n0 n m : ℕ) (φ φ' : ℝ → ℝ) (X : Fin m → Fin n0 → ℝ)
    (θ : DeepMLPParams d n0 n) (ℓ : Fin (d + 1)) : Matrix (Fin m) (Fin m) ℝ :=
  if htop : ℓ.val = d then
    Matrix.of fun _ _ => 1
  else
    have hℓ : ℓ.val < d := by omega
    Matrix.of fun α β =>
      (n : ℝ)⁻¹ * (backwardSensitivity d n0 n m φ φ' X θ ⟨ℓ.val, hℓ⟩ α ⬝ᵥ
                   backwardSensitivity d n0 n m φ φ' X θ ⟨ℓ.val, hℓ⟩ β)

lemma empiricalBackwardCov_terminal (d n0 n m : ℕ) (φ φ' : ℝ → ℝ) (X : Fin m → Fin n0 → ℝ)
    (θ : DeepMLPParams d n0 n) :
    empiricalBackwardCov d n0 n m φ φ' X θ ⟨d, by omega⟩ =
      Matrix.of fun _ _ => 1 := by
  ext α β
  simp [empiricalBackwardCov]

lemma empiricalBackwardCov_hidden (d n0 n m : ℕ) (φ φ' : ℝ → ℝ) (X : Fin m → Fin n0 → ℝ)
    (θ : DeepMLPParams d n0 n) (k : ℕ) (hk : k < d) :
    empiricalBackwardCov d n0 n m φ φ' X θ ⟨k, by omega⟩ =
      Matrix.of fun α β =>
        (n : ℝ)⁻¹ * (backwardSensitivity d n0 n m φ φ' X θ ⟨k, hk⟩ α ⬝ᵥ
                     backwardSensitivity d n0 n m φ φ' X θ ⟨k, hk⟩ β) := by
  ext α β
  rw [empiricalBackwardCov]
  have htop : ¬ (⟨k, by omega⟩ : Fin (d + 1)).val = d := by
    intro h
    have : (⟨k, by omega⟩ : Fin (d + 1)).val = k := rfl
    omega
  simp only [htop, ↓reduceDIte, Matrix.of_apply]

/-- The empirical backward Gram matrix `G_{ℓ+1}^{(n)}` is symmetric. -/
theorem empiricalBackwardCov_transpose (d n0 n m : ℕ) (φ φ' : ℝ → ℝ) (X : Fin m → Fin n0 → ℝ)
    (θ : DeepMLPParams d n0 n) (ℓ : Fin (d + 1)) :
    (empiricalBackwardCov d n0 n m φ φ' X θ ℓ)ᵀ = empiricalBackwardCov d n0 n m φ φ' X θ ℓ := by
  simp only [empiricalBackwardCov]
  split_ifs
  · exact const_matrix_transpose 1
  · exact scaled_gram_transpose (n : ℝ)⁻¹ _

/-- The empirical backward Gram matrix `G_{ℓ+1}^{(n)}` is positive semidefinite. -/
theorem empiricalBackwardCov_posSemidef (d n0 n m : ℕ) (φ φ' : ℝ → ℝ) (X : Fin m → Fin n0 → ℝ)
    (θ : DeepMLPParams d n0 n) (ℓ : Fin (d + 1)) :
    (empiricalBackwardCov d n0 n m φ φ' X θ ℓ).PosSemidef := by
  simp only [empiricalBackwardCov]
  split_ifs
  · exact posSemidef_allOnes
  · exact scaled_gram_posSemidef (n : ℝ)⁻¹ (by positivity) _

end NTK

end
