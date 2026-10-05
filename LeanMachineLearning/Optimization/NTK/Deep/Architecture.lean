/-
Copyright (c) 2025 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

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
   - Forward feature Gram matrix `Φ_ℓ^{(n)}` (`deepActivationGram`):
     - `Φ₀ = (1/n₀) X Xᵀ`
     - `Φ_{k+1}^{(n), αβ} = (1/n) ⟨φ(h_k^α), φ(h_k^β)⟩`
   - Backward sensitivity Gram matrix `G_{ℓ+1}^{(n)}` (`deepSensitivityGram`):
     - `G_{k+1}^{(n), αβ} = (1/n) ⟨g_k^α, g_k^β⟩` for `k ∈ {0, ..., d - 1}`
     - `G_{d+1}^{(n)} = 1_{m × m}` (terminal condition)
   - Derivative feature Gram matrix `Φ'_{k+1}^{(n)}` (`deepDerivativeGram`):
     - `Φ'_{k+1}^{(n), αβ} = (1/n) ⟨φ'(h_k^α), φ'(h_k^β)⟩`

## Disambiguation and Relationship to Other Declarations

This codebase formalizes deep neural networks across multiple domains with distinct needs:

1. **`deepMLPPreactivation` vs `NTK.deepPreactivation`**:
   - `deepMLPPreactivation` (this file): Evaluates a concrete, finite parameter record
     `θ : DeepMLPParams d n0 n` of depth `d`, with layer indices bounded by `Fin d`.
     Designed for parameter gradients `∇_θ f`, backward sensitivities, and empirical NTK Gram
     matrices.
   - `NTK.deepPreactivation` (`Initialization/DeepRecursion.lean`): Evaluates an infinite weight
     tensor `W : ℕ → ℕ → ℕ → ℝ` representing an i.i.d. Gaussian population across unbounded layer
     indices `ℓ : ℕ`. Designed for infinite-width measure-theoretic asymptotic limits ($n → ∞$).
   - In this file, `d` denotes *depth* and `n0` denotes *input dimension*, whereas in
     `DeepRecursion.lean`, `d` historically denoted the *input dimension*.
   - Bridge theorem `deepMLPPreactivation_ofTensor_eq_deepPreactivation` proves that evaluating
     `deepMLPPreactivation` on `DeepMLPParams.ofTensor` coincides with `NTK.deepPreactivation`.

2. **`deepMLPPreactivation` vs `NeuralNetwork.DenseLayer.preactivation`**:
   - `DenseLayer.preactivation` (`Renormalization/Network.lean`): Single-layer affine map with
     explicit bias `b + W x`.
   - `deepMLPPreactivation`: Multilayer perceptron without bias, adhering to the NTK normalization
     factors `(n0 : ℝ)⁻¹/²` and `(n : ℝ)⁻¹/²`.

3. **Naming convention for kernels and Gram matrices** (feature Gram vs. tangent kernel):
   - `…Gram` = a finite-width, random `m × m` matrix `(1/n) · Gram` of explicit feature vectors:
     `deepActivationGram` (activation features `φ(h)`, `Φ_ℓ`), `deepDerivativeGram` (derivative
     features `φ'(h)`, `Φ'_ℓ`), `deepSensitivityGram` (backward sensitivities `g`, `G_ℓ`).
   - `…Kernel` = a deterministic infinite-width limit (`deepLimitingSensitivityKernel`, `Π^ℓ`);
     the forward limits are `layerCovarianceSeq`.
   - `…NTK` = a tangent kernel, i.e. a Gram matrix of parameter gradients: `deepEmpiricalNTK` /
     `deepLimitingNTK` for the deep network, `shallowEmpiricalNTK` / `shallowLimitingNTK` for the
     frozen-readout two-layer weight block (`Shallow/Kernel.lean`), and `empiricalNTKMatrix` for
     the generic full-Jacobian Gram `J Jᵀ`.
   The `deep…Gram` matrices are the *ingredients* of `deepEmpiricalNTK`; they are not themselves
   tangent kernels.
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

/-- Pre-activations `h_ℓ^α ∈ ℝ^n` at each hidden layer `ℓ ∈ Fin d` for evaluation inputs `X`
under finite parameters `θ : DeepMLPParams d n0 n`.

### Normalization Factors:
- Input layer `ℓ = 0`: `(n0 : ℝ)⁻¹.sqrt • (W0 ⬝ᵥ X α)`
- Hidden layers `ℓ + 1`: `(n : ℝ)⁻¹.sqrt • (Wh ℓ * φ(h_ℓ^α))`

### Disambiguation:
- `deepMLPPreactivation` (this definition): parameterized finite-width forward pass indexed by
  `Fin d`.
- `NTK.deepPreactivation` (`Initialization/DeepRecursion.lean`): infinite-population Gaussian
  recurrence indexed by unbounded `ℕ` for NNGP measure-theoretic limits.
- Bridge theorem `deepMLPPreactivation_ofTensor_eq_deepPreactivation` connects the two. -/
noncomputable def deepMLPPreactivation (d n0 n m : ℕ) (φ : ℝ → ℝ) (X : Fin m → Fin n0 → ℝ)
    (θ : DeepMLPParams d n0 n) : Fin d → Fin m → Fin n → ℝ
  | ⟨0, _⟩ => fun α j => Real.sqrt ((n0 : ℝ)⁻¹) * (θ.W0 j ⬝ᵥ X α)
  | ⟨ℓ + 1, hℓ⟩ => fun α j =>
      Real.sqrt ((n : ℝ)⁻¹) * ∑ k : Fin n,
        θ.Wh ⟨ℓ, by omega⟩ j k * φ (deepMLPPreactivation d n0 n m φ X θ ⟨ℓ, by omega⟩ α k)

/-- The first preactivation layer: `h_0^α = n₀^{-1/2} W_0 x^α`. -/
lemma deepMLPPreactivation_zero (d n0 n m : ℕ) (φ : ℝ → ℝ) (X : Fin m → Fin n0 → ℝ)
    (θ : DeepMLPParams d n0 n) (h0 : 0 < d) (α : Fin m) (j : Fin n) :
    deepMLPPreactivation d n0 n m φ X θ ⟨0, h0⟩ α j =
      Real.sqrt ((n0 : ℝ)⁻¹) * (θ.W0 j ⬝ᵥ X α) := by
  rw [deepMLPPreactivation]

/-- The forward recursion: `h_{ℓ+1}^α = n^{-1/2} W_{ℓ+1} φ(h_ℓ^α)`. -/
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

/-- Scalar network output `f^α = (n : ℝ)⁻¹/² (Wd ⬝ᵥ φ(h_{d-1}^α))` for sample `α`.

Disambiguation: Computes the prediction of a finite-parameter network `θ : DeepMLPParams`.
In NNGP asymptotics (`Initialization/DeepNNGPTheorems.lean`), network outputs are instead
evaluated conditionally under the infinite product Gaussian measure. -/
noncomputable def deepMLPOutput (d n0 n m : ℕ) (φ : ℝ → ℝ) (X : Fin m → Fin n0 → ℝ)
    (θ : DeepMLPParams d n0 n) (hd : 0 < d) : Fin m → ℝ :=
  fun α => Real.sqrt ((n : ℝ)⁻¹) * (θ.Wd ⬝ᵥ fun j =>
    φ (deepMLPPreactivation d n0 n m φ X θ ⟨d - 1, by omega⟩ α j))

/-- Empirical forward Gram matrix `Φ_ℓ^{(n)} ∈ ℝ^{m × m}` for `ℓ ∈ Fin (d + 1)`:
- `ℓ = 0`: base input Gram matrix `(n0 : ℝ)⁻¹ • (X α ⬝ᵥ X β)`
- `ℓ = k + 1`: feature Gram matrix `(n : ℝ)⁻¹ • (φ(h_k^α) ⬝ᵥ φ(h_k^β))` -/
noncomputable def deepActivationGram (d n0 n m : ℕ) (φ : ℝ → ℝ) (X : Fin m → Fin n0 → ℝ)
    (θ : DeepMLPParams d n0 n) (ℓ : Fin (d + 1)) : Matrix (Fin m) (Fin m) ℝ :=
  if h0 : ℓ.val = 0 then
    Matrix.of fun α β => (n0 : ℝ)⁻¹ * (X α ⬝ᵥ X β)
  else
    have hpred : ℓ.val - 1 < d := by omega
    Matrix.of fun α β =>
      (n : ℝ)⁻¹ * ((fun j => φ (deepMLPPreactivation d n0 n m φ X θ ⟨ℓ.val - 1, hpred⟩ α j)) ⬝ᵥ
                   (fun j => φ (deepMLPPreactivation d n0 n m φ X θ ⟨ℓ.val - 1, hpred⟩ β j)))

/-- At layer `0` the activation Gram matrix is the input Gram matrix `n₀⁻¹ ⟨x^α, x^β⟩`. -/
lemma deepActivationGram_zero (d n0 n m : ℕ) (φ : ℝ → ℝ) (X : Fin m → Fin n0 → ℝ)
    (θ : DeepMLPParams d n0 n) (h0 : 0 < d + 1) :
    deepActivationGram d n0 n m φ X θ ⟨0, h0⟩ =
      Matrix.of fun α β => (n0 : ℝ)⁻¹ * (X α ⬝ᵥ X β) := by
  ext α β
  simp [deepActivationGram]

/-- The activation Gram matrix at layer `k + 1` is the Gram matrix `n⁻¹ ⟨φ(h_k^α), φ(h_k^β)⟩` of the
layer-`k` activations. -/
lemma deepActivationGram_succ (d n0 n m : ℕ) (φ : ℝ → ℝ) (X : Fin m → Fin n0 → ℝ)
    (θ : DeepMLPParams d n0 n) (k : ℕ) (hk : k < d) :
    deepActivationGram d n0 n m φ X θ ⟨k + 1, by omega⟩ =
      Matrix.of fun α β =>
        (n : ℝ)⁻¹ * ((fun j => φ (deepMLPPreactivation d n0 n m φ X θ ⟨k, hk⟩ α j)) ⬝ᵥ
                     (fun j => φ (deepMLPPreactivation d n0 n m φ X θ ⟨k, hk⟩ β j))) := by
  ext α β
  rw [deepActivationGram]
  have h0 : ¬ (⟨k + 1, by omega⟩ : Fin (d + 1)).val = 0 := by simp
  simp only [h0, ↓reduceDIte, Matrix.of_apply]
  have heq : (⟨(⟨k + 1, by omega⟩ : Fin (d + 1)).val - 1, by omega⟩ : Fin d) = ⟨k, hk⟩ :=
    Fin.ext (by simp)
  rw [heq]

/-- The empirical forward Gram matrix `Φ_ℓ^{(n)}` is symmetric. -/
theorem deepActivationGram_transpose (d n0 n m : ℕ) (φ : ℝ → ℝ) (X : Fin m → Fin n0 → ℝ)
    (θ : DeepMLPParams d n0 n) (ℓ : Fin (d + 1)) :
    (deepActivationGram d n0 n m φ X θ ℓ)ᵀ = deepActivationGram d n0 n m φ X θ ℓ := by
  simp only [deepActivationGram]
  split_ifs
  · exact scaled_gram_transpose (n0 : ℝ)⁻¹ X
  · exact scaled_gram_transpose (n : ℝ)⁻¹ _

/-- The empirical forward Gram matrix `Φ_ℓ^{(n)}` is positive semidefinite. -/
theorem deepActivationGram_posSemidef (d n0 n m : ℕ) (φ : ℝ → ℝ) (X : Fin m → Fin n0 → ℝ)
    (θ : DeepMLPParams d n0 n) (ℓ : Fin (d + 1)) :
    (deepActivationGram d n0 n m φ X θ ℓ).PosSemidef := by
  simp only [deepActivationGram]
  split_ifs
  · exact scaled_gram_posSemidef (n0 : ℝ)⁻¹ (by positivity) X
  · exact scaled_gram_posSemidef (n : ℝ)⁻¹ (by positivity) _

/-- Empirical derivative covariance matrix `Φ'_{k+1}^{(n)} ∈ ℝ^{m × m}` for hidden layer
`k ∈ Fin d`: `Φ'_{k+1}^{(n), αβ} = (n : ℝ)⁻¹ • (φ'(h_k^α) ⬝ᵥ φ'(h_k^β))`. -/
noncomputable def deepDerivativeGram (d n0 n m : ℕ) (φ φ' : ℝ → ℝ) (X : Fin m → Fin n0 → ℝ)
    (θ : DeepMLPParams d n0 n) (k : Fin d) : Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of fun α β =>
    (n : ℝ)⁻¹ * ((fun j => φ' (deepMLPPreactivation d n0 n m φ X θ k α j)) ⬝ᵥ
                 (fun j => φ' (deepMLPPreactivation d n0 n m φ X θ k β j)))

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

/-- The top backward sensitivity is `g_{d-1} = W_d ⊙ φ'(h_{d-1})`. -/
lemma backwardSensitivity_top (d n0 n m : ℕ) (φ φ' : ℝ → ℝ) (X : Fin m → Fin n0 → ℝ)
    (θ : DeepMLPParams d n0 n) (hd : 0 < d) (α : Fin m) (j : Fin n) :
    backwardSensitivity d n0 n m φ φ' X θ ⟨d - 1, by omega⟩ α j =
      θ.Wd j * φ' (deepMLPPreactivation d n0 n m φ X θ ⟨d - 1, by omega⟩ α j) := by
  rw [backwardSensitivity]
  simp

/-- The backward recursion for `ℓ < d - 1`: `g_ℓ` is `φ'(h_ℓ)` times the sensitivity `g_{ℓ+1}` back-
propagated through `W_{ℓ+1}ᵀ`. -/
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

/-- **Downward induction on `Fin n`.** To prove `P ℓ` for every layer `ℓ`, prove it at the top
layer (`ℓ.val + 1 = n`) and show that `P (ℓ + 1)` implies `P ℓ` for every non-top layer. Used for
the backward recursions (`backwardSensitivity`, `deepLimitingSensitivityKernel`). -/
@[elab_as_elim]
theorem backwardInduction {n : ℕ} {P : Fin n → Prop}
    (top : ∀ ℓ : Fin n, ℓ.val + 1 = n → P ℓ)
    (step : ∀ ℓ : Fin n, (hℓ : ℓ.val + 1 < n) → P ⟨ℓ.val + 1, hℓ⟩ → P ℓ) (ℓ : Fin n) : P ℓ := by
  suffices H : ∀ k : ℕ, ∀ ℓ : Fin n, n - 1 - ℓ.val = k → P ℓ from H _ ℓ rfl
  intro k
  induction k with
  | zero => intro ℓ h; exact top ℓ (by have := ℓ.2; omega)
  | succ k ih =>
    intro ℓ h
    have hℓ : ℓ.val + 1 < n := by have := ℓ.2; omega
    exact step ℓ hℓ (ih ⟨ℓ.val + 1, hℓ⟩ (by simp only; omega))

/-- **Suffix congruence for the backward pass.** The sensitivity `g_ℓ` reads only the readout `Wd`,
the hidden weights `Wh k` and the preactivations `h_k` with `k ≥ ℓ` (the mirror image of
`deepPreactivation_congr_of_eqOn`, where `h_ℓ` reads only the weights up to `ℓ`). In particular
`g_{k+1}` sees `W_{k+1} = Wh k` only through `h_{k+1} = n^{-1/2} Wh k φ(h_k)`, i.e. through
`Wh k Φ`. -/
lemma backwardSensitivity_congr_of_eqOn (d n0 n m : ℕ) (φ φ' : ℝ → ℝ)
    (X : Fin m → Fin n0 → ℝ) (θ θ' : DeepMLPParams d n0 n) (ℓ : Fin d)
    (hWd : θ.Wd = θ'.Wd)
    (hWh : ∀ k : Fin (d - 1), ℓ.val ≤ k.val → θ.Wh k = θ'.Wh k)
    (hh : ∀ k : Fin d, ℓ.val ≤ k.val →
      deepMLPPreactivation d n0 n m φ X θ k = deepMLPPreactivation d n0 n m φ X θ' k) :
    backwardSensitivity d n0 n m φ φ' X θ ℓ = backwardSensitivity d n0 n m φ φ' X θ' ℓ := by
  induction ℓ using backwardInduction with
  | top ℓ hℓ =>
    have hd : 0 < d := by have := ℓ.2; omega
    have heq : ℓ = ⟨d - 1, by omega⟩ := Fin.ext (by simp only; omega)
    have hh' := hh ℓ le_rfl
    rw [heq] at hh' ⊢
    funext α i
    rw [backwardSensitivity_top d n0 n m φ φ' X θ hd, backwardSensitivity_top d n0 n m φ φ' X θ' hd,
      hWd, hh']
  | step ℓ hℓ ih =>
    have hne : ℓ.val < d - 1 := by omega
    funext α i
    rw [backwardSensitivity_step d n0 n m φ φ' X θ ℓ hne,
      backwardSensitivity_step d n0 n m φ φ' X θ' ℓ hne]
    have hrec := ih (fun k hk => hWh k (by simp only at hk; omega))
      (fun k hk => hh k (by simp only at hk; omega))
    rw [hh ℓ le_rfl, hWh ⟨ℓ.val, by omega⟩ le_rfl]
    simp only [hrec]

/-- Empirical backward Gram matrix `G_{ℓ+1}^{(n)} ∈ ℝ^{m × m}` for `ℓ ∈ Fin (d + 1)`:
- `ℓ = 0, ..., d - 1`: hidden sensitivity covariance `(n : ℝ)⁻¹ • (g_ℓ^α ⬝ᵥ g_ℓ^β)`
- `ℓ = d`: terminal condition `G_{d+1}^{(n)} = 1_{m × m}` -/
noncomputable def deepSensitivityGram (d n0 n m : ℕ) (φ φ' : ℝ → ℝ) (X : Fin m → Fin n0 → ℝ)
    (θ : DeepMLPParams d n0 n) (ℓ : Fin (d + 1)) : Matrix (Fin m) (Fin m) ℝ :=
  if htop : ℓ.val = d then
    Matrix.of fun _ _ => 1
  else
    have hℓ : ℓ.val < d := by omega
    Matrix.of fun α β =>
      (n : ℝ)⁻¹ * (backwardSensitivity d n0 n m φ φ' X θ ⟨ℓ.val, hℓ⟩ α ⬝ᵥ
                   backwardSensitivity d n0 n m φ φ' X θ ⟨ℓ.val, hℓ⟩ β)

/-- The terminal backward Gram matrix (layer `d`) is the all-ones matrix. -/
lemma deepSensitivityGram_terminal (d n0 n m : ℕ) (φ φ' : ℝ → ℝ) (X : Fin m → Fin n0 → ℝ)
    (θ : DeepMLPParams d n0 n) :
    deepSensitivityGram d n0 n m φ φ' X θ ⟨d, by omega⟩ =
      Matrix.of fun _ _ => 1 := by
  ext α β
  simp [deepSensitivityGram]

/-- For a hidden layer `k < d` the backward Gram matrix is the Gram matrix `n⁻¹ ⟨g_k^α, g_k^β⟩` of
the sensitivities. -/
lemma deepSensitivityGram_hidden (d n0 n m : ℕ) (φ φ' : ℝ → ℝ) (X : Fin m → Fin n0 → ℝ)
    (θ : DeepMLPParams d n0 n) (k : ℕ) (hk : k < d) :
    deepSensitivityGram d n0 n m φ φ' X θ ⟨k, by omega⟩ =
      Matrix.of fun α β =>
        (n : ℝ)⁻¹ * (backwardSensitivity d n0 n m φ φ' X θ ⟨k, hk⟩ α ⬝ᵥ
                     backwardSensitivity d n0 n m φ φ' X θ ⟨k, hk⟩ β) := by
  ext α β
  rw [deepSensitivityGram]
  have htop : ¬ (⟨k, by omega⟩ : Fin (d + 1)).val = d := by
    intro h
    have : (⟨k, by omega⟩ : Fin (d + 1)).val = k := rfl
    omega
  simp only [htop, ↓reduceDIte, Matrix.of_apply]

/-- The empirical backward Gram matrix `G_{ℓ+1}^{(n)}` is symmetric. -/
theorem deepSensitivityGram_transpose (d n0 n m : ℕ) (φ φ' : ℝ → ℝ) (X : Fin m → Fin n0 → ℝ)
    (θ : DeepMLPParams d n0 n) (ℓ : Fin (d + 1)) :
    (deepSensitivityGram d n0 n m φ φ' X θ ℓ)ᵀ = deepSensitivityGram d n0 n m φ φ' X θ ℓ := by
  simp only [deepSensitivityGram]
  split_ifs
  · exact const_matrix_transpose 1
  · exact scaled_gram_transpose (n : ℝ)⁻¹ _

/-- The empirical backward Gram matrix `G_{ℓ+1}^{(n)}` is positive semidefinite. -/
theorem deepSensitivityGram_posSemidef (d n0 n m : ℕ) (φ φ' : ℝ → ℝ) (X : Fin m → Fin n0 → ℝ)
    (θ : DeepMLPParams d n0 n) (ℓ : Fin (d + 1)) :
    (deepSensitivityGram d n0 n m φ φ' X θ ℓ).PosSemidef := by
  simp only [deepSensitivityGram]
  split_ifs
  · exact posSemidef_allOnes
  · exact scaled_gram_posSemidef (n : ℝ)⁻¹ (by positivity) _

end NTK

end
