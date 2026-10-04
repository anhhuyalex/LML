/-
Copyright (c) 2025 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.NTK.Deep.LayerwiseNTK
public import LeanMachineLearning.Optimization.NTK.Initialization.FullNTK

/-!
# Limiting Deep Neural Tangent Kernel and Backward Recurrence (Proposition 2.27)

This file formalizes the infinite-width limiting Neural Tangent Kernel (NTK) Gram matrix
`deepLimitingNTK` and proves Proposition 2.27: the deterministic backward sensitivity recurrence,
global positive semidefiniteness, limiting Loewner order dominance over the NNGP kernel, and
exact consistency with the two-layer limiting NTK (`limitingFullNTKMatrix`).

## Mathematical Overview

For an MLP of architectural depth `d`, evaluation size `m`, activation `φ : ℝ → ℝ`, companion
weak derivative `φ' : ℝ → ℝ`, and base input Gram matrix `Φ₀ ∈ ℝ^{m × m}`:

1. **Forward Covariance Sequence** (`layerCovarianceSeq`):
   Directly reuses `layerCovarianceSeq 1 0 φ m Φ0` from `Initialization.CovariancePropagation`:
   - `Σ⁰ = Φ₀`
   - `Σ^{ℓ+1} = 𝒞_φ(Σ^ℓ)`

2. **Limiting Backward Covariance Tensor** (`deepLimitingSensitivityKernel`):
   Defined via the backward recurrence:
   - Terminal condition `ℓ = d`: `Π^d = 1_{m × m}`
   - Recurrence `ℓ < d`: `Π^ℓ = 𝒞_{φ'}(Σ^ℓ) ⊙ Π^{ℓ+1} = ⨀_{k=ℓ}^{d-1} 𝒞_{φ'}(Σ^k)`

3. **Limiting Deep NTK Matrix** (`deepLimitingNTK`):
   $$\mathbf{\Theta}^{(d)} := \sum_{\ell=0}^d \mathbf{\Pi}^{\ell+1} \odot \mathbf{\Sigma}^\ell$$
   where `Π^{ℓ+1}` is `deepLimitingSensitivityKernel d m φ φ' Φ0 ℓ`.

4. **Properties**:
   - **Positive Semidefiniteness** (`deepLimitingNTK_posSemidef`):
     `Θ^{(d)} ⪰ 0`, verified via `layerCovarianceSeq_posSemidef` and `Matrix.PosSemidef.hadamard`.
   - **Loewner Order Dominance** (`deepLimitingNTK_ge_nngp`):
     `Σ^d ≤ Θ^{(d)}` in Mathlib's canonical `MatrixOrder`, with difference
     `Θ^{(d)} - Σ^d = ∑_{ℓ < d} Π^{ℓ+1} ⊙ Σ^ℓ ⪰ 0`.
   - **Two-Layer Specialization** (`deepLimitingNTK_twoLayer_eq_add_hadamard`):
     At `d = 1` (a network with 2 weight layers: input and readout), `deepLimitingNTK` reduces to
     `Σ¹ + 𝒞_{φ'}(Φ₀) ⊙ Φ₀`, matching `limitingFullNTKMatrix`.
-/

@[expose]
public section

open scoped Matrix Real BigOperators MatrixOrder
open MeasureTheory ProbabilityTheory

namespace NTK

/-- Deterministic limiting backward sensitivity covariance tensor `Π^ℓ ∈ ℝ^{m × m}`
for `ℓ ∈ Fin (d + 1)` (Proposition 2.27):
- Terminal condition `ℓ = d`: `Π^d = 1_{m × m}`
- Backward recurrence `ℓ < d`: `Π^ℓ = 𝒞_{φ'}(Σ^ℓ) ⊙ Π^{ℓ+1}` where `Σ^ℓ` is the forward
  limiting covariance at layer `ℓ`, given by `layerCovarianceSeq 1 0 φ m Φ0 ℓ`. -/
noncomputable def deepLimitingSensitivityKernel (d m : ℕ) (φ φ' : ℝ → ℝ)
    (Φ0 : Matrix (Fin m) (Fin m) ℝ) : Fin (d + 1) → Matrix (Fin m) (Fin m) ℝ
  | ⟨ℓ, hℓ⟩ =>
      if htop : ℓ = d then
        Matrix.of fun _ _ => 1
      else
        have hsucc : ℓ + 1 < d + 1 := by omega
        let dotSigma : Matrix (Fin m) (Fin m) ℝ :=
          Matrix.of fun α β => ∫ z : EuclideanSpace ℝ (Fin m),
            φ' (z.ofLp α) * φ' (z.ofLp β) ∂(multivariateGaussian 0
              (layerCovarianceSeq 1 0 φ m Φ0 ℓ))
        dotSigma ⊙ deepLimitingSensitivityKernel d m φ φ' Φ0 ⟨ℓ + 1, hsucc⟩
termination_by ℓ => d - ℓ.val
decreasing_by omega

lemma deepLimitingSensitivityKernel_terminal (d m : ℕ) (φ φ' : ℝ → ℝ)
    (Φ0 : Matrix (Fin m) (Fin m) ℝ) :
    deepLimitingSensitivityKernel d m φ φ' Φ0 ⟨d, by omega⟩ =
      Matrix.of fun _ _ => 1 := by
  ext α β
  simp [deepLimitingSensitivityKernel]

lemma deepLimitingSensitivityKernel_step (d m : ℕ) (φ φ' : ℝ → ℝ)
    (Φ0 : Matrix (Fin m) (Fin m) ℝ) (ℓ : Fin (d + 1)) (hne : ℓ.val < d) :
    deepLimitingSensitivityKernel d m φ φ' Φ0 ℓ =
      (Matrix.of fun α β => ∫ z : EuclideanSpace ℝ (Fin m),
        φ' (z.ofLp α) * φ' (z.ofLp β) ∂(multivariateGaussian 0
          (layerCovarianceSeq 1 0 φ m Φ0 ℓ.val))) ⊙
      deepLimitingSensitivityKernel d m φ φ' Φ0 ⟨ℓ.val + 1, by omega⟩ := by
  rw [deepLimitingSensitivityKernel]
  have htop : ¬ ℓ.val = d := by omega
  simp [htop]

/-- The limiting backward covariance tensor is symmetric at every layer `ℓ`. -/
theorem deepLimitingSensitivityKernel_transpose (d m : ℕ) (φ φ' : ℝ → ℝ)
    (Φ0 : Matrix (Fin m) (Fin m) ℝ) (ℓ : Fin (d + 1)) :
    (deepLimitingSensitivityKernel d m φ φ' Φ0 ℓ)ᵀ =
      deepLimitingSensitivityKernel d m φ φ' Φ0 ℓ := by
  have H : ∀ k, ∀ (ℓ : Fin (d + 1)), d - ℓ.val = k →
      (deepLimitingSensitivityKernel d m φ φ' Φ0 ℓ)ᵀ =
        deepLimitingSensitivityKernel d m φ φ' Φ0 ℓ := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro ℓ hk
      rw [deepLimitingSensitivityKernel]
      split_ifs with htop
      · exact const_matrix_transpose 1
      · have hsucc : ℓ.val + 1 < d + 1 := by omega
        have h_ih := ih (d - (ℓ.val + 1)) (by omega) ⟨ℓ.val + 1, hsucc⟩ rfl
        have h_dot_trans :
            (Matrix.of fun α β => ∫ z : EuclideanSpace ℝ (Fin m),
              φ' (z.ofLp α) * φ' (z.ofLp β) ∂(multivariateGaussian 0
                (layerCovarianceSeq 1 0 φ m Φ0 ℓ.val)))ᵀ =
            (Matrix.of fun α β => ∫ z : EuclideanSpace ℝ (Fin m),
              φ' (z.ofLp α) * φ' (z.ofLp β) ∂(multivariateGaussian 0
                (layerCovarianceSeq 1 0 φ m Φ0 ℓ.val))) := by
          ext α β
          simp only [Matrix.transpose_apply, Matrix.of_apply]
          congr 1 with z
          ring
        simp only [Matrix.transpose_hadamard, h_dot_trans, h_ih]
  exact H (d - ℓ.val) ℓ rfl

/-- The limiting backward covariance matrix is positive semidefinite at every layer `ℓ`,
assuming `φ'` is measurable and has finite $L^2$ moments under the forward Gaussian layers. -/
theorem deepLimitingSensitivityKernel_posSemidef (d m : ℕ) (φ φ' : ℝ → ℝ)
    (hφ'_meas : Measurable φ') (Φ0 : Matrix (Fin m) (Fin m) ℝ)
    (hφ'_L2 : ∀ (k : ℕ) (α : Fin m),
      MemLp (fun z : EuclideanSpace ℝ (Fin m) => φ' (z.ofLp α)) 2
        (multivariateGaussian 0 (layerCovarianceSeq 1 0 φ m Φ0 k))) (ℓ : Fin (d + 1)) :
    (deepLimitingSensitivityKernel d m φ φ' Φ0 ℓ).PosSemidef := by
  have H : ∀ k, ∀ (ℓ : Fin (d + 1)), d - ℓ.val = k →
      (deepLimitingSensitivityKernel d m φ φ' Φ0 ℓ).PosSemidef := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro ℓ hk
      rw [deepLimitingSensitivityKernel]
      split_ifs with htop
      · exact posSemidef_allOnes (m := Fin m)
      · have hsucc : ℓ.val + 1 < d + 1 := by omega
        have h_rec := limitingRecurrence_posSemidef_multivariate 1 0 m φ' hφ'_meas
          (layerCovarianceSeq 1 0 φ m Φ0 ℓ.val) (hφ'_L2 ℓ.val)
        have h_dot_psd : (Matrix.of fun α β =>
            ∫ z : EuclideanSpace ℝ (Fin m), φ' (z.ofLp α) * φ' (z.ofLp β) ∂
              (multivariateGaussian 0 (layerCovarianceSeq 1 0 φ m Φ0 ℓ.val))).PosSemidef := by
          have heq : (Matrix.of fun α β =>
              ∫ z : EuclideanSpace ℝ (Fin m), φ' (z.ofLp α) * φ' (z.ofLp β) ∂
                (multivariateGaussian 0 (layerCovarianceSeq 1 0 φ m Φ0 ℓ.val))) =
            (show Matrix (Fin m) (Fin m) ℝ from fun α β => 0 ^ 2 + 1 ^ 2 *
              ∫ z : EuclideanSpace ℝ (Fin m), φ' (z.ofLp α) * φ' (z.ofLp β) ∂
                (multivariateGaussian 0 (layerCovarianceSeq 1 0 φ m Φ0 ℓ.val))) := by
            ext α β
            simp
          rw [heq]
          exact h_rec
        have h_tail := ih (d - (ℓ.val + 1)) (by omega) ⟨ℓ.val + 1, hsucc⟩ rfl
        exact Matrix.PosSemidef.hadamard h_dot_psd h_tail
  exact H (d - ℓ.val) ℓ rfl

/-- Deterministic limiting Neural Tangent Kernel (NTK) Gram matrix `Θ^{(d)} ∈ ℝ^{m × m}`
(Proposition 2.27):
`Θ^{(d)} = ∑_{ℓ=0}^d Π^{ℓ+1} ⊙ Σ^ℓ`.
Here `Σ^ℓ` is `layerCovarianceSeq 1 0 φ m Φ0 ℓ` and `Π^{ℓ+1}` is
`deepLimitingSensitivityKernel ... ℓ`. -/
noncomputable def deepLimitingNTK (d m : ℕ) (φ φ' : ℝ → ℝ)
    (Φ0 : Matrix (Fin m) (Fin m) ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  ∑ ℓ : Fin (d + 1),
    deepLimitingSensitivityKernel d m φ φ' Φ0 ℓ ⊙ layerCovarianceSeq 1 0 φ m Φ0 ℓ.val

/-- Equation lemma for the limiting deep NTK decomposition (Proposition 2.27). -/
theorem deepLimitingNTK_eq_sum_hadamard (d m : ℕ) (φ φ' : ℝ → ℝ)
    (Φ0 : Matrix (Fin m) (Fin m) ℝ) :
    deepLimitingNTK d m φ φ' Φ0 =
      ∑ ℓ : Fin (d + 1),
        deepLimitingSensitivityKernel d m φ φ' Φ0 ℓ ⊙ layerCovarianceSeq 1 0 φ m Φ0 ℓ.val :=
  rfl

/-- The limiting deep NTK matrix is symmetric. -/
theorem deepLimitingNTK_transpose (d m : ℕ) (φ φ' : ℝ → ℝ)
    (Φ0 : Matrix (Fin m) (Fin m) ℝ)
    (h_cov_symm : ∀ (k : ℕ),
      (layerCovarianceSeq 1 0 φ m Φ0 k)ᵀ = layerCovarianceSeq 1 0 φ m Φ0 k) :
    (deepLimitingNTK d m φ φ' Φ0)ᵀ = deepLimitingNTK d m φ φ' Φ0 := by
  simp only [deepLimitingNTK, Matrix.transpose_sum, Matrix.transpose_hadamard]
  congr 1 with ℓ
  rw [deepLimitingSensitivityKernel_transpose, h_cov_symm ℓ.val]

/-- Global positive semidefiniteness guarantee for the limiting deep NTK matrix
(Proposition 2.27). -/
theorem deepLimitingNTK_posSemidef (d m : ℕ) (φ φ' : ℝ → ℝ)
    (hφ_meas : Measurable φ) (hφ'_meas : Measurable φ')
    (Φ0 : Matrix (Fin m) (Fin m) ℝ) (hΦ0 : Φ0.PosSemidef)
    (hφ_L2 : ∀ (k : ℕ) (α : Fin m),
      MemLp (fun z => φ (z.ofLp α)) 2
        (multivariateGaussian 0 (layerCovarianceSeq 1 0 φ m Φ0 k)))
    (hφ'_L2 : ∀ (k : ℕ) (α : Fin m),
      MemLp (fun z => φ' (z.ofLp α)) 2
        (multivariateGaussian 0 (layerCovarianceSeq 1 0 φ m Φ0 k))) :
    (deepLimitingNTK d m φ φ' Φ0).PosSemidef := by
  rw [deepLimitingNTK]
  apply Matrix.posSemidef_sum
  intro ℓ _
  have hB := deepLimitingSensitivityKernel_posSemidef d m φ φ' hφ'_meas Φ0 hφ'_L2 ℓ
  have hF := layerCovarianceSeq_posSemidef 1 0 φ hφ_meas m Φ0 hΦ0 hφ_L2 ℓ.val
  exact Matrix.PosSemidef.hadamard hB hF

/-- Limiting Loewner order dominance over the NNGP kernel (Proposition 2.27):
`Σ^d ≤ Θ^{(d)}`.
The difference `Θ^{(d)} - Σ^d = ∑_{ℓ < d} Π^{ℓ+1} ⊙ Σ^ℓ` is positive semidefinite. -/
theorem deepLimitingNTK_ge_nngp (d m : ℕ) (φ φ' : ℝ → ℝ)
    (hφ_meas : Measurable φ) (hφ'_meas : Measurable φ')
    (Φ0 : Matrix (Fin m) (Fin m) ℝ) (hΦ0 : Φ0.PosSemidef)
    (hφ_L2 : ∀ (k : ℕ) (α : Fin m),
      MemLp (fun z => φ (z.ofLp α)) 2
        (multivariateGaussian 0 (layerCovarianceSeq 1 0 φ m Φ0 k)))
    (hφ'_L2 : ∀ (k : ℕ) (α : Fin m),
      MemLp (fun z => φ' (z.ofLp α)) 2
        (multivariateGaussian 0 (layerCovarianceSeq 1 0 φ m Φ0 k))) :
    layerCovarianceSeq 1 0 φ m Φ0 d ≤ deepLimitingNTK d m φ φ' Φ0 := by
  rw [Matrix.le_iff]
  have hsplit : deepLimitingNTK d m φ φ' Φ0 =
      (∑ ℓ : Fin d,
        deepLimitingSensitivityKernel d m φ φ' Φ0 ℓ.castSucc ⊙
        layerCovarianceSeq 1 0 φ m Φ0 ℓ.castSucc.val) +
      layerCovarianceSeq 1 0 φ m Φ0 d := by
    rw [deepLimitingNTK]
    have h_sum := Fin.sum_univ_castSucc
      (fun ℓ : Fin (d + 1) => deepLimitingSensitivityKernel d m φ φ' Φ0 ℓ ⊙
        layerCovarianceSeq 1 0 φ m Φ0 ℓ.val)
    rw [h_sum]
    congr 1
    have hterm := deepLimitingSensitivityKernel_terminal d m φ φ' Φ0
    have hd : (Fin.last d).val = d := rfl
    have hlast : deepLimitingSensitivityKernel d m φ φ' Φ0 (Fin.last d) ⊙
        layerCovarianceSeq 1 0 φ m Φ0 (Fin.last d).val =
        layerCovarianceSeq 1 0 φ m Φ0 d := by
      have hlast_eq : deepLimitingSensitivityKernel d m φ φ' Φ0 (Fin.last d) =
          Matrix.of fun _ _ => 1 := by
        have : (Fin.last d) = ⟨d, by omega⟩ := rfl
        rw [this, hterm]
      rw [hd, hlast_eq, allOnes_hadamard]
    exact hlast
  rw [hsplit, add_sub_cancel_right]
  apply Matrix.posSemidef_sum
  intro ℓ _
  have hB := deepLimitingSensitivityKernel_posSemidef d m φ φ' hφ'_meas Φ0 hφ'_L2 ℓ.castSucc
  have hF := layerCovarianceSeq_posSemidef 1 0 φ hφ_meas m Φ0 hΦ0 hφ_L2 ℓ.castSucc.val
  exact Matrix.PosSemidef.hadamard hB hF

/-- Two-layer specialization: at architectural depth `d = 1`, the limiting NTK matrix
`Θ^{(1)} = Σ¹ + 𝒞_{φ'}(Φ₀) ⊙ Φ₀`, recovering the two-layer full NTK decomposition. -/
theorem deepLimitingNTK_twoLayer_eq_add_hadamard (m : ℕ) (φ φ' : ℝ → ℝ)
    (Φ0 : Matrix (Fin m) (Fin m) ℝ) :
    deepLimitingNTK 1 m φ φ' Φ0 =
      layerCovarianceSeq 1 0 φ m Φ0 1 +
        (Matrix.of fun α β => ∫ z : EuclideanSpace ℝ (Fin m),
          φ' (z.ofLp α) * φ' (z.ofLp β) ∂(multivariateGaussian 0 Φ0)) ⊙ Φ0 := by
  rw [deepLimitingNTK, Fin.sum_univ_two]
  have h0 : deepLimitingSensitivityKernel 1 m φ φ' Φ0 0 =
      (Matrix.of fun α β => ∫ z : EuclideanSpace ℝ (Fin m),
        φ' (z.ofLp α) * φ' (z.ofLp β) ∂(multivariateGaussian 0 Φ0)) := by
    have hstep := deepLimitingSensitivityKernel_step 1 m φ φ' Φ0 0 (by decide)
    rw [hstep]
    have hterm : deepLimitingSensitivityKernel 1 m φ φ' Φ0 ⟨(0 : Fin 2).val + 1, by omega⟩ =
        Matrix.of fun _ _ => 1 := by
      have : (⟨(0 : Fin 2).val + 1, by omega⟩ : Fin 2) = ⟨1, by omega⟩ := rfl
      rw [this]
      exact deepLimitingSensitivityKernel_terminal 1 m φ φ' Φ0
    rw [hterm, hadamard_allOnes]
    rfl
  have h1 : deepLimitingSensitivityKernel 1 m φ φ' Φ0 1 =
      Matrix.of fun _ _ => 1 := by
    have : (1 : Fin 2) = ⟨1, by omega⟩ := rfl
    rw [this]
    exact deepLimitingSensitivityKernel_terminal 1 m φ φ' Φ0
  have hcov0 : layerCovarianceSeq 1 0 φ m Φ0 (0 : Fin 2).val = Φ0 := rfl
  have hcov1 : layerCovarianceSeq 1 0 φ m Φ0 (1 : Fin 2).val =
      layerCovarianceSeq 1 0 φ m Φ0 1 := rfl
  rw [h0, h1, hcov0, hcov1, allOnes_hadamard, add_comm]

end NTK

end
