/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Probability.Moments.GaussianPiLinearForm
public import LeanMachineLearning.SpinGlasses.Talagrand.Perceptron.SmartPathModel

/-!
# Covariance relations of the cavity family

Talagrand Section 2.3, (2.50)--(2.51) and the identification of `R^t`.

All random variables of the interpolation are linear forms in one vector `w` of i.i.d. standard
Gaussians, indexed by `κ₀ ⊕ (Unit ⊕ (R ⊕ R))`: the old part `κ₀` (the couplings `g_{i,M}` and
`g_{N,M}` of the removed constraint), the shared `z`, the `ξ_M^ℓ` and the `ξ^ℓ`. A linear form is
given by its coefficient vector `cavityVec α b c e ℓ`: the coefficients `α` on `κ₀`, `b` on `z`,
`c` on `ξ_M^ℓ` and `e` on `ξ^ℓ`. By `integral_dotProduct_mul_dotProduct_pi_gaussianReal` the
covariance of two such forms is the dot product of their coefficient vectors
(`cavityVec_dotProduct`).

With `s` the path parameter (`cos s = √v`), `a₀ = √((1-t)/(N+1))` and `α_σ` the coefficients of the
quenched part of `S_{M,t}(σ)`:

* `S^ℓ_σ = cavityVec α_σ 0 a₀ 0 ℓ`, `θ^ℓ = cavityVec 0 √q 0 √(1-q) ℓ`,
* `z^ℓ_σ = cos s S^ℓ_σ + sin s θ^ℓ` and its `s`-derivative `z̃^ℓ_σ = -sin s S^ℓ_σ + cos s θ^ℓ`
  (the book's `z'` is `-z̃ / (2 sin s cos s)`),
* `y_σ = cos s S_σ + sin s √q z` (the part of `z^ℓ_σ` free of the `ξ`-labelled variables).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace SpinGlasses

variable {κ₀ R : Type*} [Fintype κ₀] [Fintype R] [DecidableEq R]

/-- Coefficient vector of the linear form `α · g + b z + c ξ_M^ℓ + e ξ^ℓ` in the i.i.d. Gaussian
vector of the cavity interpolation. -/
noncomputable def cavityVec (α : κ₀ → ℝ) (b c e : ℝ) (ℓ : R) : κ₀ ⊕ (Unit ⊕ (R ⊕ R)) → ℝ :=
  Sum.elim α (Sum.elim (fun _ => b) (Sum.elim (Pi.single ℓ c) (Pi.single ℓ e)))

/-- **Covariance of two cavity linear forms.** Forms with different replica labels share only the
old part and the common `z`. -/
theorem cavityVec_dotProduct (α α' : κ₀ → ℝ) (b b' c c' e e' : ℝ) (ℓ ℓ' : R) :
    cavityVec α b c e ℓ ⬝ᵥ cavityVec α' b' c' e' ℓ' =
      α ⬝ᵥ α' + b * b' + if ℓ = ℓ' then c * c' + e * e' else 0 := by
  simp only [dotProduct, cavityVec, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    Finset.univ_unique, Finset.sum_const, Finset.card_singleton, one_smul, Pi.single_apply,
    mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  by_cases h : ℓ = ℓ'
  · subst h
    simp [add_assoc]
  · simp [h, Ne.symm h]

section Relations

variable {s q a₀ : ℝ} (α₁ α₂ : κ₀ → ℝ) (ℓ ℓ' : R)

/-- **`E (θ^ℓ)² = 1`** and, for `ℓ ≠ ℓ'`, **`E θ^ℓ θ^ℓ' = q`** (below (2.49)), for `q ∈ [0, 1]`. -/
theorem cavity_theta_dot_theta (hq : q ∈ Set.Icc (0 : ℝ) 1) :
    cavityVec (0 : κ₀ → ℝ) (Real.sqrt q) 0 (Real.sqrt (1 - q)) ℓ ⬝ᵥ
      cavityVec 0 (Real.sqrt q) 0 (Real.sqrt (1 - q)) ℓ' = if ℓ = ℓ' then 1 else q := by
  rw [cavityVec_dotProduct]
  have h1 := Real.mul_self_sqrt hq.1
  have h2 := Real.mul_self_sqrt (sub_nonneg.2 hq.2)
  by_cases h : ℓ = ℓ' <;> simp [h, h1, h2]

/-- **(2.50), distinct replicas.** For `ℓ ≠ ℓ'`,
`E z̃^ℓ_σ z^{ℓ'}_τ = sin s cos s (q - C(σ,τ))` with `C(σ,τ) = α_σ ⬝ α_τ` the covariance of the
quenched parts; here `z̃ = -sin s S + cos s θ` is the `s`-derivative of `z = cos s S + sin s θ`. -/
theorem cavity_zTilde_dot_z_of_ne (hq : q ∈ Set.Icc (0 : ℝ) 1) (hℓ : ℓ ≠ ℓ') :
    cavityVec ((-Real.sin s) • α₁) (Real.cos s * Real.sqrt q) (-Real.sin s * a₀)
        (Real.cos s * Real.sqrt (1 - q)) ℓ ⬝ᵥ
      cavityVec (Real.cos s • α₂) (Real.sin s * Real.sqrt q) (Real.cos s * a₀)
        (Real.sin s * Real.sqrt (1 - q)) ℓ' =
      Real.sin s * Real.cos s * (q - α₁ ⬝ᵥ α₂) := by
  have h1 := Real.mul_self_sqrt hq.1
  rw [cavityVec_dotProduct, smul_dotProduct, dotProduct_smul]
  simp only [smul_eq_mul, hℓ, ↓reduceIte]
  linear_combination (Real.cos s * Real.sin s) * h1

/-- **(2.50), the same replica.** For every `σ, τ`,
`E z̃^ℓ_σ z^ℓ_τ = sin s cos s (1 - C(σ,τ) - a₀²)`; in particular `E z̃^ℓ_σ z^ℓ_σ = 0` when the
variance of `S_{M,t}` is `C(σ,σ) + a₀² = 1`. -/
theorem cavity_zTilde_dot_z_same (hq : q ∈ Set.Icc (0 : ℝ) 1) :
    cavityVec ((-Real.sin s) • α₁) (Real.cos s * Real.sqrt q) (-Real.sin s * a₀)
        (Real.cos s * Real.sqrt (1 - q)) ℓ ⬝ᵥ
      cavityVec (Real.cos s • α₂) (Real.sin s * Real.sqrt q) (Real.cos s * a₀)
        (Real.sin s * Real.sqrt (1 - q)) ℓ =
      Real.sin s * Real.cos s * (1 - (α₁ ⬝ᵥ α₂ + a₀ ^ 2)) := by
  have h1 := Real.mul_self_sqrt hq.1
  have h2 := Real.mul_self_sqrt (sub_nonneg.2 hq.2)
  rw [cavityVec_dotProduct, smul_dotProduct, dotProduct_smul]
  simp only [smul_eq_mul, ↓reduceIte]
  linear_combination (Real.cos s * Real.sin s) * h1 + (Real.cos s * Real.sin s) * h2

/-- **(2.51).** `E z̃^ℓ_σ y_τ = sin s cos s (q - C(σ,τ))` for all replica labels, where
`y_τ = cos s S_τ + sin s √q z` is the part of `z^ℓ_τ` free of the `ξ`-labelled variables. -/
theorem cavity_zTilde_dot_y (hq : q ∈ Set.Icc (0 : ℝ) 1) :
    cavityVec ((-Real.sin s) • α₁) (Real.cos s * Real.sqrt q) (-Real.sin s * a₀)
        (Real.cos s * Real.sqrt (1 - q)) ℓ ⬝ᵥ
      cavityVec (Real.cos s • α₂) (Real.sin s * Real.sqrt q) 0 0 ℓ' =
      Real.sin s * Real.cos s * (q - α₁ ⬝ᵥ α₂) := by
  have h1 := Real.mul_self_sqrt hq.1
  rw [cavityVec_dotProduct, smul_dotProduct, dotProduct_smul]
  simp only [smul_eq_mul, mul_zero, add_zero, ite_self]
  linear_combination (Real.cos s * Real.sin s) * h1

/-- **Constant variance of `z`.** If `C(σ,σ) + a₀² = 1` and `q ∈ [0,1]` then `E (z^ℓ_σ)² = 1`. -/
theorem cavity_z_dot_z_same (hq : q ∈ Set.Icc (0 : ℝ) 1) (hC : α₁ ⬝ᵥ α₁ + a₀ ^ 2 = 1) :
    cavityVec (Real.cos s • α₁) (Real.sin s * Real.sqrt q) (Real.cos s * a₀)
        (Real.sin s * Real.sqrt (1 - q)) ℓ ⬝ᵥ
      cavityVec (Real.cos s • α₁) (Real.sin s * Real.sqrt q) (Real.cos s * a₀)
        (Real.sin s * Real.sqrt (1 - q)) ℓ = 1 := by
  have h1 := Real.mul_self_sqrt hq.1
  have h2 := Real.mul_self_sqrt (sub_nonneg.2 hq.2)
  rw [cavityVec_dotProduct, smul_dotProduct, dotProduct_smul]
  simp only [smul_eq_mul, ↓reduceIte]
  have hs := Real.sin_sq_add_cos_sq s
  linear_combination (Real.cos s ^ 2) * hC + (Real.sin s ^ 2) * h1 + (Real.sin s ^ 2) * h2 + hs

end Relations

section Perceptron

variable {N M : ℕ} {t : ℝ}

/-- Coefficients of the quenched part of `S_{M,t}(σ)` in the removed constraint's Gaussians
`(g_{i,M})_{i<N}` and `g_{N,M}` (indexed by `Fin N ⊕ Unit`). -/
noncomputable def cavityCoef (N : ℕ) (t : ℝ) (σ : PerceptronSpin N) : Fin N ⊕ Unit → ℝ :=
  Sum.elim (fun i => (Real.sqrt (N + 1 : ℕ))⁻¹ * ((σ.1 i : ℤ) : ℝ))
    (fun _ => Real.sqrt (t / (N + 1)) * ((σ.2 : ℤ) : ℝ))

/-- The field of the removed constraint is the linear form `cavityCoef · (g, a)` of its Gaussian
couplings plus the auxiliary term `√((1-t)/(N+1)) ξ_M`. -/
theorem smartPathField_last_eq_dotProduct (ω : SmartPathDisorder N (M + 1))
    (x : SmartPathState N (M + 1)) :
    smartPathField t ω x (Fin.last M) =
      cavityCoef N t x.1 ⬝ᵥ Sum.elim (ω.1.1 (Fin.last M)) (fun _ => ω.1.2 (Fin.last M)) +
        Real.sqrt ((1 - t) / (N + 1)) * x.2 (Fin.last M) := by
  simp only [smartPathField_eq, smartPathFieldNoAux_eq, dotProduct, cavityCoef,
    Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Finset.univ_unique, Finset.sum_const,
    Finset.card_singleton, one_smul]
  have hs : (Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω.1.1 (Fin.last M) i * ((x.1.1 i : ℤ) : ℝ) =
      ∑ i, (Real.sqrt (N + 1 : ℕ))⁻¹ * ((x.1.1 i : ℤ) : ℝ) * ω.1.1 (Fin.last M) i := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hs]
  ring

/-- **The covariance `R^t`.** `E S_{M,t}(σ) S_{M,t}(τ) = R^t(σ, τ)` is the dot product of the
coefficient vectors: `(Σ_{i<N} σ_i τ_i + t σ_N τ_N) / (N + 1)`, for `0 ≤ t`. -/
theorem cavityCoef_dotProduct (ht : 0 ≤ t) (σ τ : PerceptronSpin N) :
    cavityCoef N t σ ⬝ᵥ cavityCoef N t τ =
      ((∑ i, ((σ.1 i : ℤ) : ℝ) * ((τ.1 i : ℤ) : ℝ)) + t * (((σ.2 : ℤ) : ℝ) * ((τ.2 : ℤ) : ℝ))) /
        (N + 1) := by
  have h1 : (Real.sqrt (N + 1 : ℕ))⁻¹ * (Real.sqrt (N + 1 : ℕ))⁻¹ = 1 / (N + 1) := by
    rw [← mul_inv, Real.mul_self_sqrt (Nat.cast_nonneg _)]
    push_cast
    simp
  have h2 : Real.sqrt (t / (N + 1)) * Real.sqrt (t / (N + 1)) = t / (N + 1) :=
    Real.mul_self_sqrt (div_nonneg ht (by positivity))
  simp only [dotProduct, cavityCoef, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    Finset.univ_unique, Finset.sum_const, Finset.card_singleton, one_smul]
  have e1 : ∀ i : Fin N, (Real.sqrt (N + 1 : ℕ))⁻¹ * ((σ.1 i : ℤ) : ℝ) *
      ((Real.sqrt (N + 1 : ℕ))⁻¹ * ((τ.1 i : ℤ) : ℝ)) =
      (1 / (N + 1)) * (((σ.1 i : ℤ) : ℝ) * ((τ.1 i : ℤ) : ℝ)) := fun i => by
    linear_combination (((σ.1 i : ℤ) : ℝ) * ((τ.1 i : ℤ) : ℝ)) * h1
  simp_rw [e1, ← Finset.mul_sum]
  have e2 : Real.sqrt (t / (N + 1)) * ((σ.2 : ℤ) : ℝ) *
      (Real.sqrt (t / (N + 1)) * ((τ.2 : ℤ) : ℝ)) =
      t / (N + 1) * (((σ.2 : ℤ) : ℝ) * ((τ.2 : ℤ) : ℝ)) := by
    linear_combination (((σ.2 : ℤ) : ℝ) * ((τ.2 : ℤ) : ℝ)) * h2
  rw [e2]
  field_simp

/-- **Constant variance of `S_{M,t}`.** For `t ∈ [0,1]`, `C(σ,σ) + a₀² = 1` with
`a₀² = (1 - t)/(N + 1)`, so that `E S_{M,t}(σ, ξ_M)² = 1`. -/
theorem cavityCoef_dotProduct_self_add (ht : t ∈ Set.Icc (0 : ℝ) 1) (σ : PerceptronSpin N) :
    cavityCoef N t σ ⬝ᵥ cavityCoef N t σ + Real.sqrt ((1 - t) / (N + 1)) ^ 2 = 1 := by
  rw [cavityCoef_dotProduct ht.1, Real.sq_sqrt (div_nonneg (sub_nonneg.2 ht.2) (by positivity))]
  have hs : ∀ i : Fin N, ((σ.1 i : ℤ) : ℝ) * ((σ.1 i : ℤ) : ℝ) = 1 := fun i => by
    rw [← sq]; exact units_cast_sq _
  have hε : ((σ.2 : ℤ) : ℝ) * ((σ.2 : ℤ) : ℝ) = 1 := by rw [← sq]; exact units_cast_sq _
  simp only [hs, hε, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  field_simp
  ring

/-- **`R^t - R = (t - 1) ε ε' / (N + 1)`**, hence **`|R^t - R| ≤ 1/(N + 1)`** for `t ∈ [0,1]`, where
`R(σ,τ) = (Σ_{i<N} σ_i τ_i + ε ε')/(N + 1)` is the overlap of the full spins. -/
theorem abs_cavityCoef_dotProduct_sub_overlap_le (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (σ τ : PerceptronSpin N) :
    |cavityCoef N t σ ⬝ᵥ cavityCoef N t τ -
        ((∑ i, ((σ.1 i : ℤ) : ℝ) * ((τ.1 i : ℤ) : ℝ)) +
          ((σ.2 : ℤ) : ℝ) * ((τ.2 : ℤ) : ℝ)) / (N + 1)| ≤ 1 / (N + 1) := by
  rw [cavityCoef_dotProduct ht.1]
  have hεε : |((σ.2 : ℤ) : ℝ) * ((τ.2 : ℤ) : ℝ)| = 1 := by
    rw [abs_mul, abs_units_cast_eq_one, abs_units_cast_eq_one, mul_one]
  have hN : (0 : ℝ) < N + 1 := by positivity
  have : ((∑ i, ((σ.1 i : ℤ) : ℝ) * ((τ.1 i : ℤ) : ℝ)) +
        t * (((σ.2 : ℤ) : ℝ) * ((τ.2 : ℤ) : ℝ))) / (N + 1) -
      ((∑ i, ((σ.1 i : ℤ) : ℝ) * ((τ.1 i : ℤ) : ℝ)) +
          ((σ.2 : ℤ) : ℝ) * ((τ.2 : ℤ) : ℝ)) / (N + 1) =
      (t - 1) * (((σ.2 : ℤ) : ℝ) * ((τ.2 : ℤ) : ℝ)) / (N + 1) := by ring
  rw [this, abs_div, abs_of_pos hN, abs_mul, hεε, mul_one, abs_of_nonpos (by linarith [ht.2])]
  exact div_le_div_of_nonneg_right (by linarith [ht.1]) hN.le

end Perceptron

end SpinGlasses
