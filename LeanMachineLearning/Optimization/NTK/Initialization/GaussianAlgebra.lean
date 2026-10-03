/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.NTK.Initialization.Setup

/-!
# Gaussian vector algebra (Propositions 2.8-2.10)

Algebraic facts about jointly Gaussian vectors used by the conditional-normality argument.

## Main results and proof outline

  * The `Fin m`-family generalizations of Propositions 2.9-2.10 from a fixed pair of vectors to
    a fixed family (`NTK.stdGaussian_inner_family`, `NTK.gaussianMatrix_mulVec_family`), giving
    the row-indexed (neuron-indexed) family of $n'$ i.i.d. copies of the single-neuron
    $m$-variate Gaussian $\mathcal{N}(\mathbf{0}, \boldsymbol{\Phi}_\ell^{(n)})$.
* Proposition 2.8: a linear image `A g` of a Gaussian vector `g ~ 𝒩(μ, S)` is again Gaussian,
  `A g ~ 𝒩(A μ, A S Aᵀ)` (`NTK.gaussian_map_mulVec`).
* Proposition 2.9: for `g ~ 𝒩(0, I_n)` and fixed `u, v : Fin n → ℝ`, the joint law of
  `(⟪g,u⟫, ⟪g,v⟫)` is the bivariate Gaussian with covariance
  `!![u⬝ᵥu, u⬝ᵥv; u⬝ᵥv, v⬝ᵥv]` (`NTK.stdGaussian_inner_pair`), proved as a corollary of
  Proposition 2.8.
* Proposition 2.10: for a matrix `W` with i.i.d. standard Gaussian entries, the row-indexed
  family `i ↦ (W i ⬝ᵥ u, W i ⬝ᵥ v)` consists of `n` i.i.d. copies of Proposition 2.9's
  bivariate Gaussian (`NTK.gaussianMatrix_mulVec_pair`), proved by pushing the row-product
  measure `gaussianInit n n` forward row-by-row via `Measure.pi_map_pi`.
* Propositions 2.9' and 2.10': the direct `Fin m`-indexed generalizations of Propositions 2.9
  and 2.10 from a fixed pair of vectors to a fixed family `u : Fin m → Fin n → ℝ`
  (`NTK.stdGaussian_inner_family`, `NTK.gaussianMatrix_mulVec_family`), proved by the same
  techniques; used by the Layer-by-Layer Conditional Gaussian Structure below.
* `NTK.inner_eq_dotProduct_ofLp` : the real `EuclideanSpace` inner product is the `dotProduct`
  of the underlying coordinate functions.
* `NTK.gaussian_map_mulVec` : Proposition 2.8, `A g ~ 𝒩(A μ, A S Aᵀ)` for a linear image of a
  Gaussian vector.
* `NTK.stdGaussian_inner_pair` : Proposition 2.9, the joint law of `(⟪g,u⟫, ⟪g,v⟫)` for
  `g ~ 𝒩(0, I_n)`.
* `NTK.gaussianMatrix_mulVec_pair` : Proposition 2.10, the row-indexed joint law of
  `(W ⬝ᵥ u, W ⬝ᵥ v)` for an i.i.d. Gaussian matrix `W`.
* `NTK.stdGaussian_inner_family`, `NTK.gaussianMatrix_mulVec_family` : the `Fin m`-family
  generalizations of Propositions 2.9-2.10.

See
`LeanMachineLearning.Optimization.NTK.Initialization`
for the overview of the whole development.
-/

@[expose] public section

set_option linter.style.longLine false

open Real MeasureTheory ProbabilityTheory Matrix Complex
open scoped BigOperators MatrixOrder RealInnerProductSpace Kronecker ENNReal

namespace NTK

variable {d n m : ℕ}

section GaussianVectorAlgebra

/-! ## Gaussian Vector Algebra (Propositions 2.8-2.10) -/

/-- The real inner product on any finite-dimensional `EuclideanSpace` is the `dotProduct` of the
underlying coordinate functions. -/
lemma inner_eq_dotProduct_ofLp {γ : Type*} [Fintype γ] (a b : EuclideanSpace ℝ γ) :
    ⟪a, b⟫ = a.ofLp ⬝ᵥ b.ofLp := by
  simp only [PiLp.inner_apply, RCLike.inner_apply', conj_trivial, dotProduct]

/-- **Proposition 2.8 (Linear Transformations of Gaussian Vectors)**:
If `g ~ 𝒩(μ, S)` on `EuclideanSpace ℝ ι` and `A` is a deterministic `κ × ι` matrix, then the
linear image `A g` is again Gaussian: `A g ~ 𝒩(A μ, A S Aᵀ)`. -/
theorem gaussian_map_mulVec {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (μ : EuclideanSpace ℝ ι) (S : Matrix ι ι ℝ) (hS : S.PosSemidef) (A : Matrix κ ι ℝ) :
    Measure.map (fun x : EuclideanSpace ℝ ι => WithLp.toLp 2 (A *ᵥ x.ofLp))
        (multivariateGaussian μ S) =
      multivariateGaussian (WithLp.toLp 2 (A *ᵥ μ.ofLp)) (A * S * Aᵀ) := by
  have hAST : (A * S * Aᵀ).PosSemidef := by simpa using hS.mul_mul_conjTranspose_same A
  set F := fun x : EuclideanSpace ℝ ι => WithLp.toLp 2 (A *ᵥ x.ofLp) with hF_def
  have hF_cont : Continuous F :=
    (PiLp.continuous_toLp 2 _).comp (continuous_pi fun k => continuous_finsetSum _ fun j _ =>
      continuous_const.mul (PiLp.continuous_apply 2 _ j))
  apply Measure.ext_of_charFun
  ext t
  rw [charFun_apply, integral_map hF_cont.measurable.aemeasurable (by fun_prop)]
  have h_inner : ∀ x : EuclideanSpace ℝ ι, ⟪F x, t⟫ = x.ofLp ⬝ᵥ (Aᵀ *ᵥ t.ofLp) := by
    intro x
    rw [real_inner_comm, inner_eq_dotProduct_ofLp]
    rw [dotProduct_mulVec, ← mulVec_transpose, dotProduct_comm]
  simp_rw [h_inner]
  have h_as_charFun : (∫ x : EuclideanSpace ℝ ι,
      Complex.exp ((x.ofLp ⬝ᵥ (Aᵀ *ᵥ t.ofLp) : ℝ) * Complex.I) ∂(multivariateGaussian μ S)) =
      charFun (multivariateGaussian μ S) (WithLp.toLp 2 (Aᵀ *ᵥ t.ofLp)) := by
    rw [charFun_apply]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [inner_eq_dotProduct_ofLp]
  rw [h_as_charFun, charFun_multivariateGaussian hS, charFun_multivariateGaussian hAST]
  have h_mean : ⟪(WithLp.toLp 2 (Aᵀ *ᵥ t.ofLp) : EuclideanSpace ℝ ι), μ⟫ =
      ⟪t, (WithLp.toLp 2 (A *ᵥ μ.ofLp) : EuclideanSpace ℝ κ)⟫ := by
    rw [inner_eq_dotProduct_ofLp, inner_eq_dotProduct_ofLp]
    conv_rhs => rw [dotProduct_mulVec, ← mulVec_transpose]
  have h_quad : (Aᵀ *ᵥ t.ofLp) ⬝ᵥ S *ᵥ (Aᵀ *ᵥ t.ofLp) = t.ofLp ⬝ᵥ (A * S * Aᵀ) *ᵥ t.ofLp := by
    conv_rhs => rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, ← mulVec_transpose]
  rw [h_mean, h_quad]

/-- **Proposition 2.9 (Inner Products with a Standard Gaussian Vector)**:
For `g ~ 𝒩(0, I_n)` (`gaussianReadoutMeasure n`) and fixed deterministic vectors `u v : Fin n → ℝ`,
the joint law of the pair of projections `(⟪g,u⟫, ⟪g,v⟫) = (g ⬝ᵥ u, g ⬝ᵥ v)` is the bivariate
Gaussian with covariance matrix `!![u ⬝ᵥ u, u ⬝ᵥ v; u ⬝ᵥ v, v ⬝ᵥ v]`. -/
theorem stdGaussian_inner_pair (n : ℕ) (u v : Fin n → ℝ) :
    Measure.map (fun a : Fin n → ℝ => WithLp.toLp 2 (![a ⬝ᵥ u, a ⬝ᵥ v] : Fin 2 → ℝ))
        (Measure.pi fun _ : Fin n => gaussianReal 0 1) =
      multivariateGaussian 0 !![u ⬝ᵥ u, u ⬝ᵥ v; u ⬝ᵥ v, v ⬝ᵥ v] := by
  set A : Matrix (Fin 2) (Fin n) ℝ := Matrix.of ![u, v] with hA_def
  have hA_mulVec : ∀ a : Fin n → ℝ, A *ᵥ a = ![a ⬝ᵥ u, a ⬝ᵥ v] := by
    intro a
    ext i
    fin_cases i <;> simp [A, mulVec, dotProduct, mul_comm]
  have hF_eq : (fun a : Fin n → ℝ => WithLp.toLp 2 (![a ⬝ᵥ u, a ⬝ᵥ v] : Fin 2 → ℝ)) =
      (fun x : EuclideanSpace ℝ (Fin n) => WithLp.toLp 2 (A *ᵥ x.ofLp)) ∘ (WithLp.toLp 2) := by
    ext a
    simp [hA_mulVec]
  have hSpos : (1 : Matrix (Fin n) (Fin n) ℝ).PosSemidef := Matrix.PosSemidef.one
  have h_map := gaussian_map_mulVec (0 : EuclideanSpace ℝ (Fin n)) 1 hSpos A
  rw [hF_eq, ← Measure.map_map (by fun_prop) (by fun_prop)]
  have h_toLp : Measure.map (WithLp.toLp 2) (Measure.pi fun _ : Fin n => gaussianReal 0 1) =
      multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) 1 := by
    rw [map_pi_eq_stdGaussian, multivariateGaussian_zero_one]
  rw [h_toLp, h_map]
  have h_mean0 : A *ᵥ (0 : EuclideanSpace ℝ (Fin n)).ofLp = (0 : Fin 2 → ℝ) := by simp
  have h_cov : A * (1 : Matrix (Fin n) (Fin n) ℝ) * Aᵀ =
      !![u ⬝ᵥ u, u ⬝ᵥ v; u ⬝ᵥ v, v ⬝ᵥ v] := by
    rw [Matrix.mul_one]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [A, Matrix.mul_apply, Matrix.transpose_apply, dotProduct, mul_comm]
  rw [h_mean0, h_cov]
  simp

/-- **Proposition 2.10 (Matrix-Vector Multiplication by a Gaussian Matrix)**:
For `W : Fin n → Fin n → ℝ` with i.i.d. standard Gaussian entries (`gaussianInit n n`) and fixed
deterministic vectors `u v : Fin n → ℝ`, the joint law of the row-indexed pairs
`i ↦ (W i ⬝ᵥ u, W i ⬝ᵥ v) = i ↦ ((W *ᵥ u) i, (W *ᵥ v) i)` consists of `n` i.i.d. copies of the
bivariate Gaussian from Proposition 2.9, i.e. the block/Kronecker-structured covariance
`!![u ⬝ᵥ u, u ⬝ᵥ v; u ⬝ᵥ v, v ⬝ᵥ v] ⊗ Iₙ`. -/
theorem gaussianMatrix_mulVec_pair (n : ℕ) (u v : Fin n → ℝ) :
    Measure.map
      (fun W : Fin n → Fin n → ℝ =>
        fun i : Fin n => WithLp.toLp 2 (![W i ⬝ᵥ u, W i ⬝ᵥ v] : Fin 2 → ℝ))
      (Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin n => gaussianReal 0 1) =
      Measure.pi (fun _ : Fin n => multivariateGaussian 0 !![u ⬝ᵥ u, u ⬝ᵥ v; u ⬝ᵥ v, v ⬝ᵥ v]) := by
  have h_init_eq : (Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin n =>
      gaussianReal 0 1) = Measure.pi (fun _ : Fin n => (Measure.pi fun _ : Fin n =>
      gaussianReal 0 1)) := rfl
  set f := fun a : Fin n → ℝ => WithLp.toLp 2 (![a ⬝ᵥ u, a ⬝ᵥ v] : Fin 2 → ℝ) with hf_def
  have hf_cont : Continuous f := by
    apply (PiLp.continuous_toLp 2 _).comp
    refine continuous_pi fun k => ?_
    fin_cases k <;> fun_prop
  have hf_meas : Measurable f := hf_cont.measurable
  have hσ : ∀ i : Fin n, SigmaFinite ((Measure.pi fun _ : Fin n => gaussianReal 0 1).map
      f) := fun i => by
    rw [hf_def, stdGaussian_inner_pair]; infer_instance
  rw [h_init_eq, Measure.pi_map_pi (μ := fun _ : Fin n => (Measure.pi fun _ : Fin n => gaussianReal
      0 1))
    (f := fun _ : Fin n => f) (fun _ => hf_meas.aemeasurable)]
  congr 1
  funext i
  exact stdGaussian_inner_pair n u v

/-- **Proposition 2.9' (Inner Products with a Standard Gaussian Vector, `Fin m`-Family)**:
The `Fin m`-indexed generalization of Proposition 2.9 (`stdGaussian_inner_pair`) from a fixed pair
of vectors to a fixed family `u : Fin m → Fin n → ℝ`. For `g ~ 𝒩(0, I_n)` and fixed deterministic
vectors `u α`, the joint law of the projections `α ↦ ⟪g, u α⟫ = g ⬝ᵥ u α` is the `m`-variate
Gaussian with covariance matrix `(α, β) ↦ u α ⬝ᵥ u β`. -/
theorem stdGaussian_inner_family (n m : ℕ) (u : Fin m → Fin n → ℝ) :
    Measure.map (fun a : Fin n → ℝ => WithLp.toLp 2 (fun α : Fin m => a ⬝ᵥ u α))
        (Measure.pi fun _ : Fin n => gaussianReal 0 1) =
      multivariateGaussian (0 : EuclideanSpace ℝ (Fin m))
        (Matrix.of fun α β : Fin m => u α ⬝ᵥ u β) := by
  set A : Matrix (Fin m) (Fin n) ℝ := Matrix.of u with hA_def
  have hA_mulVec : ∀ a : Fin n → ℝ, A *ᵥ a = fun α => a ⬝ᵥ u α := by
    intro a
    ext α
    simp [A, mulVec, dotProduct, mul_comm]
  have hF_eq : (fun a : Fin n → ℝ => WithLp.toLp 2 (fun α : Fin m => a ⬝ᵥ u α)) =
      (fun x : EuclideanSpace ℝ (Fin n) => WithLp.toLp 2 (A *ᵥ x.ofLp)) ∘ (WithLp.toLp 2) := by
    ext a
    simp [hA_mulVec]
  have hSpos : (1 : Matrix (Fin n) (Fin n) ℝ).PosSemidef := Matrix.PosSemidef.one
  have h_map := gaussian_map_mulVec (0 : EuclideanSpace ℝ (Fin n)) 1 hSpos A
  rw [hF_eq, ← Measure.map_map (by fun_prop) (by fun_prop)]
  have h_toLp : Measure.map (WithLp.toLp 2) (Measure.pi fun _ : Fin n => gaussianReal 0 1) =
      multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) 1 := by
    rw [map_pi_eq_stdGaussian, multivariateGaussian_zero_one]
  rw [h_toLp, h_map]
  have h_mean0 : A *ᵥ (0 : EuclideanSpace ℝ (Fin n)).ofLp = (0 : Fin m → ℝ) := by simp
  have h_cov : A * (1 : Matrix (Fin n) (Fin n) ℝ) * Aᵀ =
      (Matrix.of fun α β => u α ⬝ᵥ u β) := by
    rw [Matrix.mul_one]
    ext α β
    simp [A, Matrix.mul_apply, Matrix.transpose_apply, dotProduct]
  rw [h_mean0, h_cov]
  simp

/-- **Proposition 2.10' (Matrix-Vector Multiplication by a Gaussian Matrix, `Fin m`-Family)**:
The `Fin m`-indexed generalization of Proposition 2.10 (`gaussianMatrix_mulVec_pair`) from a fixed
pair of vectors to a fixed family `u : Fin m → Fin n → ℝ`. For `W : Fin r → Fin n → ℝ` with i.i.d.
standard Gaussian rows (`gaussianInit r n`), the row-indexed family
`i ↦ (α ↦ W i ⬝ᵥ u α) : Fin r → EuclideanSpace ℝ (Fin m)` consists of `r` i.i.d. copies of
Proposition 2.9''s `m`-variate Gaussian with covariance `(α, β) ↦ u α ⬝ᵥ u β`. -/
theorem gaussianMatrix_mulVec_family (n r m : ℕ) (u : Fin m → Fin n → ℝ) :
    Measure.map
      (fun W : Fin r → Fin n → ℝ =>
        fun i : Fin r => WithLp.toLp 2 (fun α : Fin m => W i ⬝ᵥ u α))
      (Measure.pi fun _ : Fin r => Measure.pi fun _ : Fin n => gaussianReal 0 1) =
      Measure.pi (fun _ : Fin r =>
        multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) (Matrix.of fun α β : Fin m => u α ⬝ᵥ u β)) := by
  have h_init_eq : (Measure.pi fun _ : Fin r => Measure.pi fun _ : Fin n =>
      gaussianReal 0 1) = Measure.pi (fun _ : Fin r => (Measure.pi fun _ : Fin n =>
      gaussianReal 0 1)) := rfl
  set f := fun a : Fin n → ℝ => WithLp.toLp 2 (fun α : Fin m => a ⬝ᵥ u α) with hf_def
  have hf_cont : Continuous f :=
    (PiLp.continuous_toLp 2 _).comp (continuous_pi fun α => by fun_prop)
  have hf_meas : Measurable f := hf_cont.measurable
  have hσ : ∀ i : Fin r, SigmaFinite ((Measure.pi fun _ : Fin n => gaussianReal 0 1).map
      f) := fun i => by
    rw [hf_def, stdGaussian_inner_family]; infer_instance
  rw [h_init_eq, Measure.pi_map_pi (μ := fun _ : Fin r => (Measure.pi fun _ : Fin n => gaussianReal
      0 1))
    (f := fun _ : Fin r => f) (fun _ => hf_meas.aemeasurable)]
  congr 1
  funext i
  exact stdGaussian_inner_family n m u

end GaussianVectorAlgebra

end NTK

end
