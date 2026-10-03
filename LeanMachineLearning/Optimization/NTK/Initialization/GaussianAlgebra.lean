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

* Proposition 2.8: a linear image `A g` of a Gaussian vector `g ~ 𝒩(μ, S)` is again Gaussian,
  `A g ~ 𝒩(A μ, A S Aᵀ)` (`NTK.gaussian_map_mulVec`).
* Propositions 2.9' and 2.10': for `g ~ 𝒩(0, I_n)` and a fixed family `u : Fin m → Fin n → ℝ`, the
  joint law of `α ↦ ⟪g, u α⟫` is the `m`-variate Gaussian with covariance `(α, β) ↦ u α ⬝ᵥ u β`
  (`NTK.stdGaussian_inner_family`); for a matrix `W` with i.i.d. standard Gaussian rows, the
  row-indexed family `i ↦ (α ↦ W i ⬝ᵥ u α)` consists of i.i.d. copies of it
  (`NTK.gaussianMatrix_mulVec_family`, proved by `NTK.map_pi_rows_eq_pi`, a row-wise application
  of `Measure.pi_map_pi`). Used by the layer-by-layer conditional Gaussian structure.
* Propositions 2.9 and 2.10: the `m = 2`, `u := ![u, v]` special cases
  (`NTK.stdGaussian_inner_pair`, `NTK.gaussianMatrix_mulVec_pair`).

See
`LeanMachineLearning.Optimization.NTK.Initialization`
for the overview of the whole development.
-/

@[expose] public section

open Real MeasureTheory ProbabilityTheory Matrix Complex
open scoped BigOperators MatrixOrder RealInnerProductSpace Kronecker ENNReal

namespace NTK

variable {d n m : ℕ}

section GaussianVectorAlgebra

/-! ## Gaussian Vector Algebra (Propositions 2.8-2.10) -/

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
    rw [real_inner_comm, real_inner_eq_dotProduct]
    rw [dotProduct_mulVec, ← mulVec_transpose, dotProduct_comm]
  simp_rw [h_inner]
  have h_as_charFun : (∫ x : EuclideanSpace ℝ ι,
      Complex.exp ((x.ofLp ⬝ᵥ (Aᵀ *ᵥ t.ofLp) : ℝ) * Complex.I) ∂(multivariateGaussian μ S)) =
      charFun (multivariateGaussian μ S) (WithLp.toLp 2 (Aᵀ *ᵥ t.ofLp)) := by
    rw [charFun_apply]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [real_inner_eq_dotProduct]
  rw [h_as_charFun, charFun_multivariateGaussian hS, charFun_multivariateGaussian hAST]
  have h_mean : ⟪(WithLp.toLp 2 (Aᵀ *ᵥ t.ofLp) : EuclideanSpace ℝ ι), μ⟫ =
      ⟪t, (WithLp.toLp 2 (A *ᵥ μ.ofLp) : EuclideanSpace ℝ κ)⟫ := by
    rw [real_inner_eq_dotProduct, real_inner_eq_dotProduct]
    conv_rhs => rw [dotProduct_mulVec, ← mulVec_transpose]
  have h_quad : (Aᵀ *ᵥ t.ofLp) ⬝ᵥ S *ᵥ (Aᵀ *ᵥ t.ofLp) = t.ofLp ⬝ᵥ (A * S * Aᵀ) *ᵥ t.ofLp := by
    conv_rhs => rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, ← mulVec_transpose]
  rw [h_mean, h_quad]

/-- **Propositions 2.9' (Inner Products with a Standard Gaussian Vector, `Fin m`-Family)**:
For `g ~ 𝒩(0, I_n)` and a fixed family of deterministic vectors `u : Fin m → Fin n → ℝ`, the joint
law of the projections `α ↦ ⟪g, u α⟫ = g ⬝ᵥ u α` is the `m`-variate Gaussian with covariance
matrix `(α, β) ↦ u α ⬝ᵥ u β`. -/
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
  have h_map := gaussian_map_mulVec (0 : EuclideanSpace ℝ (Fin n)) 1 Matrix.PosSemidef.one A
  rw [hF_eq, ← Measure.map_map (by fun_prop) (by fun_prop), map_pi_eq_stdGaussian,
    ← multivariateGaussian_zero_one, h_map]
  have h_cov : A * (1 : Matrix (Fin n) (Fin n) ℝ) * Aᵀ =
      (Matrix.of fun α β => u α ⬝ᵥ u β) := by
    rw [Matrix.mul_one]
    ext α β
    simp [A, Matrix.mul_apply, Matrix.transpose_apply, dotProduct]
  rw [h_cov]
  simp

/-- **Row-wise pushforward of a product measure.** If `f` pushes `ν` forward to `κ`, then applying
`f` to every coordinate pushes `ν^{⊗ι}` forward to `κ^{⊗ι}` (a form of `Measure.pi_map_pi` with a
constant family). -/
lemma map_pi_rows_eq_pi {ι α β : Type*} [Fintype ι] [MeasurableSpace α] [MeasurableSpace β]
    {ν : Measure α} {κ : Measure β} [SigmaFinite ν] [SigmaFinite κ] {f : α → β}
    (hf : AEMeasurable f ν) (h : ν.map f = κ) :
    (Measure.pi fun _ : ι => ν).map (fun W i => f (W i)) = Measure.pi fun _ : ι => κ := by
  have : SigmaFinite (ν.map f) := h ▸ ‹SigmaFinite κ›
  rw [Measure.pi_map_pi (μ := fun _ : ι => ν) (f := fun _ => f) fun _ => hf, h]

/-- **Proposition 2.10' (Matrix-Vector Multiplication by a Gaussian Matrix, `Fin m`-Family)**:
For `W : Fin r → Fin n → ℝ` with i.i.d. standard Gaussian rows (`𝒩(0,1)^{r×n}`) and a fixed family
`u : Fin m → Fin n → ℝ`, the row-indexed family
`i ↦ (α ↦ W i ⬝ᵥ u α) : Fin r → EuclideanSpace ℝ (Fin m)` consists of `r` i.i.d. copies of the
`m`-variate Gaussian of Proposition 2.9' with covariance `(α, β) ↦ u α ⬝ᵥ u β`. -/
theorem gaussianMatrix_mulVec_family (n r m : ℕ) (u : Fin m → Fin n → ℝ) :
    Measure.map
      (fun W : Fin r → Fin n → ℝ =>
        fun i : Fin r => WithLp.toLp 2 (fun α : Fin m => W i ⬝ᵥ u α))
      (Measure.pi fun _ : Fin r => Measure.pi fun _ : Fin n => gaussianReal 0 1) =
      Measure.pi (fun _ : Fin r => multivariateGaussian (0 : EuclideanSpace ℝ (Fin m))
        (Matrix.of fun α β : Fin m => u α ⬝ᵥ u β)) :=
  map_pi_rows_eq_pi
    ((PiLp.continuous_toLp 2 _).comp (continuous_pi fun α => by fun_prop)).aemeasurable
    (stdGaussian_inner_family n m u)

/-- The Gram matrix of the two vectors `![u, v]` as an explicit `2 × 2` matrix. -/
private lemma gram_pair_eq {n : ℕ} (u v : Fin n → ℝ) :
    (Matrix.of fun α β : Fin 2 => (![u, v] α) ⬝ᵥ (![u, v] β)) =
      !![u ⬝ᵥ u, u ⬝ᵥ v; u ⬝ᵥ v, v ⬝ᵥ v] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dotProduct_comm]

private lemma pair_vec_eq {n : ℕ} (u v : Fin n → ℝ) (a : Fin n → ℝ) :
    (fun α : Fin 2 => a ⬝ᵥ ![u, v] α) = ![a ⬝ᵥ u, a ⬝ᵥ v] := by
  funext α
  fin_cases α <;> rfl

/-- **Proposition 2.9 (Inner Products with a Standard Gaussian Vector)**:
For `g ~ 𝒩(0, I_n)` and fixed deterministic vectors `u v : Fin n → ℝ`, the joint law of the pair
of projections `(⟪g,u⟫, ⟪g,v⟫) = (g ⬝ᵥ u, g ⬝ᵥ v)` is the bivariate Gaussian with covariance matrix
`!![u ⬝ᵥ u, u ⬝ᵥ v; u ⬝ᵥ v, v ⬝ᵥ v]`. This is `stdGaussian_inner_family` with `m = 2`. -/
theorem stdGaussian_inner_pair (n : ℕ) (u v : Fin n → ℝ) :
    Measure.map (fun a : Fin n → ℝ => WithLp.toLp 2 (![a ⬝ᵥ u, a ⬝ᵥ v] : Fin 2 → ℝ))
        (Measure.pi fun _ : Fin n => gaussianReal 0 1) =
      multivariateGaussian 0 !![u ⬝ᵥ u, u ⬝ᵥ v; u ⬝ᵥ v, v ⬝ᵥ v] := by
  simpa only [pair_vec_eq, gram_pair_eq] using stdGaussian_inner_family n 2 ![u, v]

/-- **Proposition 2.10 (Matrix-Vector Multiplication by a Gaussian Matrix)**:
For `W : Fin n → Fin n → ℝ` with i.i.d. standard Gaussian entries (`𝒩(0,1)^{n×n}`) and fixed
deterministic vectors `u v : Fin n → ℝ`, the row-indexed pairs
`i ↦ (W i ⬝ᵥ u, W i ⬝ᵥ v) = i ↦ ((W *ᵥ u) i, (W *ᵥ v) i)` are `n` i.i.d. copies of the bivariate
Gaussian from Proposition 2.9, i.e. the block/Kronecker-structured covariance
`!![u ⬝ᵥ u, u ⬝ᵥ v; u ⬝ᵥ v, v ⬝ᵥ v] ⊗ Iₙ`. This is `gaussianMatrix_mulVec_family` with `m = 2`. -/
theorem gaussianMatrix_mulVec_pair (n : ℕ) (u v : Fin n → ℝ) :
    Measure.map
      (fun W : Fin n → Fin n → ℝ =>
        fun i : Fin n => WithLp.toLp 2 (![W i ⬝ᵥ u, W i ⬝ᵥ v] : Fin 2 → ℝ))
      (Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin n => gaussianReal 0 1) =
      Measure.pi (fun _ : Fin n => multivariateGaussian 0 !![u ⬝ᵥ u, u ⬝ᵥ v; u ⬝ᵥ v, v ⬝ᵥ v]) := by
  simpa only [pair_vec_eq, gram_pair_eq] using gaussianMatrix_mulVec_family n n 2 ![u, v]

end GaussianVectorAlgebra

end NTK

end
